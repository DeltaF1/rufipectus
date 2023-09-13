use std::cell::RefCell;
use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::iter::Peekable;
use std::rc::Rc;

use crate::ast::Primitive;
use crate::common::StringAddress;
use crate::Arity;
use crate::AstSig;
use crate::ClassBuilder;
use crate::ClassDef;
use crate::MethodAst;
use crate::Scope;
use crate::Signature;
use crate::{Expression, Statement};

// TODO: imports should execute the top_level_ast of the imported module at run-time, but also
// include classdefs at compile-time
#[derive(Debug)]
pub struct Module<'text> {
    pub(crate) top_level_ast: Statement<'text>,
    pub(crate) classes: HashMap<&'text str, Rc<ClassDef<'text>>>,
    pub(crate) globals: Scope<'text>,
    pub(crate) strings: Vec<&'text str>,
}

struct StringStream<'text> {
    iter: Peekable<std::iter::Enumerate<std::str::Chars<'text>>>,
    source: &'text str,
}

impl<'text> StringStream<'text> {
    fn from_str(s: &'text str) -> Self {
        StringStream {
            iter: s.chars().enumerate().peekable(),
            source: s,
        }
    }
    fn peek(&mut self) -> Option<&char> {
        self.iter.peek().map(|(_, c)| c)
    }

    fn next(&mut self) -> Option<char> {
        self.iter.next().map(|(_, c)| c)
    }

    fn index(&mut self) -> usize {
        self.index_maybe().unwrap()
    }

    fn index_maybe(&mut self) -> Option<usize> {
        self.iter.peek().map(|(i, _)| *i)
    }

    fn get(&self, start: usize, end: usize) -> &'text str {
        &self.source[start..end]
    }

    fn rollback(&mut self, n: usize) {
        let current: usize = self
            .iter
            .peek()
            .map(|(i, _)| *i)
            .unwrap_or(self.source.len() - 3);
        let new = current - n;
        let mut new_iter = self.source.chars().enumerate().peekable();
        {
            (&mut new_iter).nth(new - 1);
        }
        self.iter = new_iter;
    }

    fn newline_before_next_token(&mut self) -> bool {
        let start = self.index();
        let iter = self.source[start..].chars();
        for c in iter {
            if c == '\n' {
                return true;
            } else if c.is_whitespace() {
                continue;
            } else {
                return false;
            }
        }
        panic!("EOF")
    }
}

#[derive(Debug, Default)]
pub struct CompilerState<'text> {
    current_class: Option<ClassBuilder<'text>>,
    current_method: Option<MethodContext<'text>>,
    classes: HashMap<&'text str, Rc<ClassDef<'text>>>,
    globals: Scope<'text>,
    strings: Vec<&'text str>,
}

#[derive(Default, Debug)]
struct MethodContext<'text> {
    locals: Scope<'text>,
    args: Scope<'text>,
}

enum NameType {
    Local,
    Arg,
    ThisCall,
    Global,
}

impl<'text> MethodContext<'text> {
    fn x(&self, name: &'text str) -> NameType {
        if self.locals.contains(name) {
            NameType::Local
        } else if self.args.contains(name) {
            NameType::Arg
        } else if name.chars().nth(0).unwrap().is_uppercase() {
            NameType::Global
        } else {
            NameType::ThisCall
        }
    }
}

pub fn parse_file<'text>(s: &'text str) -> Module<'text> {
    let mut iter = StringStream::from_str(s);

    let mut state = CompilerState::default();

    let mut top_level_ast = vec![];
    let mut locals = Scope::default();
    while peek_next_token(&mut iter).is_some() {
        top_level_ast.push(state.parse_statement(&mut iter, &mut locals));
    }

    Module {
        classes: state.classes,
        strings: state.strings,
        globals: state.globals,
        top_level_ast: Statement::Block(top_level_ast),
    }
}

fn is_word(c: &char) -> bool {
    c.is_alphanumeric() | (c == &'_')
}

fn is_binary_op(name: &str) -> bool {
    match name {
        "*" => true,
        _ => false,
    }
}

fn next_token<'a>(i: &mut StringStream<'a>) -> Option<&'a str> {
    while i.peek()?.is_whitespace() {
        i.next();
    }

    let start: usize = i.index_maybe()?;
    if let Some(next) = i.peek() {
        if !is_word(next) {
            i.next();
        } else {
            while i.peek().is_some_and(is_word) {
                i.next();
            }
        }
    }
    let end = i.index_maybe().unwrap_or(i.source.len());
    let s = i.get(start, end);
    println!("next_token = {s:?}");
    Some(s)
}

fn peek_next_token<'text>(i: &mut StringStream<'text>) -> Option<&'text str> {
    let mut start = i.index();
    let mut iter = (&i.source[start..]).chars().peekable();
    while iter.peek()?.is_whitespace() {
        iter.next()?;
        start += 1;
    }

    let mut end = start;
    if !is_word(iter.peek().unwrap()) {
        iter.next();
        end += 1;
    } else {
        while is_word(iter.peek().unwrap()) {
            iter.next();
            end += 1;
        }
    }

    // Was unable to parse any token out of this
    if start == end {
        return None;
    }

    let s = i.get(start, end);
    println!("peek_token = {s:?}");
    Some(s)
}

fn peek_nth_token<'text>(i: &mut StringStream<'text>, n: usize) -> Option<&'text str> {
    let current = i.index_maybe()?;
    let mut new_stream = StringStream::from_str(i.source);
    {
        if current != 0 {
            new_stream.iter.nth(current - 1);
        }
    }

    for _ in 0..n {
        next_token(&mut new_stream);
    }
    next_token(&mut new_stream)
}

/*
macro_rules! token_match_arm {
    (peek $pat:expr => $body:tt) => {
        $pat => {
            $body
        }
    };

    ($pat:expr => $body:tt) => {
        $pat => {
            $body
        }
    }
}

macro_rules! token_match {
    ($iter:ident $()*, )
}
*/

enum Consumed<'text> {
    Other(&'text str),
    Expected,
}

/// Consumes the next token if it equals `expected`, else the StringStream is not advanced
fn next_token_is<'text>(i: &mut StringStream<'text>, expected: &str) -> Option<bool> {
    Some(match consume_next_token_if(i, expected)? {
        Consumed::Other(_) => false,
        Consumed::Expected => true,
    })
}

/*
fn consume_next_token_if<'text, F>(
    i: &mut StringStream<'text>,
    predicate: F,
) -> Option<Consumed<'text>>
where
    F: FnOnce(&'text str) -> bool,
    */

fn consume_next_token_if<'text>(
    i: &mut StringStream<'text>,
    expected: &str,
) -> Option<Consumed<'text>> {
    let next = peek_next_token(i)?;

    if expected == next {
        next_token(i);
        Some(Consumed::Expected)
    } else {
        Some(Consumed::Other(next))
    }
}

impl<'text> CompilerState<'text> {
    fn parse_expr(&mut self, i: &mut StringStream<'text>) -> Expression<'text> {
        let tok = next_token(i).unwrap();

        // TODO: Parse floats
        let place = if tok.chars().nth(0).unwrap().is_numeric() {
            Expression::Primitive(Primitive::Number(tok.parse::<u32>().unwrap().into()))
        } else {
            match tok {
                "\"" => Expression::Primitive(Primitive::String(self.parse_string(i))),
                "[" => todo!("List literals"),
                "{" => todo!("Dictionary literals"),
                "this" => Expression::This,
                _ => {
                    // TODO current_method.x()
                    if tok.starts_with('_') {
                        let class = self.current_class.as_mut().unwrap();
                        Expression::ReadField(class.read_field(tok))
                    } else if let Some(n) = self
                        .current_method
                        .as_ref()
                        .and_then(|m| m.args.get_index(tok))
                    {
                        Expression::ArgLookup(n)
                        // TODO: Lookup locals
                    } else if let Some(n) = self.globals.get_index(tok) {
                        Expression::GlobalLookup(n)
                    } else if tok.chars().nth(0).unwrap().is_uppercase() {
                        Expression::GlobalLookup(
                            self.globals
                                .get_index(tok)
                                .expect(&format!("No global named {tok:?}")),
                        )
                    } else {
                        Expression::ThisCall(self.parse_func_call(i, tok))
                    }
                }
            }
        };

        /* TODO: Is this correct? not sure how newlines work
        if i.newline_before_next_token() {
            return place;
        }
        */

        if peek_next_token(i).is_some_and(is_binary_op) {
            let op = next_token(i).unwrap();
            return Expression::Call(Box::new(place), self.parse_func_call(i, op));
        }
        match peek_next_token(i) {
            Some(".") => {
                // Drop "."
                next_token(i);
                let method_name = next_token(i).unwrap();
                match method_name {
                    "{" | "}" => panic!("Bad char in method name"),
                    _ => {}
                };
                Expression::Call(Box::new(place), self.parse_func_call(i, method_name))
            }
            Some(_) => place,
            None => place,
        }
        /*

        determine what the name means.
        generate proper lookup type.
        peek ahead
        if "[" "=" or "." then the name lookup is part of a larger call expr.
            generate the call expr
        peek ahead
        if "?" then expr is part of ternary
            parse_expr()
            look for ":". if missing, error with broken ternary
            parse_expr()
            generate ternary with the three
            */
    }

    fn parse_statement(
        &mut self,
        i: &mut StringStream<'text>,
        locals: &mut Scope<'text>,
    ) -> Statement<'text> {
        match next_token(i).expect("EOF when parsing statement") {
            "class" => {
                let name = next_token(i).expect("EOF when parsing class name");
                let mut class_builder;
                if next_token_is(i, "is").expect("EOF when parsing class declaration") {
                    let super_name = next_token(i).expect("EOF parsing superclass name");
                    // TODO: Defer building class if it's inside another class
                    if self
                        .current_class
                        .as_ref()
                        .is_some_and(|c| c.class.name == super_name)
                    {
                        panic!("Can't define subclass inside of class definition. This is a limitation of the compiler")
                    }
                    let super_class = &self.classes[super_name];
                    class_builder = ClassDef::child_of(super_class, name);
                } else {
                    class_builder = ClassBuilder::new(name);
                }

                locals.declare(name);
                //FIXME
                self.globals.declare(name);

                let old_class = self.current_class.replace(class_builder);
                let def = Rc::new(self.parse_class_body(i));
                self.current_class = old_class;
                self.classes.insert(name, def);
                Statement::AssignGlobal(
                    locals.get_index(name).unwrap(),
                    // Generate AST for creating a class object from a ClassDef
                    Box::new(Expression::Primitive(Primitive::Null)),
                )
            }
            "if" => todo!(), //parse_if(i, ctx),
            "return" => Statement::Return(self.parse_expr(i)),
            "{" => self.parse_block(i, locals),
            "var" => {
                let name = peek_next_token(i).unwrap();
                self.globals.declare(name);

                // Look ahead past the name to see if we're in an assignment
                if peek_nth_token(i, 1) != Some("=") {
                    // Drop the name
                    next_token(i);
                }
                self.parse_statement(i, locals)
            }
            x => {
                let assignment = next_token_is(i, "=").unwrap();
                if let Some(class) = self.current_class.as_mut() {
                    if x.starts_with("__") {
                        if assignment {
                            return Statement::WriteStaticField(
                                class.write_static_field(x),
                                Box::new(self.parse_expr(i)),
                            );
                        }
                    } else if x.starts_with("_") {
                        if assignment {
                            return Statement::WriteField(
                                class.write_field(x),
                                Box::new(self.parse_expr(i)),
                            );
                        }
                    }
                }
                match self.current_method.as_ref().map(|method| method.x(x)) {
                    Some(NameType::Local) => {
                        if assignment {
                            Statement::AssignLocal(
                                locals.get_index(x).unwrap(),
                                Box::new(self.parse_expr(i)),
                            )
                        } else {
                            unimplemented!("discarded local")
                        }
                    }
                    Some(NameType::Global) => {
                        if assignment {
                            Statement::AssignGlobal(
                                self.globals.get_index(x).unwrap(),
                                Box::new(self.parse_expr(i)),
                            )
                        } else {
                            unimplemented!("discarded global")
                        }
                    }
                    Some(NameType::ThisCall) => {
                        let sig: AstSig = self.parse_func_call(i, x);
                        Statement::ExprStatement(Expression::ThisCall(sig))
                    }
                    Some(NameType::Arg) => unimplemented!("Using arg in statement mode"),
                    None => {
                        // We're in highest scope
                        // if locals.contains(x)
                        if assignment {
                            Statement::AssignGlobal(
                                self.globals.get_index(x).expect("No global named {x:?}"),
                                Box::new(self.parse_expr(i)),
                            )
                        } else {
                            i.rollback(x.len());
                            Statement::ExprStatement(self.parse_expr(i))
                        }
                    }
                }
            }
        }
    }

    fn parse_block(
        &mut self,
        i: &mut StringStream<'text>,
        locals: &mut Scope<'text>,
    ) -> Statement<'text> {
        // Check for newlines before the next token
        if i.newline_before_next_token() {
            let mut v = vec![];
            while peek_next_token(i).unwrap() != "}" {
                v.push(self.parse_statement(i, locals));
            }
            assert_eq!(next_token(i), Some("}"));
            Statement::Block(v)
        } else {
            let e = self.parse_expr(i);
            assert_eq!(next_token(i), Some("}"));
            Statement::Return(e)
        }
    }

    fn parse_func_call(&mut self, i: &mut StringStream<'text>, name: &'text str) -> AstSig<'text> {
        let intermediate;
        if is_binary_op(name) {
            return AstSig::Func(name.into(), vec![self.parse_expr(i)]);
        } else {
            if let Some(Consumed::Expected) = consume_next_token_if(i, "(") {
                let mut args = vec![];
                loop {
                    match peek_next_token(i).unwrap() {
                        "," => panic!("Too many commas"),
                        ")" => break,
                        _ => (),
                    }

                    args.push(self.parse_expr(i));
                    match peek_next_token(i).unwrap() {
                        "," => {
                            next_token(i);
                            continue;
                        }
                        ")" => break,
                        _ => panic!(),
                    }
                }
                assert_eq!(next_token(i), Some(")"));
                return AstSig::Func(name.into(), args);
            } else if let Some(Consumed::Expected) = consume_next_token_if(i, "{") {
                todo!("Function body arguments")
            } else {
                intermediate = AstSig::Getter(name.into())
            }
        }

        if peek_next_token(i) == Some("=") {
            next_token(i);
            match intermediate {
                AstSig::Getter(name) => return AstSig::Setter(name, Box::new(self.parse_expr(i))),
                _ => todo!("Subscriptgetter"),
            }
        }

        return intermediate;
    }

    fn parse_sig(&mut self, i: &mut StringStream<'text>) -> Signature<'text> {
        let name = next_token(i).unwrap();

        let mut arity;

        if name == "[" {
            arity = Arity::SubscriptGetter(self.parse_args_list(i));
            assert_eq!(next_token(i), Some("]"))
        } else if next_token_is(i, "(").unwrap() {
            arity = Arity::Func(self.parse_args_list(i));
            assert_eq!(next_token(i), Some(")"));
        } else {
            arity = Arity::Getter
        }

        if next_token_is(i, "=").unwrap() {
            next_token(i);
            let setter_arg = next_token(i).unwrap();
            //self.current_method.args.declare(setter_arg)
            arity = match arity {
                Arity::Getter => Arity::Setter,
                Arity::SubscriptGetter(n) => Arity::SubscriptSetter(n),
                x => panic!(),
            }
        }

        Signature::new(name.into(), arity)
    }

    fn parse_args_list(&mut self, i: &mut StringStream<'text>) -> usize {
        let args = &mut self.current_method.as_mut().unwrap().args;

        loop {
            match peek_next_token(i).unwrap() {
                "," => panic!("Too many commas"),
                "]" => break,
                ")" => break,
                x => {}
            }
            let name = next_token(i).expect("EOF when parsing parameter list");
            args.declare(name);
            match peek_next_token(i).unwrap() {
                "," => {
                    next_token(i);
                    continue;
                }
                "]" => break,
                ")" => break,
                x => panic!("Malformed list"),
            }
        }

        args.len()
    }

    fn parse_class_body(&mut self, i: &mut StringStream<'text>) -> ClassDef<'text> {
        assert_eq!(next_token(i), Some("{"));
        let ref_self = RefCell::new(self);
        while peek_next_token(i).expect("EOF when parsing class body") != "}" {
            let mut binding = ref_self.borrow_mut();
            let specifier = peek_next_token(i).unwrap();
            enum MethodType {
                Constructor,
                Static,
                Foreign,
                Normal,
            }
            let method_type;
            match specifier {
                "construct" => {
                    method_type = MethodType::Constructor;
                    next_token(i);
                }
                "static" => {
                    method_type = MethodType::Static;
                    next_token(i);
                }
                "foreign" => todo!(),
                _ => method_type = MethodType::Normal,
            }
            let old_method = binding.current_method.replace(MethodContext::default());
            let sig = binding.parse_sig(i);
            let body = binding.parse_method_body(i);

            let class = binding
                .current_class
                .as_mut()
                .expect("Class body outside of class");

            match method_type {
                MethodType::Normal => class.add_method(sig, body),
                MethodType::Constructor => class.add_constructor(sig, body),
                _ => todo!(),
            };
            binding.current_method = old_method;
            drop(binding);
        }
        assert_eq!(next_token(i), Some("}"));

        ref_self.into_inner().current_class.take().unwrap().finish()
    }

    fn parse_method_body(&mut self, i: &mut StringStream<'text>) -> MethodAst<'text> {
        let mut locals = Scope::new();
        MethodAst {
            ast: self.parse_statement(i, &mut locals),
        }
    }

    fn parse_string(&mut self, i: &mut StringStream<'text>) -> StringAddress {
        let start = i.index();
        loop {
            let c = i.next();
            if c.is_none() {
                break;
            }
            let c = c.unwrap();
            if c == '"' {
                break;
            } else if c == '\\' {
                let escaped = i.next();
                // TODO: Process escapes like \n etc.
            }
        }
        let end = i.index() - 1;

        let str = &i.source[start..end];
        println!("Parsed string: {str:?}");
        if let Some(index) = self.strings.iter().position(|s| s == &str) {
            index
        } else {
            self.strings.push(str);
            self.strings.len() - 1
        }
        .try_into()
        .expect("Overflowed string cache")
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn peeking() {
        let mut f = File::open("test.wren").unwrap();
        let s = {
            let mut s = String::new();
            f.read_to_string(&mut s);
            s
        };
        // FIXME
        let s = s.leak();

        let mut iter = StringStream {
            iter: s.chars().enumerate().peekable(),
            source: s,
        };

        while peek_next_token(&mut iter).is_some() {
            assert_eq!(peek_next_token(&mut iter), next_token(&mut iter));
        }
    }

    #[test]
    fn rollback() {
        let string = "    token1 longtoken2 token3()   ";
        let mut stream = StringStream::from_str(&string);

        {
            let stream = &mut stream;
            assert_eq!(peek_next_token(stream), Some("token1"));
            assert_eq!(next_token(stream), Some("token1"));
            stream.rollback("token1".len());
            assert_eq!(peek_next_token(stream), Some("token1"));
            assert_eq!(next_token(stream), Some("token1"));
            assert_eq!(next_token(stream), Some("longtoken2"));
            stream.rollback(17);
            assert_eq!(next_token(stream), Some("token1"));
            assert_eq!(next_token(stream), Some("longtoken2"));
            assert_eq!(next_token(stream), Some("token3"));
            assert_eq!(next_token(stream), Some("("));
            assert_eq!(next_token(stream), Some(")"));
            stream.rollback(1);
            assert_eq!(next_token(stream), Some(")"));
            assert_eq!(next_token(stream), None);
            stream.rollback(1);
            assert_eq!(next_token(stream), Some(")"));
        }
    }

    #[test]
    fn peek_nth_tokens() {
        let string = "token1 2 3[4";
        let mut stream = StringStream::from_str(&string);

        {
            let stream = &mut stream;
            assert_eq!(peek_nth_token(stream, 100), None);
            assert_eq!(peek_nth_token(stream, 0), Some("token1"));
            assert_eq!(peek_nth_token(stream, 1), Some("2"));
            assert_eq!(peek_nth_token(stream, 2), Some("3"));
            assert_eq!(peek_nth_token(stream, 3), Some("["));
            assert_eq!(peek_nth_token(stream, 4), Some("4"));
            assert_eq!(peek_nth_token(stream, 5), None);

            assert_eq!(peek_nth_token(stream, 0), Some("token1"));
            assert_eq!(next_token(stream), Some("token1"));
            assert_eq!(peek_next_token(stream), Some("2"));
            assert_eq!(peek_nth_token(stream, 0), Some("2"));
            assert_eq!(next_token(stream), Some("2"));

            assert_eq!(peek_nth_token(stream, 0), Some("3"));
            assert_eq!(peek_nth_token(stream, 1), Some("["));
            assert_eq!(peek_nth_token(stream, 2), Some("4"));

            assert_eq!(next_token(stream), Some("3"));
            assert_eq!(next_token(stream), Some("["));
            assert_eq!(next_token(stream), Some("4"));

            assert_eq!(peek_nth_token(stream, 100), None);
        }
    }
}
