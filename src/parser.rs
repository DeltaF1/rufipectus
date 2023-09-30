use std::cell::RefCell;
use std::collections::HashMap;

use std::borrow::Cow;
use std::io::Read;
use std::iter::Peekable;
use std::rc::Rc;

use crate::ast::Primitive;
use crate::common::StringAddress;
use crate::Arity;
use crate::AstSig;
use crate::ClassBuilder;
use crate::ClassDef;
use crate::ClassRef;
use crate::MethodAst;
use crate::Scope;
use crate::Signature;
use crate::{Expression, Statement};

// TODO: imports should execute the top_level_ast of the imported module at run-time, but also
// include classdefs at compile-time
#[derive(Debug)]
pub struct Module<'text> {
    pub(crate) top_level_ast: Statement<'text>,
    pub(crate) global_classes: HashMap<&'text str, Rc<ClassDef<'text>>>,
    pub(crate) classes: Vec<Rc<ClassDef<'text>>>,
    pub(crate) globals: Scope<'text>,
    pub(crate) strings: Vec<Cow<'text, str>>,
}

impl<'text> Module<'text> {
    pub fn from_parser(parser: Parser<'text>, top_level_ast: Statement<'text>) -> Self {
        Module {
            global_classes: parser.global_classes,
            classes: parser.classes,
            strings: parser.strings,
            globals: parser.globals,
            top_level_ast,
        }
    }
}

#[derive(Clone)]
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
        if new > 0 {
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
pub struct Parser<'text> {
    current_class: Option<ClassBuilder<'text>>,
    current_method: Option<MethodContext<'text>>,
    global_classes: HashMap<&'text str, Rc<ClassDef<'text>>>,
    classes: Vec<Rc<ClassDef<'text>>>,
    globals: Scope<'text>,
    strings: Vec<Cow<'text, str>>,
}

#[derive(Debug, Default, Clone, Copy)]
enum MethodType {
    Constructor,
    Static,
    Foreign,
    #[default]
    Normal,
}

#[derive(Default, Debug)]
struct MethodContext<'text> {
    locals: Scope<'text>,
    args: Scope<'text>,
    sig: Option<Signature<'text>>,
    typ: MethodType,
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
    let mut state = Parser::default();
    let top_level_ast = state.feed_text(s);

    Module::from_parser(state, Statement::Block(top_level_ast))
}

fn is_word(c: &char) -> bool {
    c.is_alphanumeric() | (c == &'_')
}

fn is_binary_op(name: &str) -> bool {
    matches!(
        name,
        "*" | "/"
            | "%"
            | "+"
            | "-"
            | ".."
            | "..."
            | "<<"
            | ">>"
            | "<"
            | "<="
            | ">"
            | ">="
            | "=="
            | "!="
            | "&&"
            | "||"
            | "&"
            | "^"
            | "|"
            | "is"
    )
}

fn is_unary_op(name: &str) -> bool {
    matches!(name, "-" | "!" | "~")
}

fn next_token<'a>(i: &mut StringStream<'a>) -> Option<&'a str> {
    // TODO: Construct tokens for non-word mutlichars like == and ||
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

    fn consume_next_char_if(i: &mut StringStream, target: char) -> bool {
        if let Some((_, c)) = i.iter.peek() {
            if c == &target {
                i.iter.next();
                return true;
            }
        }
        false
    }
    let _bin_op = match s {
        "=" => consume_next_char_if(i, '='),
        "!" => consume_next_char_if(i, '='),
        "&" => consume_next_char_if(i, '&'),
        "|" => consume_next_char_if(i, '|'),
        "<" => consume_next_char_if(i, '=') || consume_next_char_if(i, '<'),
        ">" => consume_next_char_if(i, '=') || consume_next_char_if(i, '>'),
        "." => consume_next_char_if(i, '.') && consume_next_char_if(i, '.'),
        _ => false,
    };

    let end = i.index_maybe().unwrap_or(i.source.len());
    let s = i.get(start, end);

    if s == "/" {
        let (_, next_char) = i.iter.peek()?;
        return if next_char == &'/' {
            //println!("Skipping line comment");
            // Line comment
            while i.iter.next().map(|(_i, c)| c)? != '\n' {}
            next_token(i)
        } else if next_char == &'*' {
            //println!("Skipping multi-line comment");
            // We're parsing a multi-line comment
            // Drop the "*"
            next_token(i);
            loop {
                let next = next_token(i)?;
                if next == "*" && i.iter.next().map(|(_, c)| c)? == '/' {
                    break;
                }
            }
            next_token(i)
        } else {
            Some(s)
        };
    }

    //println!("next_token = {s:?}");
    Some(s)
}

fn peek_next_token<'text>(i: &mut StringStream<'text>) -> Option<&'text str> {
    let mut i = i.clone();
    next_token(&mut i)
}

fn peek_nth_token<'text>(i: &mut StringStream<'text>, n: usize) -> Option<&'text str> {
    let mut new_stream = i.clone();

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

impl<'text> Parser<'text> {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn feed_text(&mut self, text: &'text str) -> Vec<Statement<'text>> {
        let mut stream = StringStream::from_str(text);

        let mut v = vec![];
        let mut locals = Scope::new();
        while peek_next_token(&mut stream).is_some() {
            v.push(self.parse_statement(&mut stream, &mut locals))
        }

        v
    }

    fn parse_expr(&mut self, i: &mut StringStream<'text>) -> Expression<'text> {
        let tok = next_token(i).unwrap();
        let place = if tok.chars().nth(0).unwrap().is_numeric() {
            let mut num_string = String::from(tok);
            // Only parse a decimal value if the bit after the . is numeric. Otherwise this is a
            // number literal with a method call
            if let Some(".") = peek_next_token(i) {
                if let Some(true) =
                    peek_nth_token(i, 1).map(|s| s.chars().nth(0).unwrap().is_numeric())
                {
                    num_string += next_token(i).unwrap();
                    num_string += next_token(i).unwrap();
                }
            }

            let f: f64 = if num_string.starts_with("0x") {
                let int: i64 = i64::from_str_radix(&num_string[2..], 16).unwrap();
                int as f64
            } else {
                num_string.parse().unwrap()
            };

            Expression::Primitive(Primitive::Number(f.into()))
        } else {
            match tok {
                ";" => {
                    // The only symbol not in use
                    match consume_next_token_if(i, "asm") {
                        Some(Consumed::Expected) => {
                            let mut args = vec![];
                            if let Consumed::Expected = consume_next_token_if(i, "(").unwrap() {
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
                            }

                            assert_eq!(next_token(i), Some("{"));
                            let mut asm = crate::bytecode::Assembler::new();
                            let mut bytes = vec![];
                            loop {
                                let byte = next_token(i).unwrap();
                                // fragile to stray } inside the asm
                                if byte == "}" {
                                    break;
                                }

                                let stripped = byte.strip_prefix("0x").unwrap_or(byte);
                                let byte = u8::from_str_radix(stripped, 16).unwrap();
                                bytes.push(byte);
                            }

                            let mut iter = bytes.into_iter();

                            use crate::bytecode;
                            while let Some(op) = bytecode::Op::deserialize(&mut iter) {
                                asm.emit_op(op);
                            }

                            let section = asm.into_tree();

                            Expression::InlineAsm(args, section)
                        }
                        _ => {
                            panic!("';' is not a valid token unless followed by the string 'asm'")
                        }
                    }
                }
                "\"" => Expression::Primitive(Primitive::String(self.parse_string(i))),
                "[" => todo!("List literals"),
                "{" => todo!("Dictionary literals"),
                "(" => {
                    let e = self.parse_expr(i);
                    assert_eq!(next_token(i), Some(")"));
                    e
                }
                "this" => Expression::This,
                "false" => Expression::Primitive(Primitive::Bool(false)),
                "true" => Expression::Primitive(Primitive::Bool(true)),
                "null" => Expression::Primitive(Primitive::Null),
                "super" => {
                    if let Consumed::Expected = consume_next_token_if(i, ".").unwrap() {
                        // FIXME: [] ops
                        let name = next_token(i).unwrap();
                        Expression::SuperCall(self.parse_func_call(i, name))
                    } else {
                        let mut name = self
                            .current_method
                            .as_ref()
                            .unwrap()
                            .sig
                            .as_ref()
                            .unwrap()
                            .name
                            .clone();
                        if let MethodType::Constructor = self.current_method.as_ref().unwrap().typ {
                            name = name + " init"
                        }
                        Expression::SuperCall(self.parse_func_call(i, name))
                    }
                }
                _ => {
                    if is_unary_op(tok) {
                        return Expression::Call(
                            Box::new(self.parse_expr(i)),
                            AstSig::Getter(tok.into()),
                        );
                    }
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
                    } else if self.current_method.is_none() && self.globals.get_index(tok).is_some() {
                        Expression::GlobalLookup(self.globals.get_index(tok).unwrap())
                    } else if tok.chars().nth(0).unwrap().is_uppercase() {
                        Expression::GlobalLookup(
                            self.globals
                                .get_index(tok)
                                .expect(&format!("No global named {tok:?}")),
                        )
                    } else {
                        assert_ne!(tok, "super");
                        Expression::Call(Box::new(Expression::This), self.parse_func_call(i, tok))
                    }
                }
            }
        };

        /* TODO: Is this correct? not sure how newlines work
        if i.newline_before_next_token() {
            return place;
        }
        */

        let mut place = place;
        loop {
            match peek_next_token(i) {
                Some(".") => {
                    // Drop "."
                    next_token(i);
                    let method_name = next_token(i).unwrap();
                    match method_name {
                        "{" | "}" => panic!("Bad char in method name"),
                        _ => {}
                    };
                    place = Expression::Call(Box::new(place), self.parse_func_call(i, method_name))
                }
                Some("?") => {
                    assert_eq!(next_token(i), Some("?"));
                    let left = self.parse_expr(i);
                    assert_eq!(next_token(i), Some(":"));
                    let right = self.parse_expr(i);
                    break Expression::Ternary(place.into(), left.into(), right.into());
                }
                Some(x) => {
                    if is_binary_op(x) {
                        let op = next_token(i).unwrap();
                        let result = match op {
                            "||" => Expression::Or(Box::new(place), Box::new(self.parse_expr(i))),
                            "&&" => Expression::And(Box::new(place), Box::new(self.parse_expr(i))),
                            _ => Expression::Call(Box::new(place), self.parse_func_call(i, op)),
                        };
                        place = result;
                    } else {
                        break place;
                    }
                }

                None => break place,
            }
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
        _locals: &mut Scope<'text>,
    ) -> Statement<'text> {
        match next_token(i).expect("EOF when parsing statement") {
            "foreign" => todo!("Foreign class defs"),
            "class" => {
                let name = next_token(i).expect("EOF when parsing class name");
                let class_builder;
                let mut super_slot = crate::common::GlobalClassSlots::Object as usize;
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
                    // FIXME: Classes can exist outside of global scope
                    let super_class = &self.global_classes[super_name];
                    super_slot =
                        None // locals
                            //.get_index(super_name)
                            .or_else(|| self.globals.get_index(super_name))
                            .unwrap();
                    class_builder = ClassDef::child_of(super_class, name);
                } else {
                    let super_class = self.global_classes.get("Object");
                    class_builder = match super_class {
                        Some(object_class) => ClassDef::child_of(object_class, name),
                        None => ClassBuilder::new(name),
                    }
                }

                //locals.declare(name);
                //FIXME
                self.globals.declare(name);

                let old_class = self.current_class.replace(class_builder);
                let def = self.parse_class_body(i);
                self.current_class = old_class;
                self.global_classes.insert(name, Rc::clone(&def));
                self.classes.push(Rc::clone(&def));
                self.classes
                    // SAFETY: Metaclass is never written to
                    // Furthermore, this reference is immediately cloned
                    .push(unsafe { def.get_meta_class() }.map(Rc::clone).unwrap());
                Statement::AssignGlobal(
                    self.globals.get_index(name).unwrap(),
                    Box::new(Expression::ClassBody(ClassRef(def), super_slot)),
                )
            }
            "if" => self.parse_if(i, _locals), //parse_if(i, ctx),
            "return" => {
                if i.newline_before_next_token() {
                    Statement::Return(Expression::Primitive(Primitive::Null))
                } else {
                    Statement::Return(self.parse_expr(i))
                }
            }
            "yield" => {
                if i.newline_before_next_token() {
                    Statement::Yield(Expression::Primitive(Primitive::Null))
                } else {
                    Statement::Yield(self.parse_expr(i))
                }
            }
            "{" => self.parse_block(i, _locals),
            "while" => {
                assert_eq!(next_token(i), Some("("));
                let cond = self.parse_expr(i);
                assert_eq!(next_token(i), Some(")"));
                let block = self.parse_statement(i, _locals);
                Statement::While(cond, Box::new(block))
            }
            "for" => {
                assert_eq!(next_token(i), Some("("));
                // TODO: Mutiple var names allowed?
                let var_name = next_token(i).unwrap();
                assert_eq!(next_token(i), Some("in"));
                let sequence = self.parse_expr(i);
                assert_eq!(next_token(i), Some(")"));
                let body = self.parse_statement(i, _locals);
                dbg!(var_name, sequence, body);
                todo!("for loops");
            }
            "break" => Statement::Break,
            "continue" => Statement::Continue,
            "var" => {
                let name = peek_next_token(i).unwrap();
                self.globals.declare(name);

                // Look ahead past the name to see if we're in an assignment
                if peek_nth_token(i, 1) != Some("=") {
                    // Drop the name
                    next_token(i);
                }
                self.parse_statement(i, _locals)
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
                                _locals.get_index(x).unwrap(),
                                Box::new(self.parse_expr(i)),
                            )
                        } else {
                            i.rollback(x.len());
                            Statement::ExprStatement(self.parse_expr(i))
                        }
                    }
                    Some(NameType::Global) => {
                        if assignment {
                            Statement::AssignGlobal(
                                self.globals.get_index(x).unwrap(),
                                Box::new(self.parse_expr(i)),
                            )
                        } else {
                            i.rollback(x.len());
                            Statement::ExprStatement(self.parse_expr(i))
                        }
                    }
                    Some(NameType::ThisCall) => {
                        i.rollback(x.len());
                        Statement::ExprStatement(self.parse_expr(i))
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

    fn parse_if(
        &mut self,
        i: &mut StringStream<'text>,
        _locals: &mut Scope<'text>,
    ) -> Statement<'text> {
        use crate::ast::IfBody;
        assert_eq!(peek_next_token(i), Some("("));
        let cond = self.parse_expr(i);
        let body = self.parse_statement(i, _locals);
        let if_body = if let Some(Consumed::Expected) = consume_next_token_if(i, "else") {
            if let Consumed::Expected = consume_next_token_if(i, "if").unwrap() {
                todo!("elseif chain")
            } else {
                let r#else = self.parse_statement(i, _locals);
                IfBody::ThenElse {
                    then: Box::new(body),
                    r#else: Box::new(r#else),
                }
            }
        } else {
            IfBody::Then {
                then: Box::new(body),
            }
        };
        Statement::If(Box::new(cond), if_body)
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
        } else if let Some(Consumed::Expected) = consume_next_token_if(i, "}") {
            Statement::Block(vec![])
        } else {
            let s = self.parse_statement(i, locals);
            assert_eq!(next_token(i), Some("}"));
            if let Statement::ExprStatement(e) = s {
                Statement::Return(e)
            } else {
                s
            }
        }
    }

    fn parse_func_call<S: Into<std::borrow::Cow<'text, str>>>(
        &mut self,
        i: &mut StringStream<'text>,
        name: S,
    ) -> AstSig<'text> {
        let intermediate;
        let name = name.into();
        if is_binary_op(&name) {
            return AstSig::Func(name, vec![self.parse_expr(i)]);
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
                        x => panic!("Unexpected token {x:?} in arg list for function call"),
                    }
                }
                assert_eq!(next_token(i), Some(")"));
                return AstSig::Func(name, args);
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
            let parsed_args = Parser::parse_args_list(i, "]");
            let args = &mut self.current_method.as_mut().unwrap().args;
            for parsed in &parsed_args {
                args.declare(parsed);
            }
            arity = Arity::SubscriptGetter(parsed_args.len());
            assert_eq!(next_token(i), Some("]"))
        } else if next_token_is(i, "(").unwrap() {
            let parsed_args = Parser::parse_args_list(i, ")");
            let args = &mut self.current_method.as_mut().unwrap().args;
            for parsed in &parsed_args {
                args.declare(parsed);
            }
            arity = Arity::Func(parsed_args.len());
            assert_eq!(next_token(i), Some(")"));
        } else {
            arity = Arity::Getter
        }

        if next_token_is(i, "=").unwrap() {
            assert_eq!(next_token(i), Some("("));
            let args = Parser::parse_args_list(i, ")");
            assert_eq!(next_token(i), Some(")"));
            assert_eq!(args.len(), 1, "Only one value can be set by a setter");
            for setter_arg in args {
                self.current_method
                    .as_mut()
                    .unwrap()
                    .args
                    .declare(setter_arg);
            }
            arity = match arity {
                Arity::Getter => Arity::Setter,
                Arity::SubscriptGetter(n) => Arity::SubscriptSetter(n),
                _x => panic!(),
            }
        }

        Signature::new(name.into(), arity)
    }

    fn parse_args_list(i: &mut StringStream<'text>, closing: &str) -> Vec<&'text str> {
        let mut args = vec![];
        loop {
            let next = peek_next_token(i).unwrap();
            if next == "," {
                panic!("Too many commas")
            } else if next == closing {
                break;
            }
            let name = next_token(i).expect("EOF when parsing parameter list");
            args.push(name);
            let next = peek_next_token(i).unwrap();
            if next == "," {
                next_token(i);
                continue;
            } else if next == closing {
                break;
            } else {
                panic!("Malformed list");
            }
        }

        args
    }

    fn parse_class_body(&mut self, i: &mut StringStream<'text>) -> Rc<ClassDef<'text>> {
        assert_eq!(next_token(i), Some("{"));
        let ref_self = RefCell::new(self);
        while peek_next_token(i).expect("EOF when parsing class body") != "}" {
            let mut binding = ref_self.borrow_mut();
            let specifier = peek_next_token(i).unwrap();
            let method_type = match specifier {
                "construct" => {
                    next_token(i);
                    MethodType::Constructor
                }
                "static" => {
                    next_token(i);
                    MethodType::Static
                }
                "foreign" => todo!(),
                _ => MethodType::Normal,
            };
            let old_method = binding.current_method.replace(MethodContext {
                typ: method_type,
                ..Default::default()
            });
            let sig = binding.parse_sig(i);
            binding.current_method.as_mut().unwrap().sig = Some(sig.clone());
            let body = binding.parse_method_body(i);

            let class = binding
                .current_class
                .as_mut()
                .expect("Class body outside of class");

            match method_type {
                MethodType::Normal => class.add_method(sig, body),
                MethodType::Constructor => class.add_constructor(sig, body),
                MethodType::Static => class.add_static_method(sig, body),
                MethodType::Foreign => todo!(),
            };
            binding.current_method = old_method;
            drop(binding);
        }
        assert_eq!(next_token(i), Some("}"));

        let class_class = ref_self.borrow().global_classes.get("Class").map(Rc::clone);
        ref_self
            .into_inner()
            .current_class
            .take()
            .unwrap()
            .finish(class_class)
    }

    fn parse_method_body(&mut self, i: &mut StringStream<'text>) -> MethodAst<'text> {
        let mut locals = Scope::new();
        MethodAst {
            ast: self.parse_statement(i, &mut locals),
        }
    }

    fn parse_string(&mut self, i: &mut StringStream<'text>) -> StringAddress {
        let start = i.index();
        let mut end = start;
        let mut cow: Cow<'text, str> = Cow::Borrowed(&i.source[start..end]);
        loop {
            let c = i.next();
            if c.is_none() {
                break;
            }
            let c = c.unwrap();
            if c == '"' {
                break;
            } else if c == '\\' {
                let escaped = i
                    .next()
                    .expect("Unexpected EOF after backslash in string literal");
                let new_char = match escaped {
                    'n' => '\n',
                    // TODO: Other escapes
                    _ => escaped,
                };
                cow.to_mut().push(new_char);
                end += 1;
            }
            end += 1;

            // As long as there haven't been any escapes, this Cow can stay as a pointer into the
            // source text
            if let Cow::Borrowed(_) = cow {
                cow = Cow::Borrowed(&i.source[start..end]);
            } else if c != '\\' {
                cow.to_mut().push(c)
            }
        }

        //println!("Parsed string: {cow:?}");
        if let Some(index) = self.strings.iter().position(|s| s == &cow) {
            index
        } else {
            self.strings.push(cow);
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
        use std::fs::File;
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

    #[test]
    fn comments() {
        let s = r"
        token1 //Nothing else parsed /* even here */ class whatever
        token/ * not a real comment */ mismatched closing
        /*
            anything can go in here
            // even this
         */
        fin/**/al tokens
        ";
        let mut stream = StringStream::from_str(s);
        let i = &mut stream;
        assert_eq!(peek_next_token(i), Some("token1"));
        assert_eq!(next_token(i), Some("token1"));
        assert_eq!(peek_next_token(i), Some("token"));
        assert_eq!(next_token(i), Some("token"));
        assert_eq!(peek_next_token(i), Some("/"));
        assert_eq!(next_token(i), Some("/"));
        assert_eq!(peek_next_token(i), Some("*"));
        assert_eq!(next_token(i), Some("*"));
        assert_eq!(peek_next_token(i), Some("not"));
        assert_eq!(next_token(i), Some("not"));
        assert_eq!(peek_next_token(i), Some("a"));
        assert_eq!(next_token(i), Some("a"));
        assert_eq!(peek_next_token(i), Some("real"));
        assert_eq!(next_token(i), Some("real"));
        assert_eq!(peek_next_token(i), Some("comment"));
        assert_eq!(next_token(i), Some("comment"));
        assert_eq!(peek_next_token(i), Some("*"));
        assert_eq!(next_token(i), Some("*"));
        assert_eq!(peek_next_token(i), Some("/"));
        assert_eq!(next_token(i), Some("/"));
        assert_eq!(peek_next_token(i), Some("mismatched"));
        assert_eq!(next_token(i), Some("mismatched"));
        assert_eq!(peek_next_token(i), Some("closing"));
        assert_eq!(next_token(i), Some("closing"));
        assert_eq!(peek_next_token(i), Some("fin"));
        assert_eq!(next_token(i), Some("fin"));
        assert_eq!(peek_next_token(i), Some("al"));
        assert_eq!(next_token(i), Some("al"));
        assert_eq!(peek_next_token(i), Some("tokens"));
        assert_eq!(next_token(i), Some("tokens"));
    }
}
