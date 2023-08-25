pub struct ExactRepeat<T: Clone> {
    value: T,
    n: usize,
}

impl<T: Clone> ExactRepeat<T> {
    fn new(n: usize, value: T) -> Self {
        ExactRepeat { value, n }
    }
}

impl<T: Clone> Iterator for ExactRepeat<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.n == 0 {
            return None;
        }

        self.n -= 1;
        Some(self.value.clone())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.n, self.n.into())
    }
}

impl<T: Clone> ExactSizeIterator for ExactRepeat<T> {}

pub struct ExactRepeatWith<F> {
    f: F,
    n: usize,
}

impl<T, F: FnMut() -> T> ExactRepeatWith<F> {
    fn new(n: usize, f: F) -> Self {
        ExactRepeatWith { f, n }
    }
}

impl<T, F: FnMut() -> T> Iterator for ExactRepeatWith<F> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.n == 0 {
            return None;
        }

        self.n -= 1;
        Some((self.f)())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.n, self.n.into())
    }
}

impl<T, F: FnMut() -> T> ExactSizeIterator for ExactRepeatWith<F> {}

pub fn exact_repeat<T: Clone>(n: usize, value: T) -> ExactRepeat<T> {
    ExactRepeat::new(n, value)
}
pub fn exact_repeat_with<T, F: FnMut() -> T>(n: usize, f: F) -> ExactRepeatWith<F> {
    ExactRepeatWith::new(n, f)
}
