use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum Type {
    Arrow(Rc<Type>, Rc<Type>),
    Bool,
}

#[derive(Debug, PartialEq)]
pub enum Term {
    Var(i32),
    Abs(String, Rc<Type>, Rc<Term>),
    App(Rc<Term>, Rc<Term>),
    True,
    False,
    If(Rc<Term>, Rc<Term>, Rc<Term>),
}

#[derive(Debug, PartialEq, Clone)]
pub enum Binding {
    Name,
    Var(Rc<Type>),
}

#[derive(Debug, PartialEq)]
pub enum Command {
    Eval(Rc<Term>),
    Bind(String, Binding),
}

#[derive(Debug)]
pub struct Context {
    bindings: Vec<(String, Binding)>,
}

impl Term {
    pub fn is_val(self: &Rc<Term>) -> bool {
        match &**self {
            Term::True | Term::False | Term::Abs(_, _, _) => true,
            _ => false,
        }
    }

    fn map<F: Copy + Fn(i32, i32) -> Rc<Term>>(self: &Rc<Term>, c: i32, onvar: F) -> Rc<Term> {
        match &**self {
            Term::Var(x) => onvar(c, *x),
            Term::Abs(x, ty1, t2) => Term::Abs(x.clone(), ty1.clone(), t2.map(c + 1, onvar)).into(),
            Term::App(t1, t2) => Term::App(t1.map(c, onvar), t2.map(c, onvar)).into(),
            Term::True | Term::False => self.clone(),
            Term::If(t1, t2, t3) => {
                Term::If(t1.map(c, onvar), t2.map(c, onvar), t3.map(c, onvar)).into()
            }
        }
    }

    fn shift_above(self: &Rc<Term>, d: i32, c: i32) -> Rc<Term> {
        self.map(c, |c, x| {
            if x >= c {
                Term::Var(x + d).into()
            } else {
                Term::Var(x).into()
            }
        })
    }

    fn shift(self: &Rc<Term>, d: i32) -> Rc<Term> {
        self.shift_above(d, 0)
    }

    fn subst(self: &Rc<Term>, j: i32, s: Rc<Term>) -> Rc<Term> {
        self.map(j, |c, x| {
            if x == c {
                s.shift(c).into()
            } else {
                Term::Var(x).into()
            }
        })
    }

    pub fn subst_top(self: &Rc<Term>, s: Rc<Term>) -> Rc<Term> {
        self.subst(0, s.shift(1)).shift(-1)
    }
}

impl Context {
    pub fn new() -> Self {
        Self { bindings: vec![] }
    }

    pub fn with_name<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, f: F) -> R {
        self.with_binding(x, Binding::Name, f)
    }

    pub fn with_binding<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, b: Binding, f: F) -> R {
        self.bindings.push((x, b));
        let result = f(self);
        self.bindings.pop();
        result
    }

    pub fn add_binding(&mut self, x: String, b: Binding) {
        self.bindings.push((x, b));
    }

    pub fn get_name(&self, index: i32) -> Option<&String> {
        let index = self.bindings.len() - (index as usize) - 1;
        self.bindings.get(index).map(|(x, _)| x)
    }

    pub fn get_binding(&self, index: i32) -> Option<&Binding> {
        let index = self.bindings.len() - (index as usize) - 1;
        self.bindings.get(index).map(|(_, b)| b)
    }

    pub fn get_index(&self, x: &str) -> Option<i32> {
        self.bindings
            .iter()
            .rev()
            .position(|(s, _)| s == x)
            .map(|i| (self.bindings.len() - i - 1) as i32)
    }

    pub fn get_type(&self, index: i32) -> Option<&Rc<Type>> {
        match self.get_binding(index)? {
            Binding::Var(t) => Some(t),
            _ => None,
        }
    }

    pub fn with_fresh_name<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, f: F) -> R {
        let mut name: String = x;
        while self.is_name_bound(&name) {
            name.push_str("'");
        }
        self.with_name(name, f)
    }

    fn is_name_bound(&self, x: &str) -> bool {
        self.bindings.iter().rev().any(|(s, _)| s == x)
    }
}
