use std::borrow::Borrow;
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

#[derive(Debug, Clone)]
pub enum Binding {
    Name,
    Var(Rc<Type>),
}

#[derive(Debug)]
pub enum Command {
    Eval(Rc<Term>),
    Bind(String, Binding),
}

#[derive(Debug)]
pub enum Context {
    Cons((String, Binding), Rc<Context>),
    Nil,
}

impl Term {
    pub fn is_val(self: &Rc<Term>) -> bool {
        match &**self {
            Term::True | Term::False | Term::Abs(_, _, _) => true,
            _ => false,
        }
    }
}

impl Context {
    pub fn new() -> Rc<Self> {
        Rc::new(Context::Nil)
    }

    pub fn with_name(self: &Rc<Context>, x: String) -> Rc<Self> {
        self.with_binding(x, Binding::Name)
    }

    pub fn with_binding(self: &Rc<Context>, x: String, b: Binding) -> Rc<Self> {
        Rc::new(Context::Cons((x, b), self.clone()))
    }

    pub fn get_name(self: &Rc<Context>, index: i32) -> Option<String> {
        let mut next = self.clone();
        let mut i: i32 = 0;
        while let Context::Cons((s, _), cdr) = &*next {
            if i == index {
                return Some(s.clone());
            }
            i += 1;
            next = cdr.clone();
        }
        None
    }

    pub fn get_index<T: Borrow<str>>(self: &Rc<Context>, x: &T) -> Option<i32> {
        let mut next = self.clone();
        let mut i: i32 = 0;
        while let Context::Cons((name, _), cdr) = &*next {
            if name == x.borrow() {
                return Some(i);
            }
            i += 1;
            next = cdr.clone();
        }
        None
    }

    pub fn get_binding(self: &Rc<Context>, index: i32) -> Option<Binding> {
        let mut next = self.clone();
        let mut i: i32 = 0;
        while let Context::Cons((_, b), cdr) = &*next {
            if i == index {
                return Some(b.clone());
            }
            i += 1;
            next = cdr.clone();
        }
        None
    }

    pub fn get_type(self: &Rc<Context>, index: i32) -> Option<Rc<Type>> {
        match self.get_binding(index)? {
            Binding::Var(t) => Some(t),
            _ => None,
        }
    }

    pub fn pick_fresh_name<T: Borrow<str>>(self: &Rc<Context>, x: &T) -> (Rc<Context>, String) {
        let mut name: String = x.borrow().into();
        while self.is_name_bound(&name) {
            name.push_str("'");
        }
        (self.with_name(name.clone()), name)
    }

    fn is_name_bound<T: Borrow<str>>(self: &Rc<Context>, x: &T) -> bool {
        let mut next = self.clone();
        while let Context::Cons((name, _), cdr) = &*next {
            if name == x.borrow() {
                return true;
            }
            next = cdr.clone();
        }
        false
    }
}

pub fn term_shift(d: i32, t: Rc<Term>) -> Rc<Term> {
    fn walk(c: i32, d: i32, t: Rc<Term>) -> Rc<Term> {
        match &*t {
            Term::Var(x) if *x >= c => Term::Var(*x + d).into(),
            Term::Var(_) => t,
            Term::Abs(n, ty, t1) => {
                Term::Abs(n.clone(), ty.clone(), walk(c + 1, d, t1.clone())).into()
            }
            Term::App(t1, t2) => Term::App(walk(c, d, t1.clone()), walk(c, d, t2.clone())).into(),
            Term::True | Term::False => t.clone(),
            Term::If(t1, t2, t3) => Term::If(
                walk(c, d, t1.clone()),
                walk(c, d, t2.clone()),
                walk(c, d, t3.clone()),
            )
            .into(),
        }
    }
    walk(0, d, t)
}

pub fn term_subst(j: i32, s: Rc<Term>, t: Rc<Term>) -> Rc<Term> {
    fn walk(j: i32, s: Rc<Term>, c: i32, t: Rc<Term>) -> Rc<Term> {
        match &*t {
            Term::Var(x) if *x == j + c => term_shift(c, s),
            Term::Var(_) => t,
            Term::Abs(n, ty, t1) => {
                Term::Abs(n.clone(), ty.clone(), walk(j, s, c + 1, t1.clone())).into()
            }
            Term::App(t1, t2) => Term::App(
                walk(j, s.clone(), c, t1.clone()),
                walk(j, s.clone(), c, t2.clone()),
            )
            .into(),
            Term::True | Term::False => t.clone(),
            Term::If(t1, t2, t3) => Term::If(
                walk(j, s.clone(), c, t1.clone()),
                walk(j, s.clone(), c, t2.clone()),
                walk(j, s.clone(), c, t3.clone()),
            )
            .into(),
        }
    }
    walk(j, s, 0, t)
}

pub fn term_subst_top(s: Rc<Term>, t: Rc<Term>) -> Rc<Term> {
    term_shift(-1, term_subst(0, term_shift(1, s), t))
}
