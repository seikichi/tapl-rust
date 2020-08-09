use std::borrow::Borrow;
use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum Term {
    Var(i32),
    Abs(String, Rc<Term>),
    App(Rc<Term>, Rc<Term>),
}

impl Term {
    pub fn var(n: i32) -> Rc<Term> {
        Rc::new(Term::Var(n))
    }

    pub fn abs(name: String, t: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::Abs(name, t))
    }

    pub fn app(t1: Rc<Term>, t2: Rc<Term>) -> Rc<Term> {
        Rc::new(Term::App(t1, t2))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Binding {
    Name,
    Term(Rc<Term>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Command {
    Eval(Rc<Term>),
    Bind(String, Binding),
}

#[derive(Debug, PartialEq)]
pub enum Context {
    Cons((String, Binding), Rc<Context>),
    Nil,
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

    pub fn get(self: &Rc<Context>, index: i32) -> Option<Binding> {
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

    pub fn name(self: &Rc<Context>, index: i32) -> Option<String> {
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

    pub fn index<T: Borrow<str>>(self: &Rc<Context>, x: &T) -> Option<i32> {
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

    pub fn is_name_bound<T: Borrow<str>>(self: &Rc<Context>, x: &T) -> bool {
        let mut next = self.clone();
        while let Context::Cons((name, _), cdr) = &*next {
            if name == x.borrow() {
                return true;
            }
            next = cdr.clone();
        }
        false
    }

    pub fn pick_fresh_name<T: Borrow<str>>(self: &Rc<Context>, x: &T) -> (Rc<Context>, String) {
        let mut name: String = x.borrow().into();
        while self.is_name_bound(&name) {
            name.push_str("'");
        }
        (self.with_name(name.clone()), name)
    }
}

pub fn term_shift(d: i32, t: Rc<Term>) -> Rc<Term> {
    fn walk(c: i32, d: i32, t: Rc<Term>) -> Rc<Term> {
        match &*t {
            Term::Var(x) if *x >= c => Term::var(*x + d),
            Term::Var(_) => t,
            Term::Abs(n, t1) => Term::abs(n.clone(), walk(c + 1, d, t1.clone())),
            Term::App(t1, t2) => Term::app(walk(c, d, t1.clone()), walk(c, d, t2.clone())),
        }
    }
    walk(0, d, t)
}

pub fn term_subst(j: i32, s: Rc<Term>, t: Rc<Term>) -> Rc<Term> {
    fn walk(j: i32, s: Rc<Term>, c: i32, t: Rc<Term>) -> Rc<Term> {
        match &*t {
            Term::Var(x) if *x == j + c => term_shift(c, s),
            Term::Var(_) => t,
            Term::Abs(n, t1) => Term::abs(n.clone(), walk(j, s, c + 1, t1.clone())),
            Term::App(t1, t2) => Term::app(
                walk(j, s.clone(), c, t1.clone()),
                walk(j, s.clone(), c, t2.clone()),
            ),
        }
    }
    walk(j, s, 0, t)
}

pub fn term_subst_top(s: Rc<Term>, t: Rc<Term>) -> Rc<Term> {
    term_shift(-1, term_subst(0, term_shift(1, s), t))
}
