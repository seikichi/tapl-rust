use std::fmt;
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

#[derive(Debug, Clone)]
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

    pub fn display(self: &Rc<Term>, c: &Context) -> TermDisplay {
        TermDisplay {
            term: self.clone(),
            context: (*c).clone(),
        }
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

    pub fn add_name(&mut self, x: String) {
        self.add_binding(x, Binding::Name);
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
            .map(|i| i as i32)
    }

    pub fn get_type(&self, index: i32) -> Option<&Rc<Type>> {
        match self.get_binding(index)? {
            Binding::Var(t) => Some(t),
            _ => None,
        }
    }

    pub fn add_fresh_name(&mut self, x: String) -> String {
        let mut name: String = x;
        while self.is_name_bound(&name) {
            name.push_str("'");
        }
        self.add_name(name.clone());
        name
    }

    fn is_name_bound(&self, x: &str) -> bool {
        self.bindings.iter().rev().any(|(s, _)| s == x)
    }
}

pub struct TermDisplay {
    term: Rc<Term>,
    context: Context,
}

impl fmt::Display for TermDisplay {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(f)
    }
}

impl TermDisplay {
    fn format(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.term {
            Term::Abs(x, _ty, t1) => {
                let mut c = self.context.clone();
                let x = c.add_fresh_name(x.clone());
                write!(f, "λ {}. ", x)?;
                t1.display(&c).format(f)
            }
            Term::If(t1, t2, t3) => {
                write!(f, "if ")?;
                t1.display(&self.context).format(f)?;
                write!(f, " then ")?;
                t2.display(&self.context).format(f)?;
                write!(f, " else ")?;
                t3.display(&self.context).format(f)
            }
            _ => self.format_app_term(f),
        }
    }

    fn format_app_term(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.term {
            Term::App(t1, t2) => {
                t1.display(&self.context).format_app_term(f)?;
                write!(f, " ")?;
                t2.display(&self.context).format_atomic_term(f)
            }
            _ => self.format_atomic_term(f),
        }
    }

    fn format_atomic_term(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.term {
            Term::Var(x) => write!(f, "{}", self.context.get_name(*x).unwrap()),
            Term::True => write!(f, "true"),
            Term::False => write!(f, "false"),
            _ => {
                write!(f, "(")?;
                self.format(f)?;
                write!(f, ")")
            }
        }
    }
}
