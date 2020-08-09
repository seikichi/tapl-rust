use crate::syntax::*;

use std::rc::Rc;

fn is_val(t: Rc<Term>) -> bool {
    match &*t {
        Term::Abs(_, _) => true,
        _ => false,
    }
}

fn eval1(t: Rc<Term>, c: Rc<Context>) -> Option<Rc<Term>> {
    match &*t {
        Term::App(t1, t2) => Some(match (&**t1, &**t2) {
            (Term::Abs(_, t12), _) if is_val(t2.clone()) => term_subst_top(t2.clone(), t12.clone()),
            _ if is_val(t1.clone()) => Term::app(t1.clone(), eval1(t2.clone(), c)?),
            _ => Term::app(eval1(t1.clone(), c)?, t2.clone()),
        }),
        Term::Var(n) => match c.get(*n)? {
            Binding::Term(t) => Some(term_shift(n + 1, t.clone())),
            Binding::Name => None,
        },
        _ => None,
    }
}

pub fn eval(t: Rc<Term>, c: Rc<Context>) -> Rc<Term> {
    let mut t = t;
    while let Some(next) = eval1(t.clone(), c.clone()) {
        t = next;
    }
    return t;
}

pub fn eval_binding(b: Binding, c: Rc<Context>) -> Binding {
    match b {
        Binding::Term(t) => Binding::Term(eval(t, c.clone())),
        _ => b,
    }
}
