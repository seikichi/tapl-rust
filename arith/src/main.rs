#![feature(box_syntax, box_patterns)]
use std::rc::Rc;

#[derive(Debug)]
enum Term {
    True,
    False,
    If(Rc<Term>, Rc<Term>, Rc<Term>),
    Zero,
    Succ(Rc<Term>),
    Pred(Rc<Term>),
    IsZero(Rc<Term>),
}

fn is_numeric_val(t: Rc<Term>) -> bool {
    match &*t {
        Term::Zero => true,
        Term::Succ(t1) => is_numeric_val(t1.clone()),
        _ => false,
    }
}

// fn is_val(t: Rc<Term>) -> bool {
//     match &*t {
//         Term::True => true,
//         Term::False => true,
//         _ if is_numeric_val(t.clone()) => true,
//         _ => false,
//     }
// }

fn eval1(t: Rc<Term>) -> Option<Rc<Term>> {
    match &*t {
        Term::If(t1, t2, t3) => Some(match &**t1 {
            Term::True => t2.clone(),
            Term::False => t3.clone(),
            _ => Term::If(eval1(t1.clone())?, t2.clone(), t3.clone()).into(),
        }),
        Term::Succ(t1) => Some(Term::Succ(eval1(t1.clone())?).into()),
        Term::Pred(t1) => Some(match &**t1 {
            Term::Succ(nv1) if is_numeric_val(nv1.clone()) => nv1.clone(),
            _ => Term::Pred(eval1(t1.clone())?).into(),
        }),
        Term::IsZero(t1) => Some(match &**t1 {
            Term::Zero => Term::True.into(),
            Term::Succ(nv1) if is_numeric_val(nv1.clone()) => Term::False.into(),
            _ => Term::IsZero(eval1(t1.clone())?).into(),
        }),
        _ => None,
    }
}

fn eval(t: Rc<Term>) -> Rc<Term> {
    let mut t = t;
    while let Some(next) = eval1(t.clone()) {
        t = next;
    }
    return t;
}

fn main() {
    let t = Rc::new(Term::IsZero(
        Term::Pred(Term::Succ(Term::Succ(Term::Zero.into()).into()).into()).into(),
    ));
    // eval(IsZero(Pred(Succ(Succ(Zero))))) -> False
    println!("eval({:?}) -> {:?}", t, eval(t.clone()));

    let t = Rc::new(Term::If(
        Term::False.into(),
        Term::True.into(),
        Term::False.into(),
    ));
    // eval(If(False, True, False)) -> False
    println!("eval({:?}) -> {:?}", t, eval(t.clone()));
}
