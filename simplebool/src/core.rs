use crate::syntax::*;

use std::rc::Rc;

pub fn eval1(t: &Rc<Term>, c: &mut Context) -> Option<Rc<Term>> {
    match &**t {
        Term::App(t1, t2) => Some(match &**t1 {
            Term::Abs(_, _, t12) if t2.is_val() => t12.subst_top(t2.clone()),
            _ if t1.is_val() => Term::App(t1.clone(), eval1(t2, c)?).into(),
            _ => Term::App(eval1(t1, c)?, t2.clone()).into(),
        }),
        Term::If(t1, t2, t3) => Some(match &**t1 {
            Term::True => t2.clone(),
            Term::False => t3.clone(),
            _ => Term::If(eval1(t1, c)?, t2.clone(), t3.clone()).into(),
        }),
        _ => None,
    }
}

pub fn eval(t: Rc<Term>, c: &mut Context) -> Rc<Term> {
    let mut t = t;
    while let Some(next) = eval1(&t, c) {
        t = next;
    }
    return t;
}

pub fn type_of(t: &Rc<Term>, c: &mut Context) -> Option<Rc<Type>> {
    // TODO: change return type to Result<...>
    match &**t {
        Term::Var(i) => c.get_type(*i).map(|r| r.clone()),
        Term::Abs(x, ty1, t2) => c.with_binding(x.clone(), Binding::Var(ty1.clone()), |c| {
            let ty1 = ty1.clone();
            let ty2 = type_of(t2, c)?;
            Some(Type::Arrow(ty1, ty2).into())
        }),
        Term::App(t1, t2) => {
            let ty1 = type_of(t1, c)?;
            let ty2 = type_of(t2, c)?;
            if let Type::Arrow(ty11, ty12) = &*ty1 {
                if *ty2 == **ty11 {
                    return Some(ty12.clone());
                }
            }
            None
        }
        Term::True | Term::False => Some(Type::Bool.into()),
        Term::If(t1, t2, t3) => {
            if *type_of(t1, c)? == Type::Bool {
                let ty2 = type_of(t2, c)?;
                let ty3 = type_of(t3, c)?;
                if *ty2 == *ty3 {
                    return Some(ty2);
                }
            }
            None
        }
    }
}

#[test]
fn test_type_of() {
    let t = Term::App(
        Term::Abs("x".into(), Type::Bool.into(), Term::Var(0).into()).into(),
        Term::True.into(),
    )
    .into();
    let mut c = Context::new();
    let ty = type_of(&t, &mut c).unwrap();
    assert_eq!(*ty, Type::Bool);
}
