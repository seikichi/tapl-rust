#![feature(box_syntax, box_patterns)]

// use std::env;
use std::fmt;
// use std::fs;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    TyVar(Rc<str>, usize),
    TyId(Rc<str>),
    TyArr(Box<Ty>, Box<Ty>),
    TyString,
    TyUnit,
    TyRecord(Vec<(Rc<str>, Ty)>),
    TyBool,
    TyFloat,
    TyNat,
    TyAll(Rc<str>, Box<Ty>),
    TySome(Rc<str>, Box<Ty>),
}

#[derive(Debug, Clone)]
pub enum Term {
    TmVar(Rc<str>, usize),
    TmAbs(Rc<str>, Ty, Box<Term>),
    TmApp(Box<Term>, Box<Term>),
    TmLet(Rc<str>, Box<Term>, Box<Term>),
    TmFix(Box<Term>),
    TmString(Rc<str>),
    TmUnit,
    TmAscribe(Box<Term>, Ty),
    TmRecord(Vec<(Rc<str>, Term)>),
    TmProj(Box<Term>, Rc<str>),
    TmTrue,
    TmFalse,
    TmIf(Box<Term>, Box<Term>, Box<Term>),
    TmFloat(f32),
    TmTimesfloat(Box<Term>, Box<Term>),
    TmZero,
    TmSucc(Box<Term>),
    TmPred(Box<Term>),
    TmIsZero(Box<Term>),
    TmInert(Ty),
    TmPack(Ty, Box<Term>, Ty),
    TmUnpack(Rc<str>, Rc<str>, Box<Term>, Box<Term>),
    TmTAbs(Rc<str>, Box<Term>),
    TmTApp(Box<Term>, Ty),
}

#[derive(Clone, Debug)]
pub enum Binding {
    NameBind,
    TyVarBind,
    VarBind(Ty),
    TyAbbBind(Ty),
    TmAbbBind(Term, Option<Ty>),
}

#[derive(Debug)]
pub enum Command {
    Eval(Term),
    Bind(Rc<str>, Binding),
    SomeBind(Rc<str>, Rc<str>, Term),
}

use Binding::*;
use Command::*;
use Term::*;
use Ty::*;

#[derive(Clone, Debug)]
pub struct Context {
    bindings: Vec<(String, Binding)>,
}

impl Context {
    fn new() -> Self {
        Self { bindings: vec![] }
    }

    fn add_binding(&mut self, x: String, bind: Binding) {
        self.bindings.push((x, bind));
    }

    fn add_name(&mut self, x: String) {
        self.add_binding(x, NameBind);
    }

    fn with_binding<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, bind: Binding, f: F) -> R {
        self.add_binding(x, bind);
        let result = f(self);
        self.bindings.pop();
        result
    }

    fn with_name<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, f: F) -> R {
        self.with_binding(x, NameBind, f)
    }

    fn name2index(&self, x: &str) -> Option<usize> {
        self.bindings.iter().rev().position(|(y, _)| y == x)
    }

    fn get_binding(&self, i: usize) -> Binding {
        let bind = &self.bindings[self.bindings.len() - i - 1].1;
        bind.shift(i as i32 + 1)
    }

    fn get_type(&self, i: usize) -> Ty {
        match self.get_binding(i) {
            VarBind(ty) => ty,
            TmAbbBind(_, Some(ty)) => ty,
            _ => panic!("Wrong kind of binding for variable"),
        }
    }

    fn is_tyabb(&self, i: usize) -> bool {
        match self.get_binding(i) {
            TyAbbBind(_) => true,
            _ => false,
        }
    }

    fn get_tyabb(&self, i: usize) -> Ty {
        match self.get_binding(i) {
            TyAbbBind(ty) => ty,
            _ => panic!("No TyAbbBind"),
        }
    }
}

impl Term {
    fn map<F: Copy + Fn(i32, Rc<str>, usize) -> Self, TF: Copy + Fn(i32, &Ty) -> Ty>(
        &self,
        c: i32,
        onvar: F,
        ontype: TF,
    ) -> Self {
        match &self {
            TmInert(tyt) => TmInert(ontype(c, tyt)),
            TmVar(n, x) => onvar(c, n.clone(), *x),
            TmAbs(x, ty1, t2) => TmAbs(x.clone(), ontype(c, ty1), box t2.map(c + 1, onvar, ontype)),
            TmApp(t1, t2) => TmApp(box t1.map(c, onvar, ontype), box t2.map(c, onvar, ontype)),
            TmLet(x, t1, t2) => TmLet(
                x.clone(),
                box t1.map(c, onvar, ontype),
                box t2.map(c + 1, onvar, ontype),
            ),
            TmFix(t1) => TmFix(box t1.map(c, onvar, ontype)),
            TmString(_) | TmUnit | TmTrue | TmFalse | TmFloat(_) | TmZero => self.clone(),
            TmIf(t1, t2, t3) => TmIf(
                box t1.map(c, onvar, ontype),
                box t2.map(c, onvar, ontype),
                box t3.map(c, onvar, ontype),
            ),
            TmAscribe(t1, tyt1) => TmAscribe(box t1.map(c, onvar, ontype), ontype(c, tyt1)),
            TmTimesfloat(t1, t2) => {
                TmTimesfloat(box t1.map(c, onvar, ontype), box t2.map(c, onvar, ontype))
            }
            TmSucc(t1) => TmSucc(box t1.map(c, onvar, ontype)),
            TmPred(t1) => TmPred(box t1.map(c, onvar, ontype)),
            TmIsZero(t1) => TmIsZero(box t1.map(c, onvar, ontype)),
            TmPack(ty1, t2, ty3) => {
                TmPack(ontype(c, ty1), box t2.map(c, onvar, ontype), ontype(c, ty3))
            }
            TmUnpack(tyx, x, t1, t2) => TmUnpack(
                tyx.clone(),
                x.clone(),
                box t1.map(c, onvar, ontype),
                box t2.map(c + 2, onvar, ontype),
            ),
            TmTAbs(tyx, t2) => TmTAbs(tyx.clone(), box t2.map(c + 1, onvar, ontype)),
            TmTApp(t1, ty2) => TmTApp(box t1.map(c, onvar, ontype), ontype(c, ty2)),
            TmProj(t, l) => TmProj(box t.map(c, onvar, ontype), l.clone()),
            TmRecord(fields) => TmRecord(
                fields
                    .iter()
                    .map(|(li, ti)| (li.clone(), ti.map(c, onvar, ontype)))
                    .collect(),
            ),
        }
    }

    fn shift_above(&self, d: i32, c: i32) -> Self {
        self.map(
            c,
            |c, n, x| {
                if x as i32 >= c {
                    TmVar(n, (x as i32 + d) as usize)
                } else {
                    TmVar(n, x)
                }
            },
            |c, ty| ty.shift_above(d, c),
        )
    }

    fn shift(&self, d: i32) -> Self {
        self.shift_above(d, 0)
    }

    fn subst(&self, j: i32, s: &Self) -> Self {
        self.map(
            j,
            |j, n, x| {
                if x as i32 == j {
                    s.shift(j)
                } else {
                    TmVar(n, x)
                }
            },
            |_, ty| ty.clone(),
        )
    }

    fn subst_top(&self, s: &Self) -> Self {
        self.subst(0, &s.shift(1)).shift(-1)
    }

    fn ty_subst(&self, j: i32, ty: &Ty) -> Self {
        self.map(j, |_, n, x| TmVar(n, x), |j, ty2| ty2.subst(j, ty))
    }

    fn ty_subst_top(&self, ty: &Ty) -> Self {
        self.ty_subst(0, &ty.shift(1)).shift(-1)
    }

    fn is_val(&self, ctx: &Context) -> bool {
        match &self {
            TmAbs(_, _, _) => true,
            TmPack(_, v1, _) if v1.is_val(ctx) => true,
            TmTAbs(_, _) => true,
            _ => false,
        }
    }

    fn eval1(&self, ctx: &Context) -> Option<Self> {
        Some(match self {
            // TmApp
            TmApp(box TmAbs(_, _, t12), v2) if v2.is_val(ctx) => t12.subst_top(v2),
            TmApp(v1, t2) if v1.is_val(ctx) => TmApp(v1.clone(), box t2.eval1(ctx)?),
            TmApp(t1, t2) => TmApp(box t1.eval1(ctx)?, t2.clone()),
            // TmUnpack, TmPack
            TmUnpack(_, _, box TmPack(ty11, v12, _), t2) if v12.is_val(ctx) => {
                v12.shift(1).subst_top(t2).ty_subst_top(ty11)
            }
            TmUnpack(tyx, x, t1, t2) => {
                TmUnpack(tyx.clone(), x.clone(), box t1.eval1(ctx)?, t2.clone())
            }
            TmPack(ty1, t2, ty3) => TmPack(ty1.clone(), box t2.eval1(ctx)?, ty3.clone()),
            // Var
            TmVar(_, n) => match ctx.get_binding(*n) {
                TmAbbBind(t, _) => t.clone(),
                _ => return None,
            },
            // TmTApp
            TmTApp(box TmTAbs(_, t11), ty2) => t11.ty_subst_top(ty2),
            TmTApp(t1, ty2) => TmTApp(box t1.eval1(ctx)?, ty2.clone()),
            // Other
            _ => return None,
        })
    }

    fn eval(&self, ctx: &Context) -> Self {
        let mut t = self.clone();
        while let Some(n) = t.eval1(ctx) {
            t = n;
        }
        t
    }

    fn ty(&self, ctx: &mut Context) -> Ty {
        match self {
            TmVar(_, i) => ctx.get_type(*i),
            TmAbs(x, tyt1, t2) => ctx.with_binding(x.to_string(), VarBind(tyt1.clone()), |ctx| {
                let tyt2 = t2.ty(ctx);
                TyArr(box tyt1.clone(), box tyt2.shift(-1))
            }),
            TmApp(t1, t2) => {
                let tyt1 = t1.ty(ctx);
                let tyt2 = t2.ty(ctx);
                match tyt1.simplify(ctx) {
                    TyArr(box tyt11, box tyt12) if tyt2.eqv(&tyt11, ctx) => tyt12,
                    TyArr(_, _) => panic!("parameter type mismatch"),
                    _ => panic!("arrow type expected"),
                }
            }
            TmTAbs(tyx, t2) => ctx.with_binding(tyx.to_string(), TyVarBind, |ctx| {
                let tyt2 = t2.ty(ctx);
                TyAll(tyx.clone(), box tyt2)
            }),
            TmTApp(t1, tyt2) => {
                let tyt1 = t1.ty(ctx);
                match tyt1.simplify(ctx) {
                    TyAll(_, tyt12) => tyt12.subst_top(tyt2),
                    _ => panic!("universal type expected"),
                }
            }
            _ => panic!("unimplemented"), // TODO
        }
    }

    fn fix(&mut self, ctx: &mut Context) {
        match self {
            TmVar(s, x) => *x = ctx.name2index(s).unwrap(),
            TmAbs(s, ty, t) => {
                ty.fix(ctx);
                ctx.with_name(s.to_string(), |ctx| t.fix(ctx))
            }
            TmLet(s, t1, t2) => {
                t1.fix(ctx);
                ctx.with_name(s.to_string(), |ctx| t2.fix(ctx))
            }
            TmTAbs(s, t) => ctx.with_name(s.to_string(), |ctx| t.fix(ctx)),
            TmUnpack(s1, s2, t1, t2) => {
                t1.fix(ctx);
                ctx.with_name(s1.to_string(), |ctx| {
                    ctx.with_name(s2.to_string(), |ctx| t2.fix(ctx))
                })
            }

            TmApp(t1, t2) => {
                t1.fix(ctx);
                t2.fix(ctx)
            }
            TmTApp(t, ty) => {
                t.fix(ctx);
                ty.fix(ctx)
            }
            TmPack(ty1, t2, ty3) => {
                ty1.fix(ctx);
                t2.fix(ctx);
                ty3.fix(ctx);
            }
            TmFix(t) => t.fix(ctx),
            TmAscribe(t, ty) => {
                t.fix(ctx);
                ty.fix(ctx);
            }
            TmProj(t, _) => t.fix(ctx),
            TmSucc(t) => t.fix(ctx),
            TmPred(t) => t.fix(ctx),
            TmIsZero(t) => t.fix(ctx),
            TmInert(ty) => ty.fix(ctx),
            TmIf(t1, t2, t3) => {
                t1.fix(ctx);
                t2.fix(ctx);
                t3.fix(ctx)
            }
            TmTimesfloat(t1, t2) => {
                t1.fix(ctx);
                t2.fix(ctx)
            }
            TmRecord(fields) => fields.into_iter().for_each(|(_, ti)| ti.fix(ctx)),
            TmUnit | TmString(_) | TmTrue | TmFalse | TmFloat(_) | TmZero => {}
        }
    }

    fn format(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmAbs(x, tyt1, t2) => write!(f, "λ{}:{}. {}", x, tyt1, t2),
            TmLet(x, t1, t2) => write!(f, "let {} = {} in {}", x, t1, t2),
            TmFix(t1) => write!(f, "fix {}", t1),
            TmIf(t1, t2, t3) => write!(f, "if {} then {} else {}", t1, t2, t3),
            TmUnpack(tyx, x, t1, t2) => write!(f, "let {{{}, {}}} = {} in {}", tyx, x, t1, t2),
            TmTAbs(x, t) => write!(f, "λ{}. {}", x, t),
            _ => self.format_app(f),
        }
    }

    fn format_app(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmApp(t1, t2) => {
                t1.format_app(f)?;
                write!(f, " ")?;
                t2.format_atomic(f)
            }
            TmTimesfloat(t1, t2) => {
                write!(f, "timesfloat ")?;
                t1.format_atomic(f)?;
                write!(f, " ")?;
                t2.format_atomic(f)
            }
            TmPred(t1) => {
                write!(f, "pred ")?;
                t1.format_atomic(f)
            }
            TmIsZero(t1) => {
                write!(f, "iszero ")?;
                t1.format_atomic(f)
            }
            TmTApp(t, ty) => {
                t.format_app(f)?;
                write!(f, " [{}]", ty)
            }
            _ => self.format_path(f),
        }
    }

    fn format_path(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmProj(t1, l) => {
                t1.format_atomic(f)?;
                write!(f, ".{}", l)
            }
            _ => self.format_ascribe(f),
        }
    }

    fn format_ascribe(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmAscribe(t1, tyt1) => {
                t1.format_app(f)?;
                write!(f, " as {}", tyt1)
            }
            _ => self.format_atomic(f),
        }
    }

    fn format_atomic(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TmInert(tyt) => write!(f, "inert[{}]", tyt),
            TmVar(x, _) => write!(f, "{}", x),
            TmString(s) => write!(f, "\"{}\"", s),
            TmUnit => write!(f, "unit"),
            TmTrue => write!(f, "true"),
            TmFalse => write!(f, "false"),
            TmFloat(v) => write!(f, "{}", v),
            TmZero => write!(f, "0"),
            TmSucc(box t) => {
                let mut t = t;
                let mut n = 1;
                loop {
                    match t {
                        TmSucc(s) => {
                            n += 1;
                            t = s;
                        }
                        TmZero => return write!(f, "{}", n),
                        _ => {
                            write!(f, "(succ ",)?;
                            t.format_atomic(f)?;
                            return write!(f, ")");
                        }
                    }
                }
            }
            TmRecord(fields) => write!(
                f,
                "{{{}}}",
                fields
                    .iter()
                    .map(|(li, ti)| format!("{} = {}", li, ti))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TmPack(tyt1, t2, tyt3) => write!(f, "{{∃{}, {}}} as {}", tyt1, t2, tyt3),
            _ => write!(f, "({})", self),
        }
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(f)
    }
}

impl Ty {
    fn map<F: Copy + Fn(i32, Rc<str>, usize) -> Self>(&self, c: i32, onvar: F) -> Self {
        match &self {
            TyVar(s, x) => onvar(c, s.clone(), *x),
            TyId(_) | TyString | TyUnit | TyFloat | TyBool | TyNat => self.clone(),
            TyArr(ty1, ty2) => TyArr(box ty1.map(c, onvar), box ty2.map(c, onvar)),
            TyAll(tyx, ty2) => TyAll(tyx.clone(), box ty2.map(c + 1, onvar)),
            TySome(tyx, ty2) => TySome(tyx.clone(), box ty2.map(c + 1, onvar)),
            TyRecord(fieldtys) => TyRecord(
                fieldtys
                    .iter()
                    .map(|(li, tyti)| (li.clone(), tyti.map(c, onvar)))
                    .collect(),
            ),
        }
    }

    fn shift_above(&self, d: i32, c: i32) -> Self {
        self.map(c, |c, s, x| {
            if x as i32 >= c {
                TyVar(s, (x as i32 + d) as usize)
            } else {
                TyVar(s, x)
            }
        })
    }

    fn shift(&self, d: i32) -> Self {
        self.shift_above(d, 0)
    }

    fn subst(&self, j: i32, s: &Self) -> Self {
        self.map(j, |j, n, x| {
            if x as i32 == j {
                s.shift(j)
            } else {
                TyVar(n, x)
            }
        })
    }

    fn subst_top(&self, s: &Self) -> Self {
        self.subst(0, &s.shift(1)).shift(-1)
    }

    fn compute(&self, ctx: &Context) -> Option<Self> {
        match self {
            TyVar(_, i) if ctx.is_tyabb(*i) => Some(ctx.get_tyabb(*i)),
            _ => None,
        }
    }

    fn simplify(&self, ctx: &Context) -> Self {
        let mut ty = self.clone();
        while let Some(next) = ty.compute(ctx) {
            ty = next;
        }
        ty
    }

    fn eqv(&self, rhs: &Ty, ctx: &mut Context) -> bool {
        let tys = self.simplify(ctx);
        let tyt = rhs.simplify(ctx);

        match (&tys, &tyt) {
            (TyVar(_, i), _) if ctx.is_tyabb(*i) => ctx.get_tyabb(*i).eqv(&tyt, ctx),
            (_, TyVar(_, i)) if ctx.is_tyabb(*i) => tys.eqv(&ctx.get_tyabb(*i), ctx),
            (TyVar(_, i), TyVar(_, j)) => i == j,
            (TyArr(tys1, tys2), TyArr(tyt1, tyt2)) => tys1.eqv(&tyt1, ctx) && tys2.eqv(&tyt2, ctx),
            (TySome(tyx1, tys2), TySome(_, tyt2)) => {
                ctx.with_name(tyx1.to_string(), |ctx| tys2.eqv(&tyt2, ctx))
            }
            (TyAll(tyx1, tys2), TyAll(_, tyt2)) => {
                ctx.with_name(tyx1.to_string(), |ctx| tys2.eqv(&tyt2, ctx))
            }
            _ => false,
        }
    }

    fn fix(&mut self, ctx: &mut Context) {
        match self {
            TyVar(s, n) => *n = ctx.name2index(s).unwrap(),
            TyAll(s, ty) => ctx.with_name(s.to_string(), |ctx| ty.fix(ctx)),
            TySome(s, ty) => ctx.with_name(s.to_string(), |ctx| ty.fix(ctx)),

            TyArr(ty1, ty2) => {
                ty1.fix(ctx);
                ty2.fix(ctx);
            }
            TyRecord(fieldtys) => fieldtys.into_iter().for_each(|(_, tyi)| tyi.fix(ctx)),
            TyId(_) | TyString | TyUnit | TyBool | TyFloat | TyNat => {}
        }
    }

    fn format(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyAll(tyx, tyt2) => write!(f, "∀{}. {}", tyx, tyt2),
            _ => self.format_arrow(f),
        }
    }

    fn format_arrow(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyArr(tyt1, tyt2) => {
                tyt1.format_atomic(f)?;
                write!(f, " -> ")?;
                tyt2.format_arrow(f)
            }
            _ => self.format_atomic(f),
        }
    }

    fn format_atomic(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TyVar(s, _) => write!(f, "{}", s),
            TyId(b) => write!(f, "{}", b),
            TyString => write!(f, "String"),
            TyUnit => write!(f, "Unit"),
            TyBool => write!(f, "Bool"),
            TyFloat => write!(f, "Float"),
            TyNat => write!(f, "Nat"),
            TyRecord(fields) => write!(
                f,
                "{{{}}}",
                fields
                    .iter()
                    .map(|(li, tyti)| format!("{}: {}", li, tyti))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TySome(tyx, tyt2) => write!(f, "{{∃{}, {}}}", tyx, tyt2),
            _ => write!(f, "({})", self),
        }
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(f)
    }
}

impl Binding {
    fn shift(&self, d: i32) -> Self {
        match self {
            NameBind => NameBind,
            TyVarBind => TyVarBind,
            TyAbbBind(ty) => TyAbbBind(ty.shift(d)),
            VarBind(ty) => VarBind(ty.shift(d)),
            TmAbbBind(t, None) => TmAbbBind(t.shift(d), None),
            TmAbbBind(t, Some(ty)) => TmAbbBind(t.shift(d), Some(ty.shift(d))),
        }
    }

    fn eval(&self, ctx: &Context) -> Self {
        match &self {
            TmAbbBind(t, ty) => TmAbbBind(t.eval(ctx), ty.clone()),
            _ => self.clone(), // FIXME
        }
    }

    fn fix(&mut self, ctx: &mut Context) {
        match self {
            NameBind => {}
            VarBind(ty) => ty.fix(ctx),
            TyVarBind => {}
            TyAbbBind(ty) => ty.fix(ctx),
            TmAbbBind(t, None) => t.fix(ctx),
            TmAbbBind(t, Some(ty)) => {
                t.fix(ctx);
                ty.fix(ctx);
            }
        }
    }
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NameBind => Ok(()),
            TyVarBind => Ok(()),
            TyAbbBind(ty) => write!(f, " = {}", ty),
            VarBind(ty) => write!(f, ": {}", ty),
            TmAbbBind(t, None) => write!(f, " = {}", t),
            TmAbbBind(t, Some(ty)) => write!(f, " = {}; {}", t, ty),
        }
    }
}

impl Command {
    fn fix(&mut self, ctx: &mut Context) {
        match self {
            Eval(t) => t.fix(ctx),
            Bind(s, b) => {
                b.fix(ctx);
                ctx.add_name(s.to_string())
            }
            SomeBind(s1, s2, t) => {
                t.fix(ctx);
                ctx.add_name(s1.to_string());
                ctx.add_name(s2.to_string());
            }
        }
    }
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Eval(t) => t.fmt(f),
            Bind(x, b) => write!(f, "{}{}", x, b),
            SomeBind(_, _, _) => Ok(()), // TODO
        }
    }
}

mod parser {
    use super::*;

    use nom::{
        branch::alt,
        bytes::complete::tag,
        character::complete::{
            char, digit1, multispace0 as ms0, multispace1 as ms1, none_of, one_of,
        },
        combinator::{all_consuming, map, opt, recognize, verify},
        multi::{many0, many1, separated_list},
        number::complete::recognize_float,
        sequence::{delimited, pair, preceded, terminated, tuple},
        IResult,
    };

    // tokens
    const ID_CHARS: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_";

    fn id(input: &str) -> IResult<&str, Rc<str>> {
        map(
            preceded(ms0, recognize(many1(one_of(ID_CHARS)))),
            |s: &str| s.into(),
        )(input)
    }

    fn ucid(input: &str) -> IResult<&str, Rc<str>> {
        verify(id, |id: &str| id.chars().next().unwrap().is_uppercase())(input)
    }

    fn lcid(input: &str) -> IResult<&str, Rc<str>> {
        verify(id, |id: &str| id.chars().next().unwrap().is_lowercase())(input)
    }

    fn lambda(input: &str) -> IResult<&str, char> {
        preceded(
            ms0,
            alt((map(pair(tag("lambda"), ms1), |_| 'λ'), char('λ'))),
        )(input)
    }

    fn s(s: &'static str) -> Box<dyn Fn(&str) -> IResult<&str, ()>> {
        // let s = s.to_string();
        // box move |input: &str| map(preceded(ms0, tag(&s[..])), |_| {})(input)
        box move |input: &str| map(preceded(ms0, tag(s)), |_| {})(input)
    }

    // parsers
    pub fn parse(input: &str) -> IResult<&str, Vec<Command>> {
        let (input, mut commands) = all_consuming(terminated(
            separated_list(s(";"), command),
            pair(opt(s(";")), ms0),
        ))(input)?;

        let mut ctx = Context::new();
        for cmd in &mut commands {
            cmd.fix(&mut ctx);
        }
        Ok((input, commands))
    }

    fn command(input: &str) -> IResult<&str, Command> {
        alt((
            map(pair(ucid, ty_binder), |(id, b)| Bind(id, b)),
            map(pair(lcid, binder), |(id, b)| Bind(id, b)),
            map(
                tuple((s("{"), ucid, s(","), lcid, s("}"), s("="), term)),
                |(_, uid, _, lid, _, _, t)| SomeBind(uid, lid, t),
            ),
            map(term, |t| Eval(t)),
        ))(input)
    }

    fn binder(input: &str) -> IResult<&str, Binding> {
        alt((
            map(preceded(s(":"), ty), |ty| VarBind(ty)),
            map(preceded(s("="), term), |t| TmAbbBind(t, None)),
        ))(input)
    }

    fn ty_binder(input: &str) -> IResult<&str, Binding> {
        map(preceded(s("="), ty), |ty| TyAbbBind(ty))(input)
    }

    fn ty(input: &str) -> IResult<&str, Ty> {
        alt((
            arrow_type,
            map(tuple((s("∀"), ucid, s("."), ty)), |(_, id, _, t)| {
                TyAll(id, box t)
            }),
        ))(input)
    }

    fn arrow_type(input: &str) -> IResult<&str, Ty> {
        alt((
            map(
                tuple((atomic_type, s("->"), arrow_type)),
                |(ty1, _, ty2)| TyArr(box ty1, box ty2),
            ),
            atomic_type,
        ))(input)
    }

    fn atomic_type(input: &str) -> IResult<&str, Ty> {
        alt((
            delimited(s("("), ty, s(")")),
            map(s("String"), |_| TyString),
            map(s("Unit"), |_| TyUnit),
            map(s("Bool"), |_| TyBool),
            map(s("Nat"), |_| TyNat),
            map(s("Float"), |_| TyFloat),
            map(ucid, |id| TyVar(id, 0)),
            map(
                delimited(s("{"), separated_list(s(","), field_type_element), s("}")),
                |fs| TyRecord(fs),
            ),
            map(
                tuple((s("{"), s("∃"), ucid, s(","), ty, s("}"))),
                |(_, _, id, _, t, _)| TySome(id, box t),
            ),
        ))(input)
    }

    fn field_type_element(input: &str) -> IResult<&str, (Rc<str>, Ty)> {
        map(tuple((lcid, s(":"), ty)), |(id, _, ty)| (id, ty))(input)
    }

    fn term(input: &str) -> IResult<&str, Term> {
        alt((app_term, lambda_term, if_term, let_term))(input)
    }

    fn lambda_term(input: &str) -> IResult<&str, Term> {
        alt((
            map(
                tuple((lambda, lcid, s(":"), ty, s("."), term)),
                |(_, id, _, ty, _, t)| TmAbs(id, ty, box t),
            ),
            map(
                tuple((lambda, s("_"), s(":"), ty, s("."), term)),
                |(_, _, _, ty, _, t)| TmAbs("_".into(), ty, box t),
            ),
            map(tuple((lambda, ucid, s("."), term)), |(_, id, _, t)| {
                TmTAbs(id, box t)
            }),
        ))(input)
    }

    fn if_term(input: &str) -> IResult<&str, Term> {
        map(
            tuple((s("if"), term, s("then"), term, s("else"), term)),
            |(_, t1, _, t2, _, t3)| TmIf(box t1, box t2, box t3),
        )(input)
    }

    fn let_term(input: &str) -> IResult<&str, Term> {
        alt((
            map(
                tuple((s("let"), lcid, s("="), term, s("in"), term)),
                |(_, id, _, t1, _, t2)| TmLet(id, box t1, box t2),
            ),
            map(
                tuple((s("let"), s("_"), s("="), term, s("in"), term)),
                |(_, _, _, t1, _, t2)| TmLet("_".into(), box t1, box t2),
            ),
            map(
                tuple((s("letrec"), lcid, s(":"), ty, s("="), term, s("in"), term)),
                |(_, id, _, ty, _, t1, _, t2)| {
                    TmLet(id.clone(), box TmFix(box TmAbs(id, ty, box t1)), box t2)
                },
            ),
        ))(input)
    }

    fn app_term(input: &str) -> IResult<&str, Term> {
        map(
            pair(app_term_head, separated_list(ms1, app_term_rest)),
            |(head, tail)| tail.iter().fold(head, |t, f| f(t)),
        )(input)
    }

    fn app_term_head(input: &str) -> IResult<&str, Term> {
        alt((
            map(tuple((s("fix"), ms1, path_term)), |(_, _, t)| TmFix(box t)),
            map(
                tuple((s("timesfloat"), ms1, path_term, path_term)),
                |(_, _, t1, t2)| TmTimesfloat(box t1, box t2),
            ),
            map(tuple((s("succ"), ms1, path_term)), |(_, _, t)| {
                TmSucc(box t)
            }),
            map(tuple((s("pred"), ms1, path_term)), |(_, _, t)| {
                TmPred(box t)
            }),
            map(tuple((s("iszero"), ms1, path_term)), |(_, _, t)| {
                TmIsZero(box t)
            }),
            path_term,
        ))(input)
    }

    fn app_term_rest(input: &str) -> IResult<&str, Box<dyn Fn(Term) -> Term>> {
        alt((
            map(
                delimited(s("["), ty, s("]")),
                |ty| -> Box<dyn Fn(Term) -> Term> { box move |t| TmTApp(box t, ty.clone()) },
            ),
            map(path_term, |t1| -> Box<dyn Fn(Term) -> Term> {
                box move |t2| TmApp(box t2, box t1.clone())
            }),
        ))(input)
    }

    fn path_term(input: &str) -> IResult<&str, Term> {
        map(pair(ascribe_term, many0(path_term_rest)), |(head, tail)| {
            tail.iter().fold(head, |t, f| f(t))
        })(input)
    }

    fn path_term_rest(input: &str) -> IResult<&str, Box<dyn Fn(Term) -> Term>> {
        alt((
            map(preceded(s("."), lcid), |id| -> Box<dyn Fn(Term) -> Term> {
                box move |t| TmProj(box t, id.clone())
            }),
            map(
                preceded(s("."), digit1),
                |id| -> Box<dyn Fn(Term) -> Term> {
                    let id: Rc<str> = id.into();
                    box move |t| TmProj(box t, id.clone())
                },
            ),
        ))(input)
    }

    fn ascribe_term(input: &str) -> IResult<&str, Term> {
        alt((
            map(tuple((atomic_term, s("as"), ty)), |(t, _, ty)| {
                TmAscribe(box t, ty)
            }),
            atomic_term,
        ))(input)
    }

    fn atomic_term(input: &str) -> IResult<&str, Term> {
        alt((
            delimited(s("("), term, s(")")),
            map(tuple((s("inert"), s("["), ty, s("]"))), |(_, _, ty, _)| {
                TmInert(ty)
            }),
            map(
                delimited(pair(ms0, char('"')), many0(none_of("\"")), char('"')),
                |cs| TmString(cs.iter().collect::<String>().into()),
            ),
            map(s("unit"), |_| TmUnit),
            map(delimited(s("{"), many0(field_element), s("}")), |fields| {
                TmRecord(fields)
            }),
            map(s("true"), |_| TmTrue),
            map(s("false"), |_| TmFalse),
            map(preceded(ms0, recognize_float), |s: &str| {
                s.parse::<u64>()
                    .map(|v| (0..v).fold(TmZero, |n, _| TmSucc(box n)))
                    .unwrap_or(TmFloat(s.parse().unwrap()))
            }),
            map(
                tuple((s("{"), s("*"), ty, s(","), term, s("}"), s("as"), ty)),
                |(_, _, ty1, _, t, _, _, ty2)| TmPack(ty1, box t, ty2),
            ),
            map(lcid, |id| TmVar(id, 0)),
        ))(input)
    }

    fn field_element(input: &str) -> IResult<&str, (Rc<str>, Term)> {
        map(tuple((lcid, s("="), term)), |(id, _, t)| (id, t))(input)
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let code = "
        CBool = ∀X. X -> X -> X;
        tru = λX. λt:X. λf:X. t;
        fls = λX. λt:X. λf:X. f;

        not = λb:CBool. λX. λt:X. λf:X. b [X] f t;
        not tru [CBool] tru fls;

        and = λb:CBool. λc:CBool. λX. λt:X. λf:X. b [X] (c [X] t f) f;
        and tru tru [CBool] tru fls;
        and tru fls [CBool] tru fls;
        and tru fls [CBool];

        id = λX. λx:X. x;
        not;
        id [CBool] not;

        CNat = ∀X. (X -> X) -> X -> X;
        c0 = λX. λs:X->X. λz:X. z;
        c1 = λX. λs:X->X. λz:X. s z;
        c2 = λX. λs:X->X. λz:X. s (s z);

        csucc = λn:CNat. λX. λs:X->X. λz:X. s (n [X] s z);
        csucc c0;
    ";
    let (_, cmds) = parser::parse(code)?;

    // eval loop
    let mut ctx = Context::new();
    for cmd in cmds {
        println!("> {}", cmd);

        match cmd {
            Eval(t) => {
                let t = t.eval(&ctx);
                let ty = t.ty(&mut ctx);
                println!("{}: {}", t, ty);
            }
            Bind(x, bind) => {
                let bind = bind.eval(&ctx);
                println!("{}{}", x, bind);
                ctx.add_binding(x.to_string(), bind);
            }
            _ => panic!("Invalid Command: {:?}", cmd),
        }
    }

    Ok(())
}
