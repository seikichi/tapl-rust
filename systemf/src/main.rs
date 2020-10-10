// #![feature(box_syntax, box_patterns)]

use std::env;
use std::fmt;
use std::fs;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    TyVar(usize),
    TyArr(Rc<Ty>, Rc<Ty>),
    TyAll(Rc<str>, Rc<Ty>),
    TySome(Rc<str>, Rc<Ty>),
}

#[derive(Debug, Clone)]
pub enum Term {
    TmVar(usize),
    TmAbs(Rc<str>, Ty, Rc<Term>),
    TmApp(Rc<Term>, Rc<Term>),
    TmTAbs(Rc<str>, Rc<Term>),
    TmTApp(Rc<Term>, Ty),
    TmPack(Ty, Rc<Term>, Ty),
    TmUnpack(Rc<str>, Rc<str>, Rc<Term>, Rc<Term>),
}

#[derive(Clone, Debug)]
pub enum Binding {
    NameBind,
    VarBind(Ty),
    TyVarBind,
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

// #[derive(Clone, Debug)]
// pub struct Context {
//     bindings: Vec<(String, Binding)>,
// }

// impl Context {
//     fn new() -> Self {
//         Self { bindings: vec![] }
//     }

//     fn add_binding(&mut self, x: String, bind: Binding) {
//         self.bindings.push((x, bind));
//     }

//     fn add_name(&mut self, x: String) {
//         self.add_binding(x, NameBind);
//     }

//     fn with_binding<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, bind: Binding, f: F) -> R {
//         self.bindings.push((x, bind));
//         let result = f(self);
//         self.bindings.pop();
//         result
//     }

//     fn with_name<R, F: FnOnce(&mut Self) -> R>(&mut self, x: String, f: F) -> R {
//         self.with_binding(x, NameBind, f)
//     }

//     fn index2name(&self, x: usize) -> Option<&String> {
//         if self.bindings.len() <= x {
//             return None;
//         }
//         self.bindings
//             .get(self.bindings.len() - x - 1)
//             .map(|(s, _)| s)
//     }

//     fn name2index(&self, x: &str) -> Option<usize> {
//         self.bindings.iter().rev().position(|(y, _)| y == x)
//     }

//     fn get_binding(&self, i: usize) -> Binding {
//         let bind = &self.bindings[self.bindings.len() - i - 1].1;
//         bind.shift(i as i32 + 1)
//     }

//     fn get_type(&self, i: usize) -> Ty {
//         match self.get_binding(i) {
//             VarBind(ty) => ty,
//             TmAbbBind(_, Some(ty)) => ty,
//             _ => panic!("Wrong kind of binding for variable"),
//         }
//     }

//     fn with_fresh_name<R, F: FnOnce(&mut Self, String) -> R>(&mut self, x: &str, f: F) -> R {
//         let mut name: String = x.into();
//         while self.is_name_bound(&name) {
//             name.push_str("'");
//         }
//         self.with_name(name.clone(), move |ctx| f(ctx, name))
//     }

//     fn is_name_bound(&self, x: &str) -> bool {
//         self.bindings.iter().rev().any(|(s, _)| s == x)
//     }
// }

impl Term {
    fn map<F: Copy + Fn(i32, usize) -> Self, TF: Copy + Fn(i32, &Ty) -> Ty>(
        &self,
        c: i32,
        onvar: F,
        ontype: TF,
    ) -> Self {
        match &self {
            TmVar(x) => onvar(c, *x),
            TmAbs(x, ty1, t2) => TmAbs(x.clone(), ty1.clone(), t2.map(c + 1, onvar, ontype).into()),
            TmApp(t1, t2) => TmApp(
                t1.map(c, onvar, ontype).into(),
                t2.map(c, onvar, ontype).into(),
            ),
            TmTAbs(tyx, t2) => TmTAbs(tyx.clone(), t2.map(c + 1, onvar, ontype).into()),
            TmTApp(t1, ty2) => TmTApp(t1.map(c, onvar, ontype).into(), ontype(c, ty2)),
            TmPack(ty1, t2, ty3) => TmPack(
                ontype(c, ty1),
                t2.map(c, onvar, ontype).into(),
                ontype(c, ty3),
            ),
            TmUnpack(tyx, x, t1, t2) => TmUnpack(
                tyx.clone(),
                x.clone(),
                t1.map(c, onvar, ontype).into(),
                t2.map(c + 2, onvar, ontype).into(),
            ),
        }
    }

    fn shift_above(&self, d: i32, c: i32) -> Self {
        self.map(
            c,
            |c, x| {
                if x as i32 >= c {
                    TmVar((x as i32 + d) as usize)
                } else {
                    TmVar(x)
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
            |j, x| if x as i32 == j { s.shift(j) } else { TmVar(x) },
            |_, ty| ty.clone(),
        )
    }

    fn subst_top(&self, s: &Self) -> Self {
        self.subst(0, &s.shift(1)).shift(-1)
    }

    fn ty_subst(&self, j: i32, ty: &Ty) -> Self {
        self.map(j, |_, x| TmVar(x), |j, ty2| ty.subst(j, ty2))
    }

    fn ty_subst_top(&self, ty: &Ty) -> Self {
        self.ty_subst(0, &ty.shift(1)).shift(-1)
    }

    //     fn is_numeric_val(&self, ctx: &Context) -> bool {
    //         match self {
    //             TmZero => true,
    //             TmSucc(t1) => t1.is_numeric_val(ctx),
    //             _ => false,
    //         }
    //     }

    //     fn is_val(&self, ctx: &Context) -> bool {
    //         match self {
    //             TmTrue | TmFalse | TmAbs(_, _, _) | TmUnit | TmString(_) | TmFloat(_) | TmLoc(_) => {
    //                 true
    //             }
    //             TmTag(_, t1, _) if t1.is_val(ctx) => true,
    //             TmRecord(fields) => fields.iter().all(|(_, ti)| ti.is_val(ctx)),
    //             _ if self.is_numeric_val(ctx) => true,
    //             _ => false,
    //         }
    //     }

    //     fn eval1(&self, ctx: &Context, store: &mut Store) -> Option<Self> {
    //         match self {
    //             TmApp(box TmAbs(_, _, t12), v2) if v2.is_val(ctx) => Some(t12.subst_top(v2)),
    //             TmApp(v1, t2) if v1.is_val(ctx) => Some(TmApp(v1.clone(), box t2.eval1(ctx, store)?)),
    //             TmApp(t1, t2) => Some(TmApp(box t1.eval1(ctx, store)?, t2.clone())),
    //             TmIf(box TmTrue, t2, _) => Some((**t2).clone()),
    //             TmIf(box TmFalse, _, t3) => Some((**t3).clone()),
    //             TmIf(t1, t2, t3) => Some(TmIf(box t1.eval1(ctx, store)?, t2.clone(), t3.clone())),
    //             // Nat
    //             TmSucc(t1) => Some(TmSucc(box t1.eval1(ctx, store)?)),
    //             TmPred(box TmZero) => Some(TmZero),
    //             TmPred(box TmSucc(nv1)) if nv1.is_numeric_val(ctx) => Some((**nv1).clone()),
    //             TmPred(t1) => Some(TmPred(box t1.eval1(ctx, store)?)),
    //             TmIsZero(box TmZero) => Some(TmTrue),
    //             TmIsZero(box TmSucc(nv1)) if nv1.is_numeric_val(ctx) => Some(TmFalse),
    //             TmIsZero(t1) => Some(TmIsZero(box t1.eval1(ctx, store)?)),
    //             // Extension
    //             TmTimesFloat(box TmFloat(f1), box TmFloat(f2)) => Some(TmFloat(*f1 * *f2)),
    //             TmTimesFloat(box TmFloat(f1), t2) => {
    //                 Some(TmTimesFloat(box TmFloat(*f1), box t2.eval1(ctx, store)?))
    //             }
    //             TmTimesFloat(t1, t2) => Some(TmTimesFloat(box t1.eval1(ctx, store)?, (*t2).clone())),
    //             TmAscribe(v1, _) if v1.is_val(ctx) => Some((**v1).clone()),
    //             TmAscribe(t1, ty) => Some(TmAscribe(box t1.eval1(ctx, store)?, ty.clone())),
    //             TmLet(_, v1, t2) if v1.is_val(ctx) => Some(t2.subst_top(v1)),
    //             TmLet(x, t1, t2) => Some(TmLet(x.clone(), box t1.eval1(ctx, store)?, t2.clone())),
    //             TmFix(box TmAbs(_, _, t12)) => Some(t12.subst_top(self)),
    //             TmFix(t1) if !t1.is_val(ctx) => Some(TmFix(box t1.eval1(ctx, store)?)),
    //             TmVar(n) => match ctx.get_binding(*n) {
    //                 TmAbbBind(t, _) => Some(t.clone()),
    //                 _ => None,
    //             },
    //             // Ref
    //             TmRef(box t1) if t1.is_val(ctx) => {
    //                 let l = store.extend(t1.clone());
    //                 Some(TmLoc(l))
    //             }
    //             TmRef(t1) => Some(TmRef(box t1.eval1(ctx, store)?)),
    //             TmDeref(box TmLoc(l)) => Some(store.lookup(*l).clone()),
    //             TmDeref(box t1) if !t1.is_val(ctx) => Some(TmDeref(box t1.eval1(ctx, store)?)),
    //             TmAssign(box TmLoc(l), box v2) if v2.is_val(ctx) => {
    //                 store.update(*l, v2.clone());
    //                 Some(TmUnit)
    //             }
    //             TmAssign(v1, t2) if v1.is_val(ctx) => {
    //                 Some(TmAssign(v1.clone(), box t2.eval1(ctx, store)?))
    //             }
    //             TmAssign(t1, t2) => Some(TmAssign(box t1.eval1(ctx, store)?, t2.clone())),
    //             // Record
    //             TmRecord(fields) => {
    //                 let mut nfields = vec![];
    //                 let mut all_value = true;

    //                 for (li, ti) in fields {
    //                     if all_value && !ti.is_val(ctx) {
    //                         all_value = false;
    //                         nfields.push((li.clone(), ti.eval1(ctx, store)?));
    //                     } else {
    //                         nfields.push((li.clone(), ti.clone()));
    //                     }
    //                 }

    //                 if all_value {
    //                     None
    //                 } else {
    //                     Some(TmRecord(nfields))
    //                 }
    //             }
    //             TmProj(box TmRecord(fields), l) if fields.iter().all(|(_, ti)| ti.is_val(ctx)) => {
    //                 fields
    //                     .iter()
    //                     .find(|(li, _)| li == l)
    //                     .map(|(_, ti)| ti.clone())
    //             }
    //             TmProj(t1, l) => Some(TmProj(box t1.eval1(ctx, store)?, l.clone())),
    //             // Variant
    //             TmTag(l, t1, ty) => Some(TmTag(l.clone(), box t1.eval1(ctx, store)?, ty.clone())),
    //             TmCase(box TmTag(li, v11, _), branches) if v11.is_val(ctx) => {
    //                 let (_, body) = branches.iter().find(|(l, _)| l == li).map(|(_, v)| v)?;
    //                 Some(body.subst_top(v11))
    //             }
    //             TmCase(t1, branches) => Some(TmCase(box t1.eval1(ctx, store)?, branches.clone())),
    //             // Other
    //             _ => None,
    //         }
    //     }

    //     fn eval(&self, ctx: &Context, store: &mut Store) -> Self {
    //         let mut t = self.clone();
    //         while let Some(n) = t.eval1(ctx, store) {
    //             t = n;
    //         }
    //         t
    //     }

    //     // fn eval_by_big_step(&self, ctx: &Context) -> Self {
    //     //     match self {
    //     //         TmApp(t1, t2) => {
    //     //             let t1 = t1.eval(ctx);
    //     //             let t2 = t2.eval(ctx);
    //     //             if let TmAbs(_, _, t12) = &t1 {
    //     //                 if t2.is_val(ctx) {
    //     //                     return t12.subst_top(&t2);
    //     //                 }
    //     //             }
    //     //             TmApp(box t1, box t2)
    //     //         }
    //     //         TmIf(t1, t2, t3) => {
    //     //             if let TmTrue = t1.eval(ctx) {
    //     //                 t2.eval(ctx)
    //     //             } else {
    //     //                 t3.eval(ctx)
    //     //             }
    //     //         }
    //     //         _ => (*self).clone(),
    //     //     }
    //     // }

    //     fn ty(&self, ctx: &mut Context) -> Ty {
    //         match self {
    //             TmVar(i) => ctx.get_type(*i).clone(),
    //             TmAbs(x, ty1, t2) => ctx.with_binding(x.clone(), VarBind(ty1.clone()), |mut ctx| {
    //                 TyArr(box ty1.clone(), box t2.ty(&mut ctx))
    //             }),
    //             TmApp(t1, t2) => {
    //                 let ty1 = t1.ty(ctx);
    //                 let ty2 = t2.ty(ctx);
    //                 match ty1 {
    //                     TyArr(ty11, ty12) => {
    //                         if ty2 == *ty11 {
    //                             return *ty12;
    //                         }
    //                         panic!("parameter type mismatch: {}, {}", ty2, *ty11);
    //                     }
    //                     _ => panic!("arrow type expected: {}", ty1),
    //                 }
    //             }
    //             TmTrue | TmFalse => TyBool,
    //             TmIf(t1, t2, t3) => {
    //                 if t1.ty(ctx) == TyBool {
    //                     let ty2 = t2.ty(ctx);
    //                     if ty2 == t3.ty(ctx) {
    //                         return ty2;
    //                     }
    //                     panic!("arms of conditional have different types");
    //                 }
    //                 panic!("guard of conditional not a boolean");
    //             }
    //             // Unit
    //             TmUnit => TyUnit,
    //             // String
    //             TmString(_) => TyString,
    //             // Float
    //             TmFloat(_) => TyFloat,
    //             TmTimesFloat(t1, t2) => {
    //                 if let TyFloat = t1.ty(ctx) {
    //                     if let TyFloat = t2.ty(ctx) {
    //                         return TyFloat;
    //                     }
    //                 }
    //                 panic!("argument of timesfloat is not a number");
    //             }
    //             // Nat
    //             TmZero => TyNat,
    //             TmSucc(t1) => {
    //                 if let TyNat = t1.ty(ctx) {
    //                     return TyNat;
    //                 }
    //                 panic!("argument of succ is not a number");
    //             }
    //             TmPred(t1) => {
    //                 if let TyNat = t1.ty(ctx) {
    //                     return TyNat;
    //                 }
    //                 panic!("argument of succ is not a number");
    //             }
    //             TmIsZero(t1) => {
    //                 if let TyNat = t1.ty(ctx) {
    //                     return TyBool;
    //                 }
    //                 panic!("argument of succ is not a number");
    //             }
    //             // Extension
    //             TmAscribe(t1, ty1) => {
    //                 if t1.ty(ctx) == *ty1 {
    //                     return ty1.clone();
    //                 }
    //                 panic!("body of as-term does not have the expected type");
    //             }
    //             TmLet(x, t1, t2) => {
    //                 let ty1 = t1.ty(ctx);
    //                 ctx.with_binding(x.clone(), VarBind(ty1), |ctx| t2.ty(ctx))
    //             }
    //             TmFix(t1) => {
    //                 if let TyArr(box ty11, box ty12) = t1.ty(ctx) {
    //                     if ty11 == ty12 {
    //                         return ty12.clone();
    //                     }
    //                     panic!("result of body not compatible");
    //                 }
    //                 panic!("arrow type expected");
    //             }
    //             // Assign
    //             TmRef(t1) => TyRef(box t1.ty(ctx)),
    //             TmLoc(_) => panic!("locations are not supposed to occur in source programs!"),
    //             TmDeref(t1) => {
    //                 if let TyRef(box ty1) = t1.ty(ctx) {
    //                     return ty1.clone();
    //                 }
    //                 panic!("argument of ! is not a Ref");
    //             }
    //             TmAssign(t1, t2) => {
    //                 if let TyRef(box ty1) = t1.ty(ctx) {
    //                     if ty1 == t2.ty(ctx) {
    //                         return TyUnit;
    //                     }
    //                     panic!("arguments of := are incompatible");
    //                 }
    //                 panic!("arguments of ! is not a Ref");
    //             }
    //             // Record
    //             TmRecord(fields) => TyRecord(
    //                 fields
    //                     .iter()
    //                     .map(|(li, ti)| (li.clone(), ti.ty(ctx)))
    //                     .collect(),
    //             ),
    //             TmProj(t1, l) => {
    //                 if let TyRecord(fields) = t1.ty(ctx) {
    //                     if let Some((_, tyi)) = fields.iter().find(|(li, _)| li == l) {
    //                         return tyi.clone();
    //                     }
    //                     panic!("label {} not found", l);
    //                 }
    //                 panic!("Expected record type");
    //             }
    //             // Variant
    //             TmTag(li, ti, ty) => {
    //                 if let TyVariant(field_types) = ty {
    //                     if let Some(expected_ty) =
    //                         field_types.iter().find(|(l, _)| l == li).map(|(_, ty)| ty)
    //                     {
    //                         if &ti.ty(ctx) == expected_ty {
    //                             return ty.clone();
    //                         }
    //                         panic!("field does not have expected type");
    //                     }
    //                     panic!("label not found");
    //                 }
    //                 panic!("Annotation is not a variant type");
    //             }
    //             TmCase(t, cases) => {
    //                 if let TyVariant(field_types) = t.ty(ctx) {
    //                     let case_types = cases
    //                         .iter()
    //                         .map(|(li, (xi, ti))| -> Ty {
    //                             let ty = field_types
    //                                 .iter()
    //                                 .find(|(l, _)| l == li)
    //                                 .map(|(_, ty)| ty)
    //                                 .unwrap();
    //                             ctx.with_binding(xi.clone(), VarBind(ty.clone()), |ctx| ti.ty(ctx))
    //                         })
    //                         .collect::<Vec<_>>();
    //                     if !&case_types.windows(2).all(|tys| tys[0] == tys[1]) {
    //                         panic!("same type expected");
    //                     }
    //                     return case_types[0].clone();
    //                 }
    //                 panic!("Expected variant type");
    //             }
    //         }
    //     }

    //     fn format(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //         match self {
    //             TmAbs(x, ty, t1) => ctx.with_fresh_name(x, |mut ctx, x| {
    //                 write!(f, "λ {}: {}. ", x, ty)?;
    //                 t1.format(&mut ctx, f)
    //             }),
    //             TmIf(t1, t2, t3) => {
    //                 write!(f, "if ")?;
    //                 t1.format(ctx, f)?;
    //                 write!(f, " then ")?;
    //                 t2.format(ctx, f)?;
    //                 write!(f, " else ")?;
    //                 t3.format(ctx, f)
    //             }
    //             TmLet(x, t1, t2) => {
    //                 write!(f, "let {} = ", x)?;
    //                 t1.format(ctx, f)?;
    //                 write!(f, " in ")?;
    //                 ctx.with_name(x.clone(), |ctx| t2.format(ctx, f))
    //             }
    //             TmFix(t1) => {
    //                 write!(f, "fix ")?;
    //                 t1.format(ctx, f)
    //             }
    //             TmCase(t, cases) => {
    //                 write!(f, "case ")?;
    //                 t.format(ctx, f)?;
    //                 write!(f, " of")?;

    //                 let (l0, (x0, t0)) = &cases[0];
    //                 write!(f, "<{} = {}> => ", l0, x0)?;
    //                 t0.format(ctx, f)?;

    //                 for (li, (xi, ti)) in &cases[1..] {
    //                     write!(f, " | ")?;
    //                     write!(f, "<{} = {}> => ", li, xi)?;
    //                     ti.format(ctx, f)?;
    //                 }

    //                 write!(f, "")
    //             }
    //             TmAssign(t1, t2) => {
    //                 t1.format_app_term(ctx, f)?;
    //                 write!(f, " := ")?;
    //                 t2.format_app_term(ctx, f)
    //             }
    //             _ => self.format_app_term(ctx, f),
    //         }
    //     }

    //     fn format_app_term(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //         match self {
    //             TmApp(t1, t2) => {
    //                 t1.format_app_term(ctx, f)?;
    //                 write!(f, " ")?;
    //                 t2.format_atomic_term(ctx, f)
    //             }
    //             // Nat
    //             TmPred(t1) => {
    //                 write!(f, "pred ")?;
    //                 t1.format_atomic_term(ctx, f)
    //             }
    //             TmIsZero(t1) => {
    //                 write!(f, "iszero ")?;
    //                 t1.format_atomic_term(ctx, f)
    //             }
    //             // Float
    //             TmTimesFloat(t1, t2) => {
    //                 write!(f, "timesfloat ")?;
    //                 t1.format_atomic_term(ctx, f)?;
    //                 write!(f, " ")?;
    //                 t2.format_atomic_term(ctx, f)
    //             }
    //             // Ref
    //             TmRef(t1) => {
    //                 write!(f, "ref ")?;
    //                 t1.format_atomic_term(ctx, f)
    //             }
    //             TmDeref(t1) => {
    //                 write!(f, "!")?;
    //                 t1.format_atomic_term(ctx, f)
    //             }
    //             // Variant
    //             TmTag(l, t, ty) => {
    //                 write!(f, "<{} = ", l)?;
    //                 t.format(ctx, f)?;
    //                 write!(f, "> as ")?;
    //                 ty.format(ctx, f)
    //             }
    //             _ => self.format_path_term(ctx, f),
    //         }
    //     }

    //     fn format_path_term(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //         match self {
    //             TmProj(t1, l) => {
    //                 t1.format_atomic_term(ctx, f)?;
    //                 write!(f, ".{}", l)
    //             }
    //             _ => self.format_ascribe_term(ctx, f),
    //         }
    //     }

    //     fn format_ascribe_term(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //         match self {
    //             TmAscribe(t1, ty1) => {
    //                 t1.format_app_term(ctx, f)?;
    //                 write!(f, " as ")?;
    //                 ty1.format(ctx, f)
    //             }
    //             _ => self.format_atomic_term(ctx, f),
    //         }
    //     }

    //     fn format_atomic_term(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //         match self {
    //             TmVar(x) => write!(
    //                 f,
    //                 "{}",
    //                 ctx.index2name(*x).unwrap_or(&format!("<context #{}>", x))
    //             ),
    //             TmTrue => write!(f, "true"),
    //             TmFalse => write!(f, "false"),
    //             TmUnit => write!(f, "unit"),
    //             TmString(s) => write!(f, "\"{}\"", s),
    //             TmFloat(d) => write!(f, "{}", d),
    //             TmZero => write!(f, "0"),
    //             TmSucc(t1) => {
    //                 let mut t = t1;
    //                 let mut n = 1;
    //                 loop {
    //                     match t {
    //                         box TmZero => return write!(f, "{}", n),
    //                         box TmSucc(s) => {
    //                             t = s;
    //                             n += 1;
    //                         }
    //                         _ => {
    //                             return {
    //                                 write!(f, "(succ ")?;
    //                                 t1.format_atomic_term(ctx, f)?;
    //                                 write!(f, ")")
    //                             }
    //                         }
    //                     }
    //                 }
    //             }
    //             TmLoc(l) => write!(f, "<loc #{}>", l),
    //             TmRecord(fields) => {
    //                 write!(f, "{{")?;
    //                 if fields.len() >= 1 {
    //                     write!(f, "{} = ", fields[0].0)?;
    //                     fields[0].1.format(ctx, f)?;
    //                     for (li, ti) in &fields[1..] {
    //                         write!(f, ", {} = ", li)?;
    //                         ti.format(ctx, f)?;
    //                     }
    //                 }
    //                 write!(f, "}}")
    //             }
    //             _ => {
    //                 write!(f, "(")?;
    //                 self.format(ctx, f)?;
    //                 write!(f, ")")
    //             }
    //         }
    //     }

    //     fn display(&self, ctx: &Context) -> TermDisplay {
    //         TermDisplay {
    //             t: self.clone(),
    //             ctx: ctx.clone(),
    //         }
    //     }
}

impl Ty {
    fn map<F: Copy + Fn(i32, usize) -> Self>(&self, c: i32, onvar: F) -> Self {
        match &self {
            TyArr(ty1, ty2) => TyArr(ty1.map(c, onvar).into(), ty2.map(c, onvar).into()),
            TyVar(x) => onvar(c, *x),
            TyAll(tyx, ty2) => TyAll(tyx.clone(), ty2.map(c + 1, onvar).into()),
            TySome(tyx, ty2) => TySome(tyx.clone(), ty2.map(c + 1, onvar).into()),
        }
    }

    fn shift_above(&self, d: i32, c: i32) -> Self {
        self.map(c, |c, x| {
            if x as i32 >= c {
                TyVar((x as i32 + d) as usize)
            } else {
                TyVar(x)
            }
        })
    }

    fn shift(&self, d: i32) -> Self {
        self.shift_above(d, 0)
    }

    fn subst(&self, j: i32, s: &Self) -> Self {
        self.map(j, |j, x| if x as i32 == j { s.shift(j) } else { TyVar(x) })
    }

    fn subst_top(&self, s: &Self) -> Self {
        self.subst(0, &s.shift(1)).shift(-1)
    }

    // fn format(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //     match self {
    //         _ => self.format_arr_ty(ctx, f),
    //     }
    // }

    // fn format_arr_ty(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //     match self {
    //         TyArr(t1, t2) => {
    //             t1.format_atomic_ty(ctx, f)?;
    //             write!(f, " -> ")?;
    //             t2.format_arr_ty(ctx, f)
    //         }
    //         _ => self.format_atomic_ty(ctx, f),
    //     }
    // }

    // fn format_atomic_ty(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //     match self {
    //         TyBool => write!(f, "Bool"),
    //         TyUnit => write!(f, "Unit"),
    //         TyString => write!(f, "String"),
    //         TyFloat => write!(f, "Float"),
    //         TyNat => write!(f, "Nat"),
    //         TyRef(ty) => {
    //             write!(f, "Ref ")?;
    //             ty.format_atomic_ty(ctx, f)
    //         }
    //         TyRecord(fields) => {
    //             write!(f, "{{")?;
    //             if fields.len() >= 1 {
    //                 write!(f, "{}: ", fields[0].0)?;
    //                 fields[0].1.format(ctx, f)?;
    //                 for (li, ti) in &fields[1..] {
    //                     write!(f, ", {}: ", li)?;
    //                     ti.format(ctx, f)?;
    //                 }
    //             }
    //             write!(f, "}}")
    //         }
    //         TyVariant(fields) => {
    //             write!(f, "<")?;
    //             if fields.len() >= 1 {
    //                 write!(f, "{}: ", fields[0].0)?;
    //                 fields[0].1.format(ctx, f)?;
    //                 for (li, ti) in &fields[1..] {
    //                     write!(f, ", {}: ", li)?;
    //                     ti.format(ctx, f)?;
    //                 }
    //             }
    //             write!(f, ">")
    //         }
    //         TyArr(_, _) => {
    //             write!(f, "(")?;
    //             self.format(ctx, f)?;
    //             write!(f, ")")
    //         }
    //     }
    // }
}

// impl Binding {
//     fn check(&self, ctx: &mut Context) -> Self {
//         match self {
//             NameBind => NameBind,
//             VarBind(ty) => VarBind(ty.clone()),
//             TmAbbBind(t, None) => TmAbbBind(t.clone(), Some(t.ty(ctx))),
//             TmAbbBind(t, Some(ty)) if t.ty(ctx) == *ty => TmAbbBind(t.clone(), Some(ty.clone())),
//             TmAbbBind(_, _) => panic!("Type of binding does not match declared type"),
//         }
//     }

//     fn eval(&self, ctx: &Context, store: &mut Store) -> Self {
//         match self {
//             TmAbbBind(t, ty) => TmAbbBind(t.eval(ctx, store), ty.clone()),
//             _ => (*self).clone(),
//         }
//     }

//     fn shift(&self, d: i32) -> Self {
//         match self {
//             NameBind => NameBind,
//             VarBind(ty) => VarBind(ty.clone()),
//             TmAbbBind(t, None) => TmAbbBind(t.shift(d), None),
//             TmAbbBind(t, Some(ty)) => TmAbbBind(t.shift(d), Some(ty.clone())),
//         }
//     }

//     fn display(&self, ctx: &Context) -> BindingDisplay {
//         BindingDisplay {
//             b: self.clone(),
//             ctx: ctx.clone(),
//         }
//     }

//     fn format(&self, ctx: &mut Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             NameBind => Ok(()),
//             VarBind(ty) => write!(f, ": {}", ty),
//             TmAbbBind(t, _) => {
//                 write!(f, "= ")?;
//                 t.format(ctx, f)
//             }
//         }
//     }
// }

// impl fmt::Display for Term {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.format(&mut Context::new(), f)
//     }
// }

// impl fmt::Display for Ty {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.format(&mut Context::new(), f)
//     }
// }

// impl fmt::Display for Binding {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.format(&mut Context::new(), f)
//     }
// }

// struct TermDisplay {
//     t: Term,
//     ctx: Context,
// }

// struct BindingDisplay {
//     b: Binding,
//     ctx: Context,
// }

// impl fmt::Display for TermDisplay {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.t.format(&mut self.ctx.clone(), f)
//     }
// }

// impl fmt::Display for BindingDisplay {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         self.b.format(&mut self.ctx.clone(), f)
//     }
// }

// mod parser {
//     use super::*;

//     use nom::{
//         branch::alt,
//         bytes::complete::tag,
//         character::complete::{
//             alpha1, alphanumeric0, char, digit1, multispace0 as ms0, multispace1 as ms1, none_of,
//         },
//         combinator::{map, not, peek, verify},
//         multi::{many0, separated_list, separated_nonempty_list},
//         number::complete::double,
//         sequence::{delimited, pair, preceded, tuple},
//         IResult,
//     };

//     type ParseResult<T> = Box<dyn Fn(&mut Context) -> T>;

//     pub fn parse(input: &str) -> IResult<&str, Vec<Command>> {
//         map(separated_list(pair(ms0, char(';')), command), |fs| {
//             let mut ctx = Context::new();
//             fs.iter().map(|f| f(&mut ctx)).collect()
//         })(input)
//     }

//     fn command(input: &str) -> IResult<&str, ParseResult<Command>> {
//         alt((
//             map(
//                 pair(preceded(ms0, identifier), binder),
//                 |(id, f)| -> ParseResult<_> {
//                     box move |ctx| {
//                         let result = Bind(id.clone(), f(ctx));
//                         ctx.add_name(id.clone());
//                         result
//                     }
//                 },
//             ),
//             map(term, |f| -> ParseResult<_> { box move |ctx| Eval(f(ctx)) }),
//         ))(input)
//     }

//     fn binder(input: &str) -> IResult<&str, ParseResult<Binding>> {
//         alt((
//             map(
//                 preceded(tuple((ms0, char(':'), ms0)), all_type),
//                 |f| -> ParseResult<_> { box move |ctx| VarBind(f(ctx)) },
//             ),
//             map(
//                 preceded(tuple((ms0, char('='), ms0)), term),
//                 |f| -> ParseResult<_> { box move |ctx| TmAbbBind(f(ctx), None) },
//             ),
//         ))(input)
//     }

//     fn all_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
//         preceded(ms0, arrow_type)(input)
//     }

//     fn atomic_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
//         alt((
//             map(preceded(ms0, tag("Bool")), |_| -> ParseResult<_> {
//                 box |_ctx| TyBool
//             }),
//             map(preceded(ms0, tag("Unit")), |_| -> ParseResult<_> {
//                 box |_ctx| TyUnit
//             }),
//             map(preceded(ms0, tag("String")), |_| -> ParseResult<_> {
//                 box |_ctx| TyString
//             }),
//             map(preceded(ms0, tag("Float")), |_| -> ParseResult<_> {
//                 box |_ctx| TyFloat
//             }),
//             map(preceded(ms0, tag("Nat")), |_| -> ParseResult<_> {
//                 box |_ctx| TyNat
//             }),
//             map(
//                 preceded(
//                     ms0,
//                     delimited(char('{'), field_types, preceded(ms0, char('}'))),
//                 ),
//                 |f| -> ParseResult<_> { box move |ctx| TyRecord(f(ctx)) },
//             ),
//             map(
//                 preceded(
//                     ms0,
//                     delimited(char('<'), field_types, preceded(ms0, char('>'))),
//                 ),
//                 |f| -> ParseResult<_> { box move |ctx| TyVariant(f(ctx)) },
//             ),
//             preceded(
//                 ms0,
//                 delimited(char('('), all_type, preceded(ms0, char(')'))),
//             ),
//         ))(input)
//     }

//     fn field_types(input: &str) -> IResult<&str, ParseResult<Vec<(String, Ty)>>> {
//         map(
//             separated_list(pair(ms0, char(',')), field_type),
//             |fs| -> ParseResult<_> {
//                 box move |ctx| fs.iter().enumerate().map(|(i, f)| f(ctx, i + 1)).collect()
//             },
//         )(input)
//     }

//     type FieldTypeResult = Box<dyn Fn(&mut Context, usize) -> (String, Ty)>;

//     fn field_type(input: &str) -> IResult<&str, FieldTypeResult> {
//         alt((
//             map(
//                 tuple((label, ms0, char(':'), all_type)),
//                 |(l, _, _, f)| -> FieldTypeResult { box move |ctx, _| (l.clone(), f(ctx)) },
//             ),
//             map(all_type, |f| -> FieldTypeResult {
//                 box move |ctx, i| (format!("{}", i), f(ctx))
//             }),
//         ))(input)
//     }
//     fn arrow_type(input: &str) -> IResult<&str, ParseResult<Ty>> {
//         map(
//             separated_nonempty_list(pair(ms0, tag("->")), atomic_type),
//             |fs| {
//                 let mut it = fs.into_iter().rev();
//                 let f = it.next().unwrap();
//                 it.fold(f, |f1, f2| box move |ctx| TyArr(box f2(ctx), box f1(ctx)))
//             },
//         )(input)
//     }

//     pub fn term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         alt((
//             if_term,
//             lambda,
//             let_term,
//             letrec_term,
//             assign,
//             case,
//             app_term,
//         ))(input)
//     }

//     fn case(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, tag("case")),
//                 term,
//                 preceded(ms0, tag("of")),
//                 cases,
//             )),
//             |(_, tf, _, cf)| -> ParseResult<_> { box move |ctx| TmCase(box tf(ctx), cf(ctx)) },
//         )(input)
//     }

//     fn cases(input: &str) -> IResult<&str, ParseResult<Vec<(String, (String, Term))>>> {
//         map(
//             separated_nonempty_list(pair(ms0, char('|')), single_case),
//             |fs| -> ParseResult<_> { box move |ctx| fs.iter().map(|f| f(ctx)).collect() },
//         )(input)
//     }

//     fn single_case(input: &str) -> IResult<&str, ParseResult<(String, (String, Term))>> {
//         map(
//             tuple((
//                 preceded(ms0, char('<')),
//                 label,
//                 preceded(ms0, char('=')),
//                 label,
//                 preceded(ms0, char('>')),
//                 preceded(ms0, tag("=>")),
//                 app_term,
//             )),
//             |(_, l1, _, l2, _, _, ft)| -> ParseResult<_> {
//                 box move |ctx| {
//                     (
//                         l1.clone(),
//                         (l2.clone(), ctx.with_name(l2.clone(), |ctx| ft(ctx))),
//                     )
//                 }
//             },
//         )(input)
//     }

//     fn lambda(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, alt((tag("lambda"), tag("λ")))),
//                 preceded(ms1, identifier),
//                 preceded(ms0, char(':')),
//                 all_type,
//                 preceded(ms0, char('.')),
//                 term,
//             )),
//             |(_, s, _, tyf, _, tf)| -> ParseResult<_> {
//                 box move |ctx| {
//                     ctx.with_name(s.clone(), |mut ctx| {
//                         TmAbs(s.clone(), tyf(&mut ctx), box tf(&mut ctx))
//                     })
//                 }
//             },
//         )(input)
//     }

//     fn assign(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((app_term, preceded(ms0, tag(":=")), app_term)),
//             |(f1, _, f2)| -> ParseResult<_> { box move |ctx| TmAssign(box f1(ctx), box f2(ctx)) },
//         )(input)
//     }

//     fn let_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, tag("let")),
//                 preceded(ms1, identifier),
//                 preceded(ms0, char('=')),
//                 term,
//                 preceded(ms1, tag("in")),
//                 preceded(ms1, term),
//             )),
//             |(_, s, _, f1, _, f2)| -> ParseResult<_> {
//                 box move |ctx| {
//                     let t1 = f1(ctx);
//                     ctx.with_name(s.clone(), |ctx| TmLet(s.clone(), box t1, box f2(ctx)))
//                 }
//             },
//         )(input)
//     }

//     fn letrec_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, tag("letrec")),
//                 preceded(ms1, identifier),
//                 preceded(ms0, char(':')),
//                 preceded(ms0, all_type),
//                 preceded(ms0, char('=')),
//                 term,
//                 preceded(ms1, tag("in")),
//                 preceded(ms1, term),
//             )),
//             |(_, s, _, fty, _, f1, _, f2)| -> ParseResult<_> {
//                 box move |ctx| {
//                     let ty = fty(ctx);
//                     ctx.with_name(s.clone(), |ctx| {
//                         TmLet(
//                             s.clone(),
//                             box TmFix(box TmAbs(s.clone(), ty, box f1(ctx))),
//                             box f2(ctx),
//                         )
//                     })
//                 }
//             },
//         )(input)
//     }

//     fn if_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             tuple((
//                 preceded(ms0, tag("if")),
//                 term,
//                 preceded(ms1, tag("then")),
//                 term,
//                 preceded(ms1, tag("else")),
//                 term,
//             )),
//             |(_, f1, _, f2, _, f3)| -> ParseResult<_> {
//                 box move |ctx| TmIf(box f1(ctx), box f2(ctx), box f3(ctx))
//             },
//         )(input)
//     }

//     fn app_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(separated_nonempty_list(ms1, app_term_1), |fs| {
//             let mut it = fs.into_iter();
//             let f = it.next().unwrap();
//             it.fold(f, |f1, f2| box move |ctx| TmApp(box f1(ctx), box f2(ctx)))
//         })(input)
//     }

//     fn app_term_1(input: &str) -> IResult<&str, ParseResult<Term>> {
//         alt((
//             map(
//                 preceded(pair(ms0, tag("fix")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmFix(box f(ctx)) },
//             ),
//             map(
//                 preceded(pair(ms0, tag("succ")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmSucc(box f(ctx)) },
//             ),
//             map(
//                 preceded(pair(ms0, tag("pred")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmPred(box f(ctx)) },
//             ),
//             map(
//                 preceded(pair(ms0, tag("iszero")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmIsZero(box f(ctx)) },
//             ),
//             map(
//                 tuple((pair(ms0, tag("timesfloat")), path_term, path_term)),
//                 |(_, f1, f2)| -> ParseResult<_> {
//                     box move |ctx| TmTimesFloat(box f1(ctx), box f2(ctx))
//                 },
//             ),
//             map(
//                 preceded(pair(ms0, tag("ref")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmRef(box f(ctx)) },
//             ),
//             map(
//                 preceded(pair(ms0, tag("!")), path_term),
//                 |f| -> ParseResult<_> { box move |ctx| TmDeref(box f(ctx)) },
//             ),
//             path_term,
//         ))(input)
//     }

//     fn path_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(
//             pair(ascribe_term, many0(preceded(pair(ms0, char('.')), label))),
//             |(tf, ls)| -> ParseResult<_> {
//                 box move |ctx| ls.iter().fold(tf(ctx), |t, li| TmProj(box t, li.clone()))
//             },
//         )(input)
//     }

//     fn label(input: &str) -> IResult<&str, String> {
//         preceded(
//             ms0,
//             alt((identifier, map(digit1, |s: &str| s.parse().unwrap()))),
//         )(input)
//     }

//     fn ascribe_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         alt((
//             map(
//                 tuple((atomic_term, ms1, tag("as"), ms1, all_type)),
//                 |(ft, _, _, _, fty)| -> ParseResult<_> {
//                     box move |ctx| TmAscribe(box ft(ctx), fty(ctx))
//                 },
//             ),
//             atomic_term,
//         ))(input)
//     }

//     fn term_seq(input: &str) -> IResult<&str, ParseResult<Term>> {
//         map(separated_nonempty_list(pair(ms0, char(';')), term), |fs| {
//             let mut it = fs.into_iter().rev();
//             let f = it.next().unwrap();
//             it.fold(f, |f1, f2| {
//                 box move |ctx| {
//                     TmApp(
//                         box TmAbs(
//                             "_".into(),
//                             TyUnit,
//                             ctx.with_name("_".into(), |ctx| box f1(ctx)),
//                         ),
//                         box f2(ctx),
//                     )
//                 }
//             })
//         })(input)
//     }

//     fn atomic_term(input: &str) -> IResult<&str, ParseResult<Term>> {
//         preceded(
//             ms0,
//             alt((
//                 map(tag("true"), |_| -> ParseResult<_> { box |_| TmTrue }),
//                 map(tag("false"), |_| -> ParseResult<_> { box |_| TmFalse }),
//                 map(tag("unit"), |_| -> ParseResult<_> { box |_| TmUnit }),
//                 map(identifier, |s| -> ParseResult<_> {
//                     box move |ctx| TmVar(ctx.name2index(&s).expect(&format!("{} not found", s)))
//                 }),
//                 delimited(char('('), term_seq, pair(ms0, char(')'))),
//                 // String
//                 map(string_value, |s: String| -> ParseResult<_> {
//                     box move |_| TmString(s.clone())
//                 }),
//                 // Nat
//                 map(int_value, |n| -> ParseResult<_> {
//                     box move |_| {
//                         let mut result = TmZero;
//                         for _ in 0..n {
//                             result = TmSucc(box result);
//                         }
//                         result
//                     }
//                 }),
//                 map(double, |d| -> ParseResult<_> { box move |_| TmFloat(d) }),
//                 // Record
//                 map(
//                     delimited(char('{'), fields, pair(ms0, char('}'))),
//                     |fs| -> ParseResult<_> { box move |ctx| TmRecord(fs(ctx)) },
//                 ),
//                 // Tag
//                 map(
//                     tuple((
//                         char('<'),
//                         label,
//                         preceded(ms0, char('=')),
//                         term,
//                         preceded(ms0, char('>')),
//                         preceded(ms0, tag("as")),
//                         all_type,
//                     )),
//                     |(_, l, _, ft, _, _, fty)| -> ParseResult<_> {
//                         box move |ctx| TmTag(l.clone(), box ft(ctx), fty(ctx))
//                     },
//                 ),
//             )),
//         )(input)
//     }

//     fn fields(input: &str) -> IResult<&str, ParseResult<Vec<(String, Term)>>> {
//         map(
//             separated_list(pair(ms0, char(',')), field),
//             |fs| -> ParseResult<_> {
//                 box move |ctx| fs.iter().enumerate().map(|(i, f)| f(ctx, i + 1)).collect()
//             },
//         )(input)
//     }

//     type FieldResult = Box<dyn Fn(&mut Context, usize) -> (String, Term)>;

//     fn field(input: &str) -> IResult<&str, FieldResult> {
//         alt((
//             map(
//                 tuple((label, ms0, char('='), term)),
//                 |(l, _, _, f)| -> FieldResult { box move |ctx, _| (l.clone(), f(ctx)) },
//             ),
//             map(term, |f| -> FieldResult {
//                 box move |ctx, i| (format!("{}", i), f(ctx))
//             }),
//         ))(input)
//     }

//     const RESERVED_KEYWORDS: &'static [&'static str] = &[
//         "true", "false", "if", "then", "else", "succ", "pred", "iszero", "let", "in", "fix",
//         "unit", "ref", "case", "of",
//     ];

//     fn identifier(input: &str) -> IResult<&str, String> {
//         verify(
//             map(pair(alpha1, alphanumeric0), |(s1, s2)| {
//                 format!("{}{}", s1, s2)
//             }),
//             |s: &String| !RESERVED_KEYWORDS.iter().any(|x| x == &s),
//         )(input)
//     }

//     fn int_value(input: &str) -> IResult<&str, u32> {
//         map(pair(digit1, not(peek(char('.')))), |(s, _): (&str, _)| {
//             s.parse().unwrap()
//         })(input)
//     }

//     fn string_value(input: &str) -> IResult<&str, String> {
//         map(delimited(char('"'), many0(none_of("\"")), char('"')), |s| {
//             s.iter().collect()
//         })(input)
//     }
// }

// #[test]
// fn test() {
//     let testcases = vec![
//         // Bool,
//         ("true", "true", "Bool"),
//         (
//             "(λ x: Bool -> Bool. if x true then true else false) (λ x: Bool. x)",
//             "true",
//             "Bool",
//         ),
//         (
//             "(λ x: Bool -> Bool -> Bool. x true false) (λ x: Bool. λ y: Bool. true)",
//             "true",
//             "Bool",
//         ),
//         // Unit
//         ("unit", "unit", "Unit"),
//         ("λ x: Bool. unit", "λ x: Bool. unit", "Bool -> Unit"),
//         ("(λ x: Bool. unit) true", "unit", "Unit"),
//         // Seq
//         ("(unit; 42)", "42", "Nat"),
//         (
//             "λ x: Bool. (unit; 42)",
//             "λ x: Bool. (λ _: Unit. 42) unit",
//             "Bool -> Nat",
//         ),
//         // Nat
//         ("(λ x: Nat. succ x) 41", "42", "Nat"),
//         ("(λ x: Nat. if iszero x then 42 else 0) 0", "42", "Nat"),
//         ("(λ x: Nat. if iszero x then 42 else 0) 1", "0", "Nat"),
//         // String
//         (r#""hello""#, r#""hello""#, "String"),
//         (r#"λ x: Bool. "hello""#, r#"λ x: Bool. "hello""#, "Bool -> String"),
//         // Float
//         ("1.2", "1.2", "Float"),
//         ("timesfloat 2.5 2.0", "5", "Float"),
//         ("λ x: Float. timesfloat x 2.0", "λ x: Float. timesfloat x 2", "Float -> Float"),
//         // Let
//         ("let x=true in x", "true", "Bool"),
//         ("let x=0 in let f=λ x: Nat. succ x in f x", "1", "Nat"),
//         // Fix
//         (
//             "(fix (λ f: Nat -> Nat -> Nat. λ m: Nat. λ n: Nat. if iszero m then n else succ (f (pred m) n))) 40 2",
//             "42",
//             "Nat",
//         ),
//         // Letrec
//         (
//             "
//             letrec plus: Nat -> Nat -> Nat =
//               λ m: Nat. λ n: Nat.
//                 if iszero m then n else succ (plus (pred m) n) in
//             letrec times: Nat -> Nat -> Nat =
//               λ m: Nat. λ n: Nat.
//                 if iszero m then 0 else plus n (times (pred m) n) in
//             letrec factorial: Nat -> Nat =
//               λ m: Nat.
//                 if iszero m then 1 else times m (factorial (pred m)) in
//             factorial 5
//             ",
//             "120",
//             "Nat",
//         ),
//         // As
//         ("true as Bool", "true", "Bool"),
//         ("λ x:Bool. x as Bool", "λ x: Bool. x as Bool", "Bool -> Bool"),
//         // Ref
//         ("let r = ref 40 in (r := succ(!r); r := succ(!r); !r)", "42", "Nat"),
//         // TmAbbBind
//         ("x = 41; succ x", "42", "Nat"),
//         ("r = ref 40; r := succ(!r); r := succ(!r); !r", "42", "Nat"),
//         (
//             "
//             z = 0;
//             plus = fix (λ f: Nat -> Nat -> Nat. λ m: Nat. λ n: Nat. if iszero m then n else succ (f (pred m) n));
//             times = fix (λ f: Nat -> Nat -> Nat. λ m: Nat. λ n: Nat. if iszero m then z else plus n (f (pred m) n));
//             times 6 7
//             ",
//             "42",
//             "Nat"
//         ),
//         // Record
//         ("{x=true, y=1}", "{x = true, y = 1}", "{x: Bool, y: Nat}"),
//         ("{x=true, y=1}.x", "true", "Bool"),
//         ("{true, 1}", "{1 = true, 2 = 1}", "{1: Bool, 2: Nat}"),
//         ("{true, 1}.1", "true", "Bool"),
//         ("{1, {2, {3}}}.2.2.1", "3", "Nat"),
//         ("{x = (λ x: Nat. succ x) 0, y = succ 10}", "{x = 1, y = 11}", "{x: Nat, y: Nat}"),
//         ("(λ r: {x: Nat, y: Bool}. r.x) {x = 42, y = true}", "42", "Nat"),
//         // Variant
//         ("λ x: <a: Bool, b: Bool>. x", "λ x: <a: Bool, b: Bool>. x", "<a: Bool, b: Bool> -> <a: Bool, b: Bool>"),
//         ("<x = 10> as <x: Nat, b: Bool>", "<x = 10> as <x: Nat, b: Bool>", "<x: Nat, b: Bool>"),
//         (
//             "(λ o: <some: Nat, none: Unit>. case o of <some = n> => succ (n) | <none = u> => 0) <none = unit> as <some: Nat, none: Unit>",
//             "0",
//             "Nat",
//         ),
//         (
//             "
//             s = λ o: <some: Nat, none: Unit>.
//                   case o of <some = n> => succ (n)
//                           | <none = u> => 0;
//             o = <some = 10> as <some: Nat, none: Unit>;
//             s o;
//             ",
//             "11",
//             "Nat"
//         ),
//         // Other
//         (
//             "
//             counter = λ c: Nat. let v = ref c in {inc=λ u: Unit. (v := succ (!v); !v), dec=λ u: Unit. (v := pred (!v); !v)};
//             c = counter 10;
//             c.inc unit;
//             c.inc unit;
//             c.dec unit;
//             c.inc unit;
//             ",
//             "12",
//             "Nat",
//         ),
//     ];

//     for (input, expect_term, expect_ty) in testcases {
//         let result = parser::parse(input);
//         assert!(result.is_ok(), "{}", input);
//         let (_, commands) = result.unwrap();

//         let mut ctx = Context::new();
//         let mut store = Store::new();
//         let mut result = None;
//         for c in commands {
//             match c {
//                 Command::Eval(t) => result = Some(t.eval(&ctx, &mut store)),
//                 Command::Bind(s, b) => {
//                     let b = b.check(&mut ctx).eval(&ctx, &mut store);
//                     ctx.add_binding(s, b);
//                     store.shift(1)
//                 }
//             }
//         }

//         assert!(result.is_some(), "{}", input);
//         let t = result.unwrap();
//         assert_eq!(expect_term, format!("{}", t), "{}", input);
//         assert_eq!(expect_ty, format!("{}", t.ty(&mut ctx)), "{}", input);
//     }
// }

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // let args: Vec<String> = env::args().collect();
    // let filename = &args[1];
    // let code = fs::read_to_string(filename)?;
    // let (_, commands) = parser::parse(&code).unwrap();

    // let mut ctx = Context::new();
    // let mut store = Store::new();
    // for c in commands {
    //     match c {
    //         Command::Eval(t) => {
    //             println!("> {}", t.display(&ctx));
    //             println!("{} : {}", t.eval(&ctx, &mut store), t.ty(&mut ctx));
    //         }
    //         Command::Bind(s, b) => {
    //             let b = b.check(&mut ctx).eval(&ctx, &mut store);
    //             println!("> {} {}", s, b.display(&ctx));
    //             ctx.add_binding(s, b);
    //             store.shift(1);
    //         }
    //     }
    // }

    Ok(())
}
