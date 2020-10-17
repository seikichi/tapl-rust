"hello";
unit;
let x = true in x;
timesfloat 2.0 3.14159;
λx:Bool. x;
(λx: Bool->Bool. if x false then true else false) (λx:Bool. if x then false else true);
λx:Nat. succ x;
(λx:Nat. succ (succ x)) (succ 0);

T = Nat -> Nat;
λf:T. λx:Nat. f (f x);

λX. λx:X. x;
(λX. λx:X. x) [∀X.X->X];

{*∀Y.Y, λx:(∀Y.Y). x} as {∃X, X->X};

{x=true, y=false};
{x=true, y=false}.x;
{true, false};
{true, false}.1;

{*Nat, {c=0, f=λx:Nat. succ x}} as {∃X, {c: X, f: X->Nat}};
let {X, x} = {*Nat, {c=0, f=λx:Nat. succ x}} as {∃X, {c: X, f: X->Nat}} in x.f x.c;
