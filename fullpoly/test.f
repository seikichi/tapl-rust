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

double = λX. λf:X->X. λa:X. f (f a);
double [Nat] (λx:Nat. succ (succ x)) 3;

let {X, x} = {*Nat, {a = 0, f = λx:Nat. (succ x)}} as {∃X, {a: X, f: X->Nat}} in (x.f x.a);

counter = {*Nat, {new = 1, get = λi:Nat. i, inc = λi:Nat. (succ i)}}
  as {∃Counter, {new: Counter, get: Counter -> Nat, inc: Counter->Counter}};
let {C, c} = counter in c.get (c.inc c.new);

Counter = {∃X, {state: X, methods: {get: X->Nat, inc: X->X}}};
c = {*Nat, {state = 5, methods = {get = λx:Nat. x, inc = λx:Nat. (succ x)}}} as Counter;
let {X, body} = c in body.methods.get(body.state);

pair = λX. λY. λx:X. λy:Y. (λR. λp:X->Y->R. p x y);
fst = λX. λY. λp:(∀R. (X->Y->R)->R). p [X] (λx:X. λy:Y. x);
snd = λX. λY. λp:(∀R. (X->Y->R)->R). p [Y] (λx:X. λy:Y. y);
p1 = pair [Nat] [Bool] 1 true;
fst [Nat] [Bool] p1;
snd [Nat] [Bool] p1;
