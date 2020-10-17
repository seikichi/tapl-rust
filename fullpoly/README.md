# fullpolly

## Example

```sh
% cat test.f
double = λX. λf:X->X. λa:X. f (f a);
double [Nat] (λx:Nat. succ (succ x)) 3;

let {X, x} = {*Nat, {a = 0, f = λx:Nat. (succ x)}} as {∃X, {a: X, f: X->X}} in (x.f x.a);

counter = {*Nat, {new = 1, get = λi:Nat. i, inc = λi:Nat. (succ i)}}
  as {∃Counter, {new: Counter, get: Counter -> Nat, inc: Counter->Counter}};
let {C, c} = counter in c.get (c.inc c.new);

Counter = {∃X, {state: X, methods: {get: X->Nat, inc: X->X}}};
c = {*Nat, {state = 5, methods = {get = λx:Nat. x, inc = λx:Nat. (succ x)}}} as Counter;
let {X, body} = c in body.methods.get(body.state);
```

```
% cargo run -- test.f
> double = λX. λf:X->X. λa:X. f (f a)
> double [Nat] (λx:Nat. (succ (succ x))) 3
7: Nat

> let {X, x} = {*Nat, {a = 0, f = λx:Nat. (succ x)}} as {∃X, {a: X, f: X->X}} in x.f x.a
1: Nat

> counter = {*Nat, {new = 1, get = λi:Nat. i, inc = λi:Nat. (succ i)}} as {∃Counter, {new: Counter, get: Counter->Nat, inc: Counter->Counter}}
> let {C, c} = counter in c.get (c.inc c.new)
2: Nat

> Counter = {∃X, {state: X, methods: {get: X->Nat, inc: X->X}}}
> c = {*Nat, {state = 5, methods = {get = λx:Nat. x, inc = λx:Nat. (succ x)}}} as Counter
> let {X, body} = c in (body.methods).get body.state
5: Nat
```
