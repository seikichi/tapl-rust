# fullref

```sh
% cat test.f
plus = fix (λ f: Nat -> Nat -> Nat. λ m: Nat. λ n: Nat. if iszero m then n else succ (f (pred m) n));
times = fix (λ f: Nat -> Nat -> Nat. λ m: Nat. λ n: Nat. if iszero m then 0 else plus n (f (pred m) n));
factorial = fix (λ f: Nat -> Nat. λ m: Nat. if iszero m then 1 else times m (f (pred m)));
factorial 4;

counter = λ c: Nat. let v = ref c in {inc=λ u: Unit. (v := succ (!v); !v), dec=λ u: Unit. (v := pred (!v); !v)};
c1 = counter 10;
c2 = counter 10;
c1.inc unit;
c1.inc unit;
c1.dec unit;
c1.inc unit;
c2.dec unit;

% cargo run -- test.f
> plus = λ m: Nat. λ n: Nat. if iszero m then n else (succ ((fix λ f: Nat -> Nat -> Nat. λ m': Nat. λ n': Nat. if iszero m' then n' else (succ (f (pred m') n'))) (pred m) n))
> times = λ m: Nat. λ n: Nat. if iszero m then 0 else plus n ((fix λ f: Nat -> Nat -> Nat. λ m': Nat. λ n': Nat. if iszero m' then 0 else plus n' (f (pred m') n')) (pred m) n)
> factorial = λ m: Nat. if iszero m then 1 else times m ((fix λ f: Nat -> Nat. λ m': Nat. if iszero m' then 1 else times m' (f (pred m'))) (pred m))
> factorial 4
24 : Nat
> counter = λ c: Nat. let v = ref c in {inc = λ u: Unit. (λ _: Unit. !v) (v := (succ (!v))), dec = λ u: Unit. (λ _: Unit. !v) (v := pred (!v))}
> c1 = {inc = λ u: Unit. (λ _: Unit. !<loc #0>) (<loc #0> := (succ (!<loc #0>))), dec = λ u: Unit. (λ _: Unit. !<loc #0>) (<loc #0> := pred (!<loc #0>))}
> c2 = {inc = λ u: Unit. (λ _: Unit. !<loc #1>) (<loc #1> := (succ (!<loc #1>))), dec = λ u: Unit. (λ _: Unit. !<loc #1>) (<loc #1> := pred (!<loc #1>))}
> c1.inc unit
11 : Nat
> c1.inc unit
12 : Nat
> c1.dec unit
11 : Nat
> c1.inc unit
12 : Nat
> c2.dec unit
9 : Nat
```
