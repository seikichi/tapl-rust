letrec plus: Nat -> Nat -> Nat =
    λ m: Nat. λ n: Nat.
        if iszero m then n else succ (plus (pred m) n) in
letrec times: Nat -> Nat -> Nat =
    λ m: Nat. λ n: Nat.
        if iszero m then 0 else plus n (times (pred m) n) in
letrec factorial: Nat -> Nat =
    λ m: Nat.
        if iszero m then 1 else times m (factorial (pred m)) in
    factorial 4;

letrec plus: Nat -> Nat -> Nat = λ m: Nat. λ n: Nat. if iszero m then n else succ (plus (pred m) n) in
letrec times: Nat -> Nat -> Nat = λ m: Nat. λ n: Nat. if iszero m then 0 else plus n (times (pred m) n) in
letrec factorial: Nat -> Nat = λ m: Nat. if iszero m then 1 else times m (factorial (pred m)) in factorial 4;

counter = λ c: Nat. let v = ref c in {inc=λ u: Unit. (v := succ (!v); !v), dec=λ u: Unit. (v := pred (!v); !v)};
c = counter 10;
c.inc unit;
c.inc unit;
c.dec unit;
c.inc unit;
