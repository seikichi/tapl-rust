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

s = λ o: <some: Nat, none: Unit>. case o of <some = n> => succ (n) | <none = u> => 0;
o1 = <some = 10> as <some: Nat, none: Unit>;
o2 = <none = unit> as <some: Nat, none: Unit>;
s o1;
s o2
