tru = λ t. λ f. t;
fls = λ t. λ f. f;
test = λ l. λ m. λ n. l m n;
and = λ b. λ c. b c fls;

pair = λ f. λ s. λ b. b f s;
fst = λ p. p tru;
snd = λ p. p fls;

zero  = λ s. λ z. z;
one   = λ s. λ z. s z;
two   = λ s. λ z. s (s z);
three = λ s. λ z. s (s (s z));
four  = λ s. λ z. s (s (s (s z)));
five  = λ s. λ z. s (s (s (s (s z))));
six   = λ s. λ z. s (s (s (s (s (s z)))));

iszro = λ m. m (λ x. fls) tru;
plus = λ m. λ n. λ s. λ z. m s (n s z);
times = λ m. λ n. λ s. m (n s);

zz = pair zero zero;
ss = λ p. pair (snd p) (plus one (snd p));
prd = λ m. fst (m ss zz);

equal = λ m. λ n. and (iszro (m prd n)) (iszro (n prd m));

equal (plus two two) four;
equal (plus two two) three;

fix = λ f. (λ x. f (λ y. x x y)) (λ x. f (λ y. x x y));
ff = λ f. λ n. test (iszro n) (λ x. one) (λ x. (times n (f (prd n)))) zero;
factorial = fix ff;

equal six (factorial three);
