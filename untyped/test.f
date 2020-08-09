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

iszro = λ m. m (λ x. fls) tru;
plus = λ m. λ n. λ s. λ z. m s (n s z);

zz = pair zero zero;
ss = λ p. pair (snd p) (plus one (snd p));
prd = λ m. fst (m ss zz);

equal = λ m. λ n. and (iszro (m prd n)) (iszro (n prd m));

equal (plus two two) four;
equal (plus two two) three;
