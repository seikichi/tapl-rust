y: Bool;
λ x:Bool. x;
(λ x:Bool->Bool. if x false then true else false) (λ x:Bool. if x then false else true);
(λ x:Bool->Bool->Bool. x true false) (λ x:Bool. λ y:Bool. if x then y else true)
