AttachSpec("2-gen Monster.spec");
AttachSpec("../AxialTools/AxialTools.spec");

A, gen, frob := M3A();
F<al,bt> := BaseRing(A);

assert Determinant(frob) eq -al^2*(3*al - bt - 1)*(3*al^2 + 3*al*bt - bt - 1)*
                                  (3*al^2 + 3*al*bt - 9*al - 2*bt + 4)^3 / ( 2^9*(2*al-1)^5 );
                                  
QQ := Rationals();
/*

So need to check when bt = 3al-1 

and 3*al^2 + 3*al*bt - bt - 1 = 0

and 3*al^2 + 3*al*bt - 9*al - 2*bt + 4 = 0

*/
// Let bt = 3al-1

FF<Al> := FunctionField(QQ);
phi := hom<F->FF | [Al,3*Al-1]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

assert Dimension(Nullspace(frob2)) eq 1;

assert Al/2*(AA.1+AA.2+AA.3) + AA.4 in Nullspace(frob2);

I := ideal<AA | Nullspace(frob2).1>;

B, quo := quo<AA | I>;

assert forall{ i : i in [1..3] | AA.i@quo eq B.i};

// B is a 3C(bt)
assert B.1*B.2 eq (3*Al-1)/2*(B.1+B.2-B.3);

QQ := Rationals();
FF<Al> := FunctionField(QQ);
phi := hom<F->FF | [Al,3*Al-1]>;

// -------------------------------------------------------

// 3*al^2 + 3*al*bt - bt - 1 = 0 implies that
// bt := (1-3*al^2)/(3al-1)
// Assuming that al \neq 1/3

FF<Al> := FunctionField(QQ);
phi := hom<F->FF | [Al,(1-3*Al^2)/(3*Al-1)]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

assert Dimension(Nullspace(frob2)) eq 1;
assert AA.4 in Nullspace(frob2);

I := ideal<AA | AA.4>;

B, quo := quo<AA | I>;
assert forall{ i : i in [1..3] | AA.i@quo eq B.i};

evals, espace, FL := IdentifyFusionLaw(B.1);

// This is a new quotient
assert { e[1] : e in evals} eq {1, Al, (-Al^2 + 1/3)/(Al - 1/3)};

// Check al=1/3

FF<Bt> := FunctionField(QQ);
phi := hom<F->FF | [1/3, Bt]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

assert Determinant(frob2) eq -1/(3*2^8)*Bt*(3*Bt-4)^3;

// So need to check (1/3,4/3)
AA, gen, frob2 := M3A(1/3,4/3);

assert Dimension(NullSpace(frob2)) eq 3;

so, id := HasOne(AA);
assert id eq -6*AA.4;

z1 := AA.1 - id;
z2 := AA.2 - id;
z3 := AA.3 - id;

assert forall{z : z in [z1, z2, z3] | z in Nullspace(frob2)};

// Observe that the Miyamoto group acts on the zi
// Try the two S_3 modules

assert Dimension(ideal<AA|z1+z2+z3>) eq 3;
assert Dimension(ideal<AA| z1-z2, z2-z3>) eq 3;

// So only quotient is 1A

// -------------------------------------------------------

// 3*al^2 + 3*al*bt - 9*al - 2*bt + 4 = 0
// This has soln bt = (3*Al^2 - 9*Al + 4)/(2-3*Al)
// If Al ne 2/3
FF<Al> := FunctionField(QQ);
phi := hom<F->FF | [Al, (3*Al^2 - 9*Al + 4)/(2-3*Al)]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

assert Dimension(NullSpace(frob2)) eq 3;

so, id := HasOne(AA);
assert id eq -2/3*(3*Al-2)/(Al*(2*Al-1))*AA.4;

z1 := AA.1 - id;
z2 := AA.2 - id;
z3 := AA.3 - id;

assert forall{z : z in [z1, z2, z3] | z in Nullspace(frob2)};

// Observe that the Miyamoto group acts on the zi
// Try the two S_3 modules

assert Dimension(ideal<AA|z1+z2+z3>) eq 3;
assert Dimension(ideal<AA| z1-z2, z2-z3>) eq 3;
// So only quotient is 1A

// Need to Check when al = 2/3
FF<Bt> := FunctionField(QQ);
phi := hom<F->FF | [2/3, Bt]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

assert Determinant(frob2) eq -1/(3*2^4)*(Bt-1)*(3*Bt+1);

// Can't have Bt = 1, so just need to check Al = 2/3, Bt = -1/3

assert (1 - 3*(2/3)^2)/(3*2/3 - 1) eq -1/3;
// So this is just the case above


