AttachSpec("2-gen Monster.spec");
AttachSpec("../AxialTools/AxialTools.spec");
load "Property examples/Find idempotents.m";

QQ := Rationals();

// Get the algebra, generators and the frobenius form
A, gen, frob := M3A();
F<al,bt> := BaseRing(A);

assert Determinant(frob) eq -al^2*(3*al - bt - 1)*(3*al^2 + 3*al*bt - bt - 1)*
                                  (3*al^2 + 3*al*bt - 9*al - 2*bt + 4)^3 / ( 2^9*(2*al-1)^5 );
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

// NB Be more careful about the nullspace in alll situations/characteristics!!!!!!!!!

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

// 3*al^2 + 3*al*bt - bt - 1 = 0

// Note, if al = 1/3, then poly is 2/3 \neq 0.  So we can always that al \neq 1/3
// so, we have
// bt := (1-3*al^2)/(3al-1)

FF<Al> := FunctionField(QQ);
phi := hom<F->FF | [Al,(1-3*Al^2)/(3*Al-1)]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

assert Dimension(Nullspace(frob2)) eq 1;
assert AA.4 in Nullspace(frob2);
assert forall{ x : x in Basis(AA) | x*AA.4 eq 0};
// So this is the annihilator

I := ideal<AA | AA.4>;

B, quo := quo<AA | I>;
assert forall{ i : i in [1..3] | AA.i@quo eq B.i};

evals, espace, FL := IdentifyFusionLaw(B.1);

// This is a new quotient
assert { e[1] : e in evals} eq {1, Al, (-Al^2 + 1/3)/(Al - 1/3)};

// Can the nullspace ever be larger for some value of Al?
// look at the frob2
// The last row and collumn is zero, so look at the submatrix and find the nullspace of this
S := Submatrix(frob2, [1..3], [1..3]);

assert Determinant(S) eq Al*(Al-1/2)^2/(Al-1/3)^3;
// As Al \neq 0, 1/2, this never has a non-trivial nullspace.
// So, the nullspace of frob2 is never larger

// -------------------------------------------------------

// 3*al^2 + 3*al*bt - 9*al - 2*bt + 4 = 0
// Note that if al = 2/3, then the poly is -2/3 \neq 0, so we can always assume that al \neq 2/3

// Since Al ne 2/3
// This has soln bt = (3*Al^2 - 9*Al + 4)/(2-3*Al)
FF<Al> := FunctionField(QQ);
phi := hom<F->FF | [Al, (3*Al^2 - 9*Al + 4)/(2-3*Al)]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

assert Dimension(NullSpace(frob2)) eq 3;

so, id := HasOne(AA);
assert id eq -2/3*(3*Al-2)/(Al*(2*Al-1))*AA.4;
// Note that the denominator here is never zero as Al \neq 0,1/2, so we always have an identity.

z1 := AA.1 - id;
z2 := AA.2 - id;
z3 := AA.3 - id;

assert forall{z : z in [z1, z2, z3] | z in Nullspace(frob2)};

// Observe that the Miyamoto group acts on the z_i
// Try the two S_3 modules

assert Dimension(ideal<AA | z1+z2+z3>) eq 3;
assert Dimension(ideal<AA | z1-z2, z2-z3>) eq 3;
// So only quotient is 1A

// ---------------------------------------------

// Look at the idempotents

A, gen, frob := M3A();
F<al,bt> := BaseRing(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(4,F) | t1,t2>;
assert Order(G) eq 6; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

FCl := AlgebraicClosure(F);
// Need to add one root
r := Sqrt(FCl!-(2*al-1)/(3*al-bt-1)/(2*al*bt-al-bt-1));
// So need to check seperately the cases where 3*al-bt-1, or 2*al*bt-al-bt-1 are 0
// NB that -(2*al-1) \neq 0

A := ChangeRing(A, FCl);
frob := ChangeRing(frob, FCl);
idems := FindAllIdempotents(A);
Simplify(FCl);
Prune(FCl);

G := ChangeRing(G, FCl);
orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

// EDIT!


