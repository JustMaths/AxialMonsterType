/*
******************************

Code to verify properties of the 4A(1/4, bt) algebra

******************************
*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";

QQ := Rationals();
ZZ := Integers();

// =========================================================
//
// 4A(1/4, bt)
//
// =========================================================

A, gen, frob := M4A();
F<bt> := BaseRing(A);

// identity
so, id := HasOne(A);
assert so;
assert id eq A![0,0,0,0,4/(bt-1/2)];
// So the algebra has an identity iff bt ne 1/2

u_0 := (2*bt-1)*A.1 - 8*A.5;
u_al := (4*bt-1)*(A.1+A.3) - (A.2+A.4) -8*A.5;
u_bt := A.2-A.4;

assert A.1*u_0 eq 0;
assert A.1*u_al eq 1/4*u_al;
assert A.1*u_bt eq bt*u_bt;

// <<a_0, a_2 >> = 2B
assert A.1*A.3 eq 0;

// Check double axes
x := A.1+A.3;
y := A.2+A.4;

// They have Monster type (1/2, 2bt)
// NB need bt ne 1/2
assert HasMonsterFusionLaw(x: fusion_values:=[1/2, 2*bt]);
assert HasMonsterFusionLaw(y: fusion_values:=[1/2, 2*bt]);

B, inc := sub<A|x,y>;
assert Dimension(B) eq 3;
assert Eigenvalues(B!x) eq {<1,1>, <0,1>, <1/2,1>};
assert Eigenvalues(B!y) eq {<1,1>, <0,1>, <1/2,1>};

so, id_B := HasOne(B);
assert so;
assert id eq id_B;
assert id_B eq B![0,0,4/(bt-1/2)];
// Need bt not 1/2 to have an identity
assert B.1*B.2-(B.1+B.2)/2 eq (bt-1/2)*id_B;
// so x,y generate S(dl) where dl = 8(bt-1/2) + 2

// Now check for ideals

assert frob[1,2] eq bt;
// So the projection graph always has an edge between a_0 and a_1
// The projection graph is a square
// So no ideals containing axes

assert Determinant(frob) eq -1/8*bt*(2*bt-1)^3;
// Since the characteristic is not 2 and bt can't be 0, we just need to check bt = 1/2

// Check bt = 1/2
A, gen, frob := M4A(1/2);

// no identity
assert not HasOne(A);

// Check double axes
x := A.1+A.3;
y := A.2+A.4;

// They have Jordan type 1/2, but have a 3-dim 1-space
assert HasJordanFusionLaw(x: fusion_value:=1/2);
assert HasJordanFusionLaw(y: fusion_value:=1/2);
assert Eigenvalues(x) eq { <1,3>, <0,1>, <1/2,1>};
assert Eigenvalues(y) eq { <1,3>, <0,1>, <1/2,1>};

B, inc := sub<A|x,y>;
assert Dimension(B) eq 3;

// in B, the axes are primitve Jordan type 1/2
assert Dimension(Eigenspace(B!x, 1)) eq 1;
assert Dimension(Eigenspace(B!y, 1)) eq 1;

so, id := HasOne(B);
assert not so;
// So B is \widehat{S^circ}(2)

// The radical is 2-dimensional
P<lm> := PolynomialRing(QQ);
assert CharacteristicPolynomial(frob) eq lm^2*(lm-1)^2*(lm-2);
// So radical has at most dim 2 over any field

assert Dimension(NullSpace(frob)) eq 2;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
r := A.1-A.2+A.3-A.4;
assert r in R and A.5 in R;

// The quotient is S(0)
B, quo := quo<A|R>;
assert sub<B|B.1,B.2> eq B;  // so B is 2-generated
B.1 eq A.1@quo;
B.2 eq A.2@quo;

assert HasJordanFusionLaw(B.1: fusion_value:=1/2);
assert HasJordanFusionLaw(B.2: fusion_value:=1/2);
// So it is a 2-generated algebra of Jordan type 1/2

so, id := HasOne(B);
assert so;
assert (A.1+A.3)@quo eq id;
assert B.1*B.2-(B.1+B.2)/2 eq -id/4;
// Hence B is S(0) as 1/8(0-2) = -1/4

// A.5 spans the annihilator of the algebra
assert forall{i  : i in [1..5] | A.i*A.5 eq 0};
I := ideal<A|A.5>;
assert Dimension(I) eq 1;

// This is Yabe's quotient 4A(1/4,1/2)^x
// This is of Monster type
B, quo := quo<A|I>;

assert HasMonsterFusionLaw(B.1: fusion_values := {@ 1/4,1/2 @});
assert HasMonsterFusionLaw(B.2: fusion_values := {@ 1/4,1/2 @});


// There are no other ideals except these
// as A.5 spans the annihilator and
assert r*r eq -8*A.5;

// ---------------------------------------------------
//
// Idempotents
//
// ---------------------------------------------------

// These are some calculations which support a theoretical proof

A, gen, frob := M4A();
F<bt> := BaseRing(A);
// Changing basis makes the equations much nicer and so massively speeds up the Groebner basis
bas := [A.1-A.3,A.2-A.4,A.1+A.3, A.2+A.4, A.5];
AA := ChangeBasis(A, bas);

I := IdempotentIdeal(AA);

P<lm0,lm1,mu0,mu1,nu> := Generic(I);

P0 := 2*mu0 + 4*bt*mu1 + (2*bt-1)/4*nu - 1;
P1 := 2*mu1 + 4*bt*mu0 + (2*bt-1)/4*nu - 1;
Q :=  mu0 + mu1 + (2*bt-1)/4*nu - 1;

assert Basis(I) eq [ lm0*P0, lm1*P1, lm0^2 + mu0*Q, lm1^2+mu1*Q, 8*mu0*mu1 + nu*((2*bt-1)/8*nu-1)];

//---------------------------------------
//
// We suppose that bt ne 1/2
//

// Now for the idempotents not in the infinite family

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
phi := PermutationMatrix(F, [2,1,4,3,5]);
                 
// phi is the automorphism which switches the generating axes
assert forall{ <i,j> : i,j in [1..4] | (A.i*phi)*(A.j*phi) eq (A.i*A.j)*phi};
Miy := sub<GL(5,F) | t1,t2>;
G := sub<GL(5,F) | t1,t2,phi>;

// Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits
assert Order(Miy) eq 4;
assert Order(G) eq 8;

// we require bt -3/2
FCl := AlgebraicClosure(F);
rt1 := Sqrt(FCl!1/(bt+3/2));
rt2 := Sqrt(FCl!1/bt/(bt+3/2));

ACl := ChangeRing(A, FCl);
frobCl := ChangeRing(frob, FCl);

G_FCl := ChangeRing(G, FCl);

// The orbits of length 1 are the identity and zero
so, id := HasOne(ACl);
assert so;
assert id eq ACl![0,0,0,0,4/(bt-1/2)];

assert InnerProduct(id*frobCl, id) eq 4;

// When bt ne -3/2
v1 := 1/4*rt2*ACl![1,1,1,1,0] + rt1/2*ACl![1,1,-1,-1,0] -2*(2*bt+1)/(2*bt-1)*rt2*ACl.5;

assert IsIdempotent(id/2 + v1);
assert InnerProduct((id/2 + v1)*frobCl, id/2 + v1) eq 2*(1 - bt*rt2);

assert #Eigenvalues(id/2 + v1) eq 5;
_, _, FL := IdentifyFusionLaw(id/2 + v1);
Gr, gr := Grading(FL);
assert Order(Gr) eq 2;
assert MiyamotoInvolution(id/2 + v1) eq phi;

o1 := {@ ACl!u : u in Orbit(G_FCl, Vector(id/2+v1))@};
assert #o1 eq 4;
assert id/2-v1 notin o1;

assert IsIdempotent(id/2-v1);
assert InnerProduct((id/2-v1)*frobCl,(id/2- v1)) eq 2*(1 +bt*rt2);

// Check the characteristic polynomials
// Only ones we need to check are 1/2id \pm v1 and the infinite family

// NB that a_0 is Monster type if and only if a_0-1/2id has eigenvalues
// 1/2, -1/2 (twice), -1/4, bt-1/2

P<t> := PolynomialRing(FCl);

assert CharacteristicPolynomial(ACl.1-1/2*id) eq (t-1/2)*(t+1/2)^2*(t+1/4)*(t - (bt-1/2));

// So v1 must have these eigenvalues for one of 1/2id \pm v1 to be of Monster type

rt3 := Sqrt(FCl!(4-7*bt));

a := -1/4*bt*rt2;
b := 1/4*rt1*rt3;

assert CharacteristicPolynomial(v1) eq (t+1/2)*(t-1/2)*(t -4*a)*( t - (a+b))*(t- (a-b));

// We need {4a, a+b, a-b} to equal to {-1/2, -1/4, bt-1/2}

// Can't have 4*a = -rt1/rt2 = -1/2, otherwise, squaring we get
assert (4*a)^2 eq bt/(bt+3/2);
// equals 1/4.
// So 4bt = bt+3/2 and hence bt = 1/2, a contradiction.

// So, we must have {a-b,a+b} = {-1/2,-1/4}, or {-1/2, bt-1/2}
// this  corresponds to (2a, 2b) = (-3/4, pm 1/4), or (bt-1, pm bt)

// Suppose that (2a, 2b) = (-3/4, pm 1/4) and so 2b = \pm 1/4
assert (2*b)^2 eq 1/4*(4-7*bt)/(bt+3/2);
// this must equal 1/4^2
// hence the following must be 0
assert (bt+3/2) - 4*(4-7*bt) eq 29*(bt-1/2);
// and so bt = 1/2, a contradiction

// Suppose that (2a, 2b) = (bt-1, pm bt)
// So 4a = -1/4
// Then, bt-1 = -1/8 and so
// bt = 7/8
// However
assert (4*a)^2 eq bt/(bt+3/2);
// must equal 1/16 and so 15bt = 3/2 and bt = 1/10
assert 7*10-8 eq 2*31;
// So we must be in characteristic 31
// Finally
assert (2*b)^2 eq 1/4*(4-7*bt)/(bt+3/2);
assert Evaluate(1/4*(4-7*bt)/(bt+3/2), 1/10) eq 33/64;
// This must equal bt^2 = 1/100
assert GF(31)!(33/64) eq 1;
assert GF(31)!(1/100) eq 9;
// A contradiction.

// ------------------------------------------------
//
// bt ne 1/2
// Now check the infinite family of idempotents



P<lm, mu> := PolynomialRing(F, 2);
P<lm, mu> := quo<P | lm^2 + 2*(4*bt-1)*lm*mu + mu^2 -1>;

AP := ChangeRing(A, P);

x := lm*(AP.1+AP.3) + mu*(AP.2+AP.4) + 1/2*(1-lm-mu)*8/(2*bt-1)*AP.5;

assert IsIdempotent(x);

assert InnerProduct(x*ChangeRing(frob,P), x) eq 2;

char := CharacteristicPolynomial(AdjointMatrix(x));

PP<t> := PolynomialRing(P);

assert char eq t*(t-1)*(t-1/2)*(t - 1/2*(1 + lm + (4*bt-1)*mu))*(t - 1/2*(1 + mu + (4*bt-1)*lm));

// This can't be Monster type (1/4, bt) since 1/2 can't be 0, or 1/4.  So 1/2 = bt, but we are in the case where bt ne 1/2



// ----------------------------------
//
// Check bt eq 1/2

A, gen, frob := M4A(1/2);
I := IdempotentIdeal(A);
assert Dimension(I) eq 1;

prim := PrimaryDecomposition(I);    
assert #prim eq 3;
prim0 := [ J : J in prim | Dimension(J) eq 0];
prim1 := [ J : J in prim | Dimension(J) ne 0];

FCl := AlgebraicClosure(QQ);

assert #prim0 eq 1;
assert Variety(prim0[1], FCl) eq [<0,0,0,0,0>];

assert #prim1 eq 2;
J := prim1[1];
P := Generic(J);

J0 := ideal<P | P.1+P.2+P.3+P.4-1, P.1*P.3+P.5/8, P.2*P.4+P.5/8, (P.1+P.3)^2 -(P.1+P.3) + P.5/2>;
assert J0 eq J;

// We can describe the family theoretically.  Just need some products

r := A.1-A.2+A.3-A.4;

u := A.1-A.3;
v := A.2-A.4;
d0 := A.1+A.3;
d1 := A.2+A.4;
s := 1/2*(d0+d1);

assert d0 eq 1/2*(2*s+r);
assert d1 eq 1/2*(2*s-r);

assert u^2 eq d0;
assert u*v eq 0;
assert v^2 eq d1;
assert u*s eq u;
assert v*s eq v;
assert s^2 eq s + 2*A.5;
assert r*u eq 0;
assert r*v eq 0;
assert r*s eq 1/2*r;

F<lm,mu> := PolynomialRing(QQ,2);
F<lm,mu> := quo<F|lm^2+mu^2-1>;

AF := ChangeRing(A, F);

y := 1/2*(lm*AF!Eltseq(u) + mu*AF!Eltseq(v) + AF!Eltseq(s)
           + 1/2*(2*lm^2-1)*AF!Eltseq(r) + 4*lm^2*(1-lm^2)*AF.5);

assert y eq 1/2*(lm*AF!Eltseq(u) + mu*AF!Eltseq(v) + AF.2+AF.4
           + lm^2*AF!Eltseq(r) + 4*lm^2*(1-lm^2)*AF.5);

assert IsIdempotent(y);
assert InnerProduct(y*ChangeRing(frob, F), y) eq 1;

// Check if this is of Monster type
// it has the correct eigenvalues and multiplicities
assert CharacteristicPolynomial(AdjointMatrix(y)) eq CharacteristicPolynomial(Adjoin\
tMatrix(AF.1));

u01 := AF.5;
u02 := 1/2*(-lm*AF!Eltseq(u) - mu*AF!Eltseq(v) + AF!Eltseq(s)) - (1-2*lm^2)/4*AF!Eltseq(r);
ual := AF!Eltseq(r) - 8*(2*lm^2-1)*AF.5;
ubt := mu*(2*lm + 1)*AF.1 -lm*(2*mu+1)*AF.2 + mu*(2*lm-1)*AF.3 - lm*(2*mu-1)*AF.4 + 8*lm*mu*(1-2*lm^2)*AF.5;

// y is not semisimple
assert Rank(AdjointMatrix(y)) eq 4;
assert y*u01 eq 0;
assert y*u02 eq 2*mu^2*(1-mu^2)*AF.5;
// require mu = 0 (and so lm = \pm 1), or mu = \pm 1 (and lm = 0) to get y to be semisimple.
// These solutions give the known axes

assert y*ual eq 1/4*ual;
assert y*ubt eq 1/2*ubt;


// One more ideal of idempotents

// The ideal of idempotents in the double axis subalgebra, which is isomorphic to \widehat{S}^\circ(2)
J2 := prim1[2];
P := Generic(J2);
J20 := ideal<P | P.1-P.3, P.2-P.4, P.1+P.2-1,8*P.1*P.2-P.5>;
assert J20 eq J2;

/*

Soln here is

x := lm*d0 + (1 - lm)*d1 + 8*lm*(1 - lm)*e

*/
FF<lm> := FunctionField(ZZ);
A := M4A(FF!1/2);

x := lm*(A.1+A.3) + (1 - lm)*(A.2+A.4) + 8*lm*(1 - lm)*A.5;
assert IsIdempotent(x);

p := CharacteristicPolynomial(AdjointMatrix(x)) - CharacteristicPolynomial(AdjointMatrix(A.1));

coeffs := Coefficients(8*p);
assert coeffs eq [ 0, 4, -19, 29, -14];
assert GCD(ChangeUniverse(coeffs, Integers())) eq 1;

// so no additional axes from this ideal


// --------------------------------------------------------------------
//
// Nilpotents

// There are nilpotent elements too
A, gen, frob := M4A();
F<bt> := BaseRing(A);
FCl := AlgebraicClosure(F);

N := NilpotentIdeal(A);
primN := PrimaryDecomposition(N);
assert #primN eq 2;

JN := primN[1];
P := Generic(JN);
assert Dimension(JN) eq 1;

// The equations you get from requiring the coefficients in the double axis subalgebra to give a nilpotent
JN0 := ideal<P | P.1-P.3, P.2-P.4, P.1+P.2+(bt-1/2)/2*P.5, P.1^2 + (bt-1/2)/2*( P.1*P.5 - 1/16*P.5^2)>;
assert JN0 eq JN;

// This is precisely the 1-dimensional family of vectors in S(dl) which have length 0.

// The 0-dim ideal is just the zero vector
assert Variety(primN[2], FCl) eq [<0,0,0,0,0>];



// Check bt = 1/2
A, gen, frob := M4A(1/2);

N := NilpotentIdeal(A);
P := Generic(N);
primN := PrimaryDecomposition(N);
assert #primN eq 1;

// Variety corresponds to the radical ie prime ideal
NN := Radical(N);

// NN is the ideal spanned by requiring the coefficients of the axes being 0, ie the nilpotent ideal spanned by A.5
assert ideal<P|P.1, P.2, P.3, P.4> eq NN;
