/*
******************************

Code to verify properties of the 4Y(1/2, bt) algebra

******************************
*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";

QQ := Rationals();
ZZ := Integers();

// =========================================================
//
// 4Y(1/2, bt)
//
// =========================================================
A, gen, frob := M4Y_bt();
F<bt> := BaseRing(A);

u01 := (4*bt-1)*A.1+A.3 -2*(4*bt-1)*A.5;
u02 := A.2+A.4-4*bt*A.5;
ual := (8*bt-1)*A.1 + A.3-8*bt*A.5;
ubt := A.2-A.4;

assert A.1*u01 eq 0;
assert A.1*u02 eq 0;
assert A.1*ual eq 1/2*ual;
assert A.1*ubt eq bt*ubt;

// identity
so, id := HasOne(A);
assert so;
assert id eq A![-1/2,-1/2,-1/2,-1/2,(6*bt-1)]/(2*bt-1);
// Since bt \neq 1/2, algebra always has an identity

// Subalgebras
B, inc := sub<A|A.1,A.3>;
assert Dimension(B) eq 3;
assert Eigenvalues(B!A.1) eq {<1,1>, <0,1>, <1/2,1>};
assert Eigenvalues(B!A.3) eq {<1,1>, <0,1>, <1/2,1>};
so, id_B := HasOne(B);
assert so;
assert id_B eq (1/2*(A.1+A.3) + (1-4*bt)*A.5)/(1-2*bt);
// Since bt \neq 1/2, B has an identity
assert A.1*A.3-(A.1+A.3)/2 eq 4*bt*(2*bt-1)*id_B;
// so dl = 32bt(2bt-1) + 2 and <<a_0, a_2>> = S(dl)

int := B meet sub<A|A.2,A.4>;
assert Dimension(int) eq 1;
assert A.5 in int;

assert frob[1,5] eq 2*bt;
// A.5 is not in the 0-eigenspace of A.1

// Check the projection graph
assert frob[1,2] eq 4*bt^2;
assert frob[1,3] eq (4*bt-1)^2;
// So the projection graph always has an edge between a_1 and a_2 and for bt neq 1/4 it has an edge between a_1 and a_3
// The projection graph is complete if bt \neq 1/4 and a square if bt = 1/4

assert Determinant(frob) eq 2^8*bt^2*(2*bt-1)^6;
// Since the characteristic is not 2 and bt \neq 0, 1/2, there are no quotients

//------------------------------

// Idempotents

//------------------------------

A, gen, frob := M4Y_bt();
F<bt> := BaseRing(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;

assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

// we do some calculations to support a theoretical proof

// First change basis, to one which reflects the group and algebraic structure better
bas := [A.1-A.3, A.2-A.4, (1/2*(A.1+A.3) + (1-4*bt)*A.5)/(1-2*bt), (1/2*(A.2+A.4)+(1-4*bt)*A.5)/(1-2*bt), A.5];

AA := ChangeBasis(A, bas);

assert AA.1^2 eq 8*bt*(1-2*bt)*AA.3;
assert AA.1*AA.2 eq 0;
assert AA.1*AA.3 eq AA.1;
assert AA.1*AA.4 eq 1/2*AA.1;
assert AA.1*AA.5 eq 1/2*AA.1;

assert AA.3^2 eq AA.3;
assert AA.3*AA.4 eq AA.5;
assert AA.3*AA.5 eq AA.5;

assert AA.5^2 eq AA.5;

P<lm0, lm1, mu0, mu1, nu> := PolynomialRing(F, 5);

AP := ChangeRing(AA, P);

x := lm0*AP.1 + lm1*AP.2 + mu0*AP.3 + mu1*AP.4 + nu*AP.5;

assert x^2 eq lm0*(2*mu0+mu1+nu)*AP.1 + lm1*(2*mu1+mu0+nu)*AP.2
               + (mu0^2 + 8*bt*(1-2*bt)*lm0^2)*AP.3  + (mu1^2 + 8*bt*(1-2*bt)*lm1^2)*AP.4
               + (nu^2 + 2*(mu0+mu1)*nu + 2*mu0*mu1)*AP.5;

// Now we check to see if the new infinite family found is of Monster type (1/2, bt)

P<lm, nu> := PolynomialRing(F, 2);
P<lm, nu> := quo<P | 2*(1-2*bt)*nu^2 -nu + 4*bt*lm^2>;

AP := ChangeRing(A, P);

x := (nu+lm)*AP.1 + (nu-lm)*AP.3 + (1-2*nu)*AP.5;

assert IsIdempotent(x);

assert InnerProduct(x*ChangeRing(frob,P), x) eq 1;

idAP := AP!Eltseq(id);
assert InnerProduct((idAP-x)*ChangeRing(frob,P), idAP-x) eq 2;

char := CharacteristicPolynomial(AdjointMatrix(x));

PP<t> := PolynomialRing(P);
assert char eq t^2*(t^3 + ((1-2*bt)*nu-2)*t^2 + 1/4*(5 - 6*(1-2*bt)*nu)*t - 1/4*(1 - 2*(1-2*bt)*nu));

assert char eq t^2*(t-1)*(t-1/2)*(t-1/2*(1-2*(1-2*bt)*nu));

// So this is only of moster type (1/2, bt) if nu = 1/2, lm = \pm 1/2
// This gives the known axes

// Check the remaining axes not in this family

id_B := (1/2*(A.1+A.3) + (1-4*bt)*A.5)/(1-2*bt);

assert HasJordanFusionLaw(id_B: fusion_value:=1/2);
assert Dimension(Eigenspace(id_B, 1)) eq 3;
assert Dimension(Eigenspace(id_B, 0)) eq 1;
assert Dimension(Eigenspace(id_B, 1/2)) eq 1;
assert MiyamotoInvolution(id_B) eq MiyamotoInvolution(A.1);

assert InnerProduct(id_B*frob, id_B) eq 2;


// --------------------------------
//
// Double check computationally

I := IdempotentIdeal(A);
assert Dimension(I) eq 1;

prim := PrimaryDecomposition(I);    

assert #prim eq 8;
prim0 := [ J : J in prim | Dimension(J) eq 0];
prim1 := [ J : J in prim | Dimension(J) ne 0];

assert #prim0 eq 4;

assert {* VarietySizeOverAlgebraicClosure(J) : J in prim0 *} eq {* 1^^4 *};
vars := {@ A![ e : e in t] : t in Variety(J), J in prim0 @};

assert IsIdempotent(A.5);
so, id := HasOne(A);
assert vars eq {@ A!0, A.5, id, id-A.5 @};

// z and 1-z are in our infinite families

assert HasJordanFusionLaw(A.5: fusion_value:=1/2);
assert Dimension(Eigenspace(A.5, 0)) eq 2;
assert Dimension(Eigenspace(A.5, 1/2)) eq 2;
assert MiyamotoInvolution(A.5) eq t1*t2;

assert InnerProduct(id*frob,id) eq 3;
assert InnerProduct((id-A.5)*frob,id-A.5) eq 2;


assert #prim1 eq 4;
// These are the idempotents in the subalgebras <<a_0, a_2> \cong S(\dl), <<a1, a3>> and id - x, for x in each.


// Nilpotent elements

N := NilpotentIdeal(A);
primN := PrimaryDecomposition(N);

primN0 := [ J : J in primN | Dimension(J) eq 0];
primN1 := [ J : J in primN | Dimension(J) ne 0];


assert Variety(primN0[1]) eq [<0,0,0,0,0>];
assert VarietySizeOverAlgebraicClosure(primN0[1]) eq 1;

// For the one dimensional ideals, the (radical of these) give the nilpotents in the subalgebras <<a_0, a_2> \cong S(\dl), <<a1, a3>>.
