/*
******************************

Code to verify properties of the non-symmetric algebras

******************************
*/
AttachSpec("../2-gen Monster.spec");
Attach("../2-gen_Monster_non-symmetric.m");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";

QQ := Rationals();

// -------------------------------------
//
// 3C'(al, 1-al)
//
// -------------------------------------
A, gens, frob := M3Cprime();
F<al> := BaseRing(A);

assert sub<A|gens> eq A;
assert IsFrobeniusForm(frob, A);
assert HasJordanFusionLaw(gens[1] : fusion_value := 1-al);
assert HasJordanFusionLaw(gens[2] : fusion_value := al);

so, id := HasOne(A);
assert so;
assert id eq 1/al*A![-1,1,1];

assert Determinant(frob) eq al^2*(al+1)^2*(al-2)^2/4;

// For al = -1
A, gens, frob := M3Cprime(-1);
I := ideal<A|[A!v : v in Basis(Nullspace(frob))]>;

assert Dimension(I) eq 2;
assert A.2 in I and A.3 in I;
// Since A.2 and A.3 are switched by the Miyamoto involution, there are two candidates for 1-dim ideals:
// A.2+A.3 and A.2-A.3

assert A.2*(A.2+A.3) eq -A.3;
assert A.2*(A.2-A.3) eq 2*A.2 + A.3;
// So there are no 1-dim ideals.
// Only quotient is 1A

// idempotents here are all known

// -------------------------------------
//
// 3Q'(1/3, 2/3)
//
// -------------------------------------
A, gens, frob := M3Qprime();
F := BaseRing(A);

assert sub<A|gens> eq A;
assert IsFrobeniusForm(frob, A);

assert HasJordanFusionLaw(gens[1] : fusion_value := 1/3);
assert HasMonsterFusionLaw(gens[2] : fusion_values := [1/3, 2/3]);

so, id := HasOne(A);
assert so;
assert id eq 3*A![-1,1,-1,1];

// The Miyamoto group switches A.1 and A.3 and fixes the remaining algebra.
assert A.1*A.3 eq 0;
// so the subalgebra they span in a 2B

assert Determinant(frob) eq 5^3/2^8/3^3;
// So has a non-trivial radical only in characteristic 5

A, gens, frob := M3Qprime(:base_ring:=GF(5));
F := BaseRing(A);
I := ideal<A|[A!v : v in Basis(Nullspace(frob))]>;

assert Dimension(I) eq 3;
assert A.1 in I and A.3 in I and A.2-A.4 in I;

// The Miyamoto group switches A.1 and A.3 and fixes the remaining algebra.
// So possible 1-dimensional ideals are A.1+A.3, A.1-A.3, A.2-A.4;

assert A.1*(A.1+A.3) eq A.1;
assert A.1*(A.1-A.3) eq A.1;
assert A.2*(A.2-A.4) eq A.1+A.3 + 3*(A.2-A.4);

// so no 1-dimensional ideals.
// Only possible 2-dim ideal is <A.1, A.3>
assert A.2*A.1 eq A.2-A.4 -A.1;

// so no subideals for char 5
// Only quotient for char 5 is 1A

// -------------------------------------
//
// 4Q(2bt, bt)
//
// -------------------------------------
A, gens, frob := M4Q();
F<bt> := BaseRing(A);

assert sub<A|gens> eq A;
assert IsFrobeniusForm(frob, A);

assert HasJordanFusionLaw(gens[1] : fusion_value := bt);
assert HasMonsterFusionLaw(gens[2] : fusion_values := [2*bt, bt]);

so, id := HasOne(A);
assert so;
assert id eq 1/(2*bt+1)*A![1,1,1,1];

// Miyamoto group is V_4
assert A.1*A.3 eq 0;
// So this is a 2B subalgebra

assert Dimension(sub<A|A.2, A.4>) eq 3;
c := A.2+A.4 -1/bt*A.2*A.4;
assert c eq A.1+A.3;
assert c^2 eq c;
assert A.2*A.4 eq bt*(A.2+A.4-c);
// So this is a 3C(2bt)

assert Determinant(frob) eq 2^2*(bt-1)^2*(2*bt+1);
// bt can't be 1, so only option is bt = -1/2

A, gens, frob := M4Q(-1/2);
F := BaseRing(A);

I := ideal<A|[A!v : v in Basis(Nullspace(frob))]>;
assert Dimension(I) eq 1;
assert A![1,1,1,1] in I;

// Quotient is 4Q(-1, 1/2)
B, quo := quo<A|I>;
BB := M4Qx();
assert [[ Eltseq(v) : v in r] : r in BasisProducts(B)] eq [[ Eltseq(v) : v in r] : r in BasisProducts(BB)];

// -------------------------------------
//
// 4B(-1, 1/2; nu)^\times
//
// -------------------------------------
A, gens, frob := M4BNonSymmetric();
F<nu> := BaseRing(A);

assert sub<A|gens> eq A;
assert IsFrobeniusForm(frob, A);

assert HasMonsterFusionLaw(gens[1] : fusion_values := [-1, 1/2]);
assert HasMonsterFusionLaw(gens[2] : fusion_values := [-1, 1/2]);

assert not HasOne(A);

I := ideal<A|[A!v : v in Basis(Nullspace(frob))]>;
assert Dimension(I) eq 1;
assert A.1+A.3 -(A.2+A.4) in I;
// already know this quotient from the symmetric 4B algebra
// it is IY_3(-1, 1/2; 0)^times

