/*
******************************

Code to verify properties of the 6Y(1/2, 2) algebra

******************************
*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");

QQ := Rationals();

// ===========================================================================================================
//
//            6Y(1/2, 2)
//
// ===========================================================================================================

A, gen, frob := M6Y();

// the Radical is 4 dim
assert Dimension(Nullspace(frob)) eq 4;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
u1 := A.1-A.2;
u2 := A.2-A.3;
u3 := A.4;
u4 := A.5;
assert u1 in R and u2 in R and u3 in R and u4 in R;

// quotient is 1A

// check for subideals
Ann := Annihilator(A);
assert u4 in Ann;

// submodule structure is 2+1+1

// The quotient is 4 dimensional
B_1, quo := quo<A|Ann>;
assert sub<B_1|B_1.1,B_1.2+B_1.4> eq B_1;  //  is 2-generated
assert B_1.1 eq A.1@quo;
assert B_1.2 eq A.2@quo;
assert  HasMonsterFusionLaw(B_1.1:fusion_values:=[1/2,2]);
// The generating axes follow Monster fusion law (1/2, 2), Quotient is 4y(1/2,2)^x

I_2 := ideal<A|u3,u4>;
B_2, quo := quo<A|I_2>;
assert sub<B_2|B_2.1,B_2.2> eq B_2;  //  is 2-generated
assert B_2.1 eq A.1@quo;
assert B_2.2 eq A.2@quo;
assert HasJordanFusionLaw(B_2.1: fusion_value := 2);
//axes follow Jordan fusion law J(2)
so,id:= HasOne(B_2);
assert so;
// B_2 is 3C(2)

I_3 := ideal<A|u1,u2>;
B_3, quo := quo<A|I_3>;
assert sub<B_3|B_3.1,B_3.2> eq B_3;  //  is 2-generated
assert B_3.1 eq A.1@quo;
assert B_3.2 eq A.4@quo;
assert HasJordanFusionLaw(B_3.1: fusion_value := 1/2);
//axes follow Jordan fusion law J(1/2)
so,id:= HasOne(B_3);
assert not so;
// B_3 is \widehat{S}(2)^\circ

I_4 := ideal<A|u1,u2,u4>;
B_4, quo := quo<A|I_4>;
assert sub<B_4|B_4.1,B_4.2> eq B_4;  //  is 2-generated
assert B_4.1 eq A.1@quo;
assert B_4.2 eq A.4@quo;
assert HasJordanFusionLaw(B_4.1: fusion_value := 1/2);
//axes follow Jordan fusion law J(1/2)
so,id:= HasOne(B_4);
assert not so;
// B_4 is S(2)^\circ

I_5 := ideal<A|u1,u2,u3,u4>;
B_5, quo := quo<A|I_5>;
assert B_5.1 eq A.1@quo;
// B_5 is 1A

////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////         6Y Idempotents            //////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////

A, gen, frob := M6Y();

P<mu, nu> := PolynomialRing(QQ, 2);

AP := ChangeRing(A, P);

x := mu*(AP.1-AP.2) + nu*(AP.2-AP.3);

assert x^2 eq (-mu^2-2*mu*nu + 2*nu^2)*(AP.1-AP.2) + (-2*mu^2+2*mu*nu + nu^2)*(AP.2-AP.3);

// So for an idempotent in I we just get three non-zero solutions
I := ideal<P | -mu^2-2*mu*nu + 2*nu^2 - mu, -2*mu^2+2*mu*nu + nu^2 - nu>;
assert Set(Variety(I)) eq { <0,0>, <1/3, 2/3>, <1/3, -1/3>, <-2/3, -1/3>};
assert VarietySizeOverAlgebraicClosure(I) eq 4;

// Check the fusion law for x_i(lm)

P<lm> := FunctionField(QQ);
AP := ChangeRing(A, P);
frobP := ChangeRing(frob, P);

x := lm*AP.1 + (1-lm)*(AP.1+AP.4) + 2*lm*(1-lm)*AP.5;
assert IsIdempotent(x);

assert HasMonsterFusionLaw(x: fusion_values:=[1/2,2]);

assert x*(2*AP.1 -AP.2-AP.3) eq 0;
assert x*AP.5 eq 0;

assert x*(AP.4 + 2*(2*lm-1)*AP.5) eq 1/2*(AP.4 + 2*(2*lm-1)*AP.5);

assert x*(AP.2-AP.3) eq 2*(AP.2-AP.3);

evals, espace, FL := IdentifyFusionLaw(AP.1);
Gr, gr := Grading(FL);
assert Order(Gr) eq 4;
assert not IsCyclic(Gr); // it is a V_4
assert 3@gr eq Gr.1;
assert 4@gr eq Gr.2;
// So all the axes are graded by both al = 1/2 and bt = 2

assert InnerProduct(x*frobP, x) eq 1;

// Now for the y idempotent

so, id1 := HasOne(sub<AP | AP.1, AP.2>);
assert so;
so, id2 := HasOne(sub<AP | AP.1+AP.4, AP.2+AP.4>);
assert so;

y := lm*id1 + (1-lm)*id2 + 2*lm*(1-lm)*AP.5;

assert IsIdempotent(y);
assert HasJordanFusionLaw(y: fusion_value:=1/2);

// y has a 3-dim 1-space spanned by the x_i(lm)
assert x*y eq x;
assert Dimension(Eigenspace(y,1)) eq 3;

assert y*(AP.4 + 2*(2*lm-1)*AP.5) eq 1/2*(AP.4 + 2*(2*lm-1)*AP.5);

assert InnerProduct(y*frobP, y) eq 1;

// Check the 3 extra idempotents
b := 1/3*A![1,1,1,0,0] -A.1;
assert IsIdempotent(b);

assert HasJordanFusionLaw(b: fusion_value:=-1);

assert b*A.1 eq 0;
assert b*A.4 eq 0;
assert b*A.5 eq 0;

assert b*(A.2-A.3) eq -(A.2-A.3);

assert InnerProduct(b*frob, b) eq 0;


// Can double check computationally.
load "Find idempotents.m";
QQ := Rationals();

A, gen, frob := M6Y();

t1 := PermutationMatrix(QQ, [1,4,3,2,5]);
t2 := PermutationMatrix(QQ, [3,2,1,4,5]);
f := PermutationMatrix(QQ, [2,1,4,3,5]);

G := sub<GL(5, QQ) | t1, t2, f>;

I := IdempotentIdeal(A);
AP := Generic(I);
assert Dimension(I) eq 1;

P := BaseRing(AP);

prim := PrimaryDecomposition(I);
assert #prim eq 8;

prim0 := [ J : J in prim | Dimension(J) eq 0];
prim1 := [ J : J in prim | Dimension(J) ne 0];

assert {* VarietySizeOverAlgebraicClosure(J) : J in prim0 *} eq {* 1^^4 *};
vars := {@ A![ e : e in t] : t in Variety(J), J in prim0 @};
assert #vars eq 4;

// So all the idempotents in the finite-dimensional ideal are defined over Q.  They are:
x1 := A![-2/3,1/3,1/3,0,0];
x2 := A![1/3,-2/3,1/3,0,0];
x3 := A![1/3,1/3,-2/3,0,0];

assert {A!0, x1,x2,x3} subset vars;

assert HasJordanFusionLaw(x1: fusion_value:=-1);
assert Dimension(Eigenspace(x1, 0)) eq 3;
assert Dimension(Eigenspace(x1, -1)) eq 1;

assert InnerProduct(x1*frob, x1) eq 0;
// Same holds for x2 and x3

P<lm> := FunctionField(QQ);
AP := ChangeRing(A, P);

x := lm*AP.1 + (1-lm)*(AP.1 + AP.4) + 2*lm*(1-lm)*AP.5;
assert IsIdempotent(x);

assert CharacteristicPolynomial(AdjointMatrix(x)) eq CharacteristicPolynomial(AdjointMatrix(AP.1));

assert HasMonsterFusionLaw(x: fusion_values:=[1/2,2]);
assert Dimension(Eigenspace(x,0)) eq 2;

evals, espace, FL := IdentifyFusionLaw(AP.1);
Gr, gr := Grading(FL);
assert Order(Gr) eq 4;
assert not IsCyclic(Gr); // it is a V_4
assert 3@gr eq Gr.1;
assert 4@gr eq Gr.2;
// So all the axes are graded by both al = 1/2 and bt = 2

so, id1 := HasOne(sub<AP | AP.1, AP.2>);
assert so;
so, id2 := HasOne(sub<AP | AP.1+AP.4, AP.2+AP.4>);
assert so;

y := lm*id1 + (1-lm)*id2 + 2*lm*(1-lm)*AP.5;
assert HasJordanFusionLaw(y: fusion_value:=1/2);
assert Dimension(Eigenspace(y,1)) eq 3;

