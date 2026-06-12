/*
******************************

Code to verify properties of the 4J(2*bt, bt) algebra

******************************
*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";

QQ := Rationals();

// =========================================================
//
// 4J(2bt, bt)
//
// =========================================================
A, gens, frob := M4J();
F<bt> := BaseRing(A);
al := 2*bt;

// Confirm the algebra is indeed a 2-generated Monster type algebra

assert sub<A | gens> eq A;
assert HasMonsterFusionLaw(gens[1]: fusion_values:=[al, bt]);
assert HasMonsterFusionLaw(gens[2]: fusion_values:=[al, bt]);
assert IsFrobeniusForm(frob, A);

// identity
so, id := HasOne(A);
assert so;
assert id eq A![1,1,1,1,1]/(4*bt+1);
// so algebra has an identity iff bt \neq -1/4

// <<a_0, a_2 >> = 2B
assert A.1*A.3 eq 0;

// Check double axes
d0 := A.1+A.3;
d1 := A.2+A.4;
assert HasMonsterFusionLaw(d0: fusion_values := {@ 4*bt, 2*bt@});
assert HasMonsterFusionLaw(d1: fusion_values := {@ 4*bt, 2*bt@});
// They have Monster type (4bt, 2bt)
// NB need bt ne 1/4

B, inc := sub<A|d0,d1>;
assert Eigenvalues(B!d0) eq {<1,1>, <0,1>, <4*bt,1>};
assert Eigenvalues(B!d1) eq {<1,1>, <0,1>, <4*bt,1>};
assert Dimension(B) eq 3;
c := B.1+B.2 - 1/(2*bt)*B.1*B.2;
assert c^2 eq c;
assert A.5 eq c;
// So B is a 3C(4bt)


// Consider the ideals
assert frob[1,2] eq bt;
// So the projection graph always has an edge between a_1 and a_2
// The projection graph is a square

assert Determinant(frob) eq 2*(2*bt-1)^2*(4*bt+1);
// Since characteristic is not 2 and bt \neq 1/2, just need to check bt = -1/4

A, gens, frob := M4J(-1/4);
// NB not char 5 as -1/4 = 1
// not char 3 as 2bt = -2/4 = -2 = 1

// no identity
assert not HasOne(A);

P<lm> := PolynomialRing(QQ);
assert CharacteristicPolynomial(frob) eq lm*(lm-1)^2*(lm-3/2)*(lm-5/2);
// Since char is not 3, or 5, then Radical has dim at most 1.

R := NullSpace(frob);
assert Dimension(R) eq 1;
assert A!R.1 eq A![1,1,1,1,1];

// The radical is the annihilator
ann := Annihilator(A);
assert A!R.1 eq ann.1;

// Quotient is 4J(-1/2, -1/4)^d0
B, quo := quo<A|R.1>;

assert not HasOne(B);

// Check double axes for bt = 1/4
A, gens, frob := M4J(1/4);
// Check double axes
d0 := A.1+A.3;
d1 := A.2+A.4;
assert HasJordanFusionLaw(d0: fusion_value := 1/2);
assert HasJordanFusionLaw(d1: fusion_value := 1/2);
// They are Jordan 1/2 axes with a 3-dim 1-space
assert Dimension(Eigenspace(d0,1)) eq 3;
assert Dimension(Eigenspace(d1,1)) eq 3;

B, inc := sub<A|d0,d1>;
assert Dimension(B) eq 3;
assert IsAssociative(B);
// It is a sort of 3C(1)
// axes have a 2-dim 1-space and a 1-dim 0-space
assert Eigenvalues(B!d0) eq {<1,2>, <0,1>};
assert Eigenvalues(B!d1) eq {<1,2>, <0,1>};
c := B.1+B.2 - 2*B.1*B.2;
assert c^2 eq c;

//------------------------------

// Idempotents

//------------------------------

// These are some calculations which support a theoretical proof

A, gens, frob := M4J();
F<bt> := BaseRing(A);
// Changing basis makes the equations much nicer and so massively speeds up the Groebner basis
bas := [A.1-A.3,A.2-A.4,A.1+A.3, A.2+A.4, A![1,1,1,1,1]];
AA := ChangeBasis(A, bas);

I := IdempotentIdeal(AA);

P<lm0,lm1,mu0,mu1,nu> := Generic(I);

P0 := 2*mu0 + 4*bt*mu1 + 2*(4*bt+1)*nu - 1;
P1 := 2*mu1 + 4*bt*mu0 + 2*(4*bt+1)*nu - 1;
Q0 :=  mu0 + 8*bt*mu1 + 2*(4*bt+1)*nu - 1;
Q1 :=  mu1 + 8*bt*mu0 + 2*(4*bt+1)*nu - 1;

assert Basis(I) eq [ lm0*P0, lm1*P1, lm0^2 + mu0*Q0, lm1^2+mu1*Q1, -4*bt*mu0*mu1 + nu*((4*bt+1)*nu-1)];

// Check the orbits and lengths

FCl := AlgebraicClosure(F);
rt1 := Sqrt(FCl!(1-4*bt)*(1+4*bt));
rt2 := Sqrt(FCl!(1-8*bt));
rt3 := Sqrt(FCl!1/(1-12*bt^2));
rt4 := Sqrt(FCl!(1-4*bt));

I := IdempotentIdeal(AA); 
assert #Variety(I, FCl) eq 32;

Simplify(FCl: Partial:=true);
Prune(FCl);

ACl := ChangeRing(A, FCl);
frobCl := ChangeRing(frob, FCl);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;
assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

GCl := ChangeRing(G, FCl);  // Still remembers the order from above

so, id := HasOne(ACl);

x := rt3/2*rt4*ACl![1,1,-1,-1,0] + rt3/2*ACl![1,1,1,1,0] -(2*bt+1)/2/(4*bt+1)*rt3*ACl![1,1,1,1,1];

assert x eq  rt3/2/(4*bt+1)*( (2*bt + (4*bt+1)*rt4)*(ACl.1+ACl.2) + (2*bt - (4*bt+1)*rt4)*(ACl.3+ACl.4) -(2*bt+1)*ACl.5);
assert x eq  rt3/2/(4*bt+1)*( 2*bt*(ACl.1+ACl.2+ACl.3+ACl.4) + (4*bt+1)*rt4*(ACl.1+ACl.2 -ACl.3-ACl.4) -(2*bt+1)*ACl.5);

y := 1/2*rt2/rt1*ACl![1,0,-1,0,0] + 1/2/rt1*ACl![1,0, 1,0,0] + 1/rt1*ACl![0,1,0,1,0] -1/2/rt1*ACl![1,1,1,1,1];

// The complete set of idempotents

idems := [ ACl!0, ACl.5, ACl.1, ACl.1+ACl.3, id, id - ACl.1, id - ACl.5, id - (ACl.1+ACl.3), id/2+x, id/2-x, id/2+y, id/2-y];

orbs := {@ {@ ACl!u : u in Orbit(GCl, Vector(v))@} : v in idems @};  // Need to have found the order for Orbit to work
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

// So we have all the idempotents
assert #orbs eq 12;
assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^6 *};
assert #(&join orbs) eq 32;

// We now check for properties of the idempotents

// Orbits of size 1
// 0, A.5, id and id-A.5
// need bt \neq -1/4
so, id := HasOne(ACl);
assert so;
assert id eq 1/(4*bt+1)*ACl![1,1,1,1,1];
assert InnerProduct(id*frobCl, id) eq 6/(4*bt+1);

assert IsIdempotent(ACl.5);
assert HasMonsterFusionLaw(ACl.5 : fusion_values:=[4*bt, 2*bt]);
assert Dimension(Eigenspace(ACl.5, 2*bt)) eq 2;
t1_FCl := ChangeRing(t1, FCl);
t2_FCl := ChangeRing(t2, FCl);
assert MiyamotoInvolution(ACl.5) eq t1_FCl*t2_FCl;

assert InnerProduct(ACl.5*frobCl, ACl.5) eq 2;

assert InnerProduct((id-ACl.5)*frobCl, (id-ACl.5)) eq 4*(1-2*bt)/(4*bt+1);


// Orbits of size 2
// double axes and id - these
d0 := ACl.1+ACl.3;
assert exists(od0){o : o in orbs | d0 in o};
assert #od0 eq 2;
f_FCl := ChangeRing(f, FCl);
assert d0*f_FCl in od0;

assert id-d0 notin od0;
assert exists(od0_pair){o : o in orbs | id - d0 in o};

assert InnerProduct((d0)*frobCl, (d0)) eq 2;
assert InnerProduct((id-d0)*frobCl, (id-d0)) eq 4*(1-2*bt)/(1+4*bt);


// Orbits of size 4
// axes, id - axes, x, id-x, y and id -y
assert {@ ACl.i : i in [1..4] @} in orbs;

assert {@ id-ACl.i : i in [1..4] @} in orbs;
assert InnerProduct((id-ACl.1)*frobCl, (id-ACl.1)) eq (5-4*bt)/(1+4*bt);

assert IsIdempotent(id/2+x);
evals, espace, FL := IdentifyFusionLaw(id/2+x);
assert #FL eq 5;
assert Order(Grading(FL)) eq 2;
assert MiyamotoInvolution(x) eq f_FCl;

assert exists(ox){o : o in orbs | id/2+x in o};
assert #ox eq 4;
assert (id/2+x)*f_FCl in ox;
assert InnerProduct((id/2+x)*frobCl, id/2+x) eq 1/(4*bt + 1)*(3+ (2*bt - 1)*rt3);

assert id/2-x notin ox;
assert exists(ox_pair){o : o in orbs | id/2 - x in o};
assert InnerProduct((id/2-x)*frobCl, (id/2-x)) eq (3 -(2*bt-1)*rt3)/(1+4*bt);

assert IsIdempotent(id/2+y);
evals, espace, FL := IdentifyFusionLaw(id/2+y);
assert #FL eq 5;
assert Order(Grading(FL)) eq 2;
assert MiyamotoInvolution(id/2+y) eq t1_FCl;

assert exists(oy){o : o in orbs | id/2+y in o};
assert #oy eq 4;
assert (id/2+y)*f_FCl in oy;

assert id/2-y notin oy;
assert exists(oy_pair){o : o in orbs | id/2 - y in o};

assert InnerProduct((id/2+y)*frobCl, id/2+y) eq 3/(4*bt+1);
assert InnerProduct((id/2-y)*frobCl, (id/2-y)) eq 3/(4*bt+1);


// Check for characteristic polynomial matching Monster type

poss := CheckForMatchingCharactisticPoly(ACl.1, orbs);

assert #poss eq 4;

// The first two possibilities are in characteristic 3, or 5 only and lead to a contradiction
I := poss[1,4];
P := Generic(I);

// The order of the variables is rt3, then bt
assert poss[1,3] eq [* <rt3, P.1>, <bt, P.2> *];

assert 15 in I;
assert P.2+4 in I;
// If char = 3, then 0 = bt+4 = bt+1 and so bt = -1.  Then al = 2*bt = 1, a contradiction
// If char = 5, then 0 = bt+4 = bt-1 and so bt = 1 a contradiction

// Same argument for the second case
I := poss[2, 4]; P := Generic(I);
assert poss[2,3] eq [* <rt3, P.1>, <bt, P.2> *];
assert 15 in I;
assert P.2+4 in I;

// The last two possibilities must be in characteristic 3 and this gives a contradiction too
I := poss[3, 4]; P := Generic(I);
assert poss[3, 3] eq [* <rt1, P.1>, <bt, P.2> *];
assert 9*P.1 in I;
// So either rt1 = 0, a contradiction, or char = 3
assert P.1*(P.2+1)^2 in I;
// Since rt1 ne 0, we must have bt = -1, but then 2*bt = 1, a contradiction

// Same argument for the last case
I := poss[4, 4]; P := Generic(I);
assert poss[4, 3] eq [* <rt1, P.1>, <bt, P.2> *];
assert 9*P.1 in I;
// So either rt1 = 0, a contradiction, or char = 3
assert P.1*(P.2+1)^2 in I;
// Since rt1 ne 0, we must have bt = -1, but then 2*bt = 1, a contradiction






// --------------------
//
// bt = -1/4
bt := -1/4;
A, gens, frob := M4J(bt);

F := QQ;
t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;

assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits
I := IdempotentIdeal(A);

FCl := AlgebraicClosure(F);
rt := Sqrt(FCl!2);

ACl := ChangeRing(A, FCl);
frobCl := ChangeRing(frob, FCl);

assert #Variety(I, FCl) eq 12;

xp := 2*ACl![1,1,1,1,0] + rt*(ACl.1-ACl.3+ACl.2-ACl.4) + ACl.5;

idems := [ACl!0, ACl.5, ACl.1, ACl.1+ACl.3, xp];

GCl := ChangeRing(G, FCl);
orbs := {@ {@ ACl!u : u in Orbit(GCl, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

// These are all the idempotents
assert &+[ #o : o in orbs] eq 12;
assert #orbs eq 5;
assert {* #o : o in orbs *} eq {* 1^^2, 2, 4^^2 *};

assert not HasOne(A);

assert IsIdempotent(ACl.5);
assert HasMonsterFusionLaw(ACl.5 : fusion_values:=[4*bt, 2*bt]);
assert Dimension(Eigenspace(ACl.5, 2*bt)) eq 2;
t1_FCl := ChangeRing(t1, FCl);
t2_FCl := ChangeRing(t2, FCl);
assert MiyamotoInvolution(ACl.5) eq t1_FCl*t2_FCl;


// Orbits of size 2
// double axes
d0 := ACl.1+ACl.3;
assert exists(od0){o : o in orbs | d0 in o};
assert #od0 eq 2;
f_FCl := ChangeRing(f, FCl);
assert d0*f_FCl in od0;

assert InnerProduct((d0)*frobCl, (d0)) eq 2;


// Orbits of size 4
// axes, x
assert {@ ACl.i : i in [1..4] @} in orbs;

assert IsIdempotent(xp);
evals, espace, FL := IdentifyFusionLaw(xp);
assert #FL eq 5;
assert Order(Grading(FL)) eq 2;
assert MiyamotoInvolution(xp) eq f_FCl;

assert exists(ox){o : o in orbs | xp in o};
assert #ox eq 4;
assert xp*f_FCl in ox;
assert InnerProduct(xp*frobCl, xp) eq 10;

// Check for characteristic polynomial matching Monster type

poss := CheckForMatchingCharactisticPoly(ACl.1, orbs);

assert #poss eq 1;
assert poss[1,1] eq xp;
I := poss[1,3];
assert I eq ideal< Integers() |3>;
// So require characteristic 3
// But in this case, bt = -1/4 = -1 and so 2*bt = 1, a contradiction





////////// Nilpotent elements ////////////////////////////////////
A, gens, frob := M4J();
F<bt> := BaseRing(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;

assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

N := NilpotentIdeal(A);
assert VarietySizeOverAlgebraicClosure(N) eq 1;  // so no non-trivial nilpotent elements


// Now bt = -1/4
A, gens, frob := M4J(-1/4);
F := BaseRing(A);

N := NilpotentIdeal(A);
P := Generic(N);

assert Radical(N) eq ideal<P| P.1-P.5,P.2-P.5,P.3-P.5,P.4-P.5>;


