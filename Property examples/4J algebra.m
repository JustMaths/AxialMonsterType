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
A, gen, frob := M4J();
F<bt> := BaseRing(A);

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

A, gen, frob := M4J(-1/4);
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
A, gen, frob := M4J(1/4);
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

A, gen, frob := M4J();
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






































// ---------------------------------------------------
//
// Check for bad primes of reduction for the singular points
//

A, gen, frob := M4A();
// Changing basis makes the equations much nicer and so massively speeds up the Groebner basis
bas := [A.1-A.3,A.2-A.4,A.1+A.3-(A.2+A.4), A.1+A.3+A.2+A.4, A.5];
AA := ChangeBasis(A, bas);

II := IdealOfSingularPoints(AA: base_ring:=Integers());

// We also need to change the monomial ordering for the Groebner basis to help the elimination ideal
// Without the order change it takes 35000secs, with it takes 900.
J := ChangeOrder(II, "elim", 2);

// With the basis and monomial order changes, this takes 900 secs ~ 20 mins
// Without these it won't complete
elim := EliminationIdeal(J, 6);

assert elim = ideal<Generic(elim)|>;

// So there are no bad characteristics
// Hence we can proceed with the analysis in characteristic 0 and will apply to characteristic p (not 2) too.

// ---------------------------------------------------
//
// Check singular locus
//

A, gen, frob := M4J();
II := IdealOfSingularPoints(A);
primII := RadicalDecomposition(II);
P := Generic(II);

assert #primII eq 36;

// NB bt can't be 1/2

// There are exceptional isomorphisms with 4A if bt = 1/8 and with 4Y(1/2, bt) if bt =1/4
// Both of these have infinitely many idempotents, so we can rule these cases out and deal with them in 4A and 4Y

assert #{ J : J in primII | P.6 -1/4 in J or P.6-1/2 in J or P.6-1/8 in J} eq #primII;

// So no special cases we need to check

// ------------------------
//
// Check the generic case

A, gen, frob := M4J();
F<bt> := BaseRing(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;

assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

I := IdempotentIdeal(A);

FCl := AlgebraicClosure(F);
rt1 := Sqrt(FCl!(1-4*bt)*(1+4*bt));
rt2 := Sqrt(FCl!(1-8*bt));

// We need some other roots too
P<t> := PolynomialRing(F);

p4 := t^2 + (1-2*bt)*t + bt^2;
roots := [ r[1] : r in Roots(p4, FCl)];
rt41 := Sqrt(FCl!roots[1]/(12*bt^2-1));
rt42 := Sqrt(FCl!roots[2]/(12*bt^2-1));

p42 := t^4 + (-2*bt + 1)/(12*bt^2 - 1)*t^2 + bt^2/(144*bt^4 - 24*bt^2 + 1);
assert MinimalPolynomial(rt41) eq p42;
assert Set(Conjugates(rt41)) eq { rt41, -rt41, rt42, -rt42};

Simplify(FCl:Partial:=true); // Needed so that the equality checking works below
Prune(FCl);

// ensure that the signs are correct
signs := [+1,-1];

value := bt/(1-12*bt^2);
assert #{ p : p in signs | p*rt41*rt42 eq value} eq 1;
assert exists(p){ p : p in signs | p*rt41*rt42 eq value};

rt42 := p*rt42;
// NB of the four roots, {rt41, rt42} and {-rt41, -rt42} satisfy the signs convention

// So bad values of bt are 1/4, -1/4, 1/8, 1/sqrt{12}
// By above, we do not need to deal with bt = 1/4 or 1/8

ACl := ChangeRing(A, FCl);
frobCl := ChangeRing(frob, FCl);

vars := Variety(I, FCl);
idems := [ ACl![t[i] : i in [1..#t]] : t in vars];

// Simplify takes a long time, but partial is quick
Simplify(FCl:Partial:=true);
Prune(FCl);

GCl := ChangeRing(G, FCl);
orbs := {@ {@ ACl!u : u in Orbit(GCl, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #orbs eq 12;
assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^6 *};

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

rt3 := (1-(1+2*bt)*(rt41+rt42))/2/(1+4*bt);
assert (3+ (2*bt-1)*(rt41+rt42))/(1+4*bt) eq 1/(2*bt+1)*(2 +2*(1-2*bt)*rt3);  // below when bt = -1/4, we can describe the length differently
x := rt3*ACl![1,1,1,1,1] + rt41*(ACl.1+ACl.2) + rt42*(ACl.3+ACl.4);

assert IsIdempotent(x);
evals, espace, FL := IdentifyFusionLaw(x);
assert #FL eq 5;
assert Order(Grading(FL)) eq 2;
assert MiyamotoInvolution(x) eq f_FCl;

assert exists(ox){o : o in orbs | x in o};
assert #ox eq 4;
assert x*f_FCl in ox;
assert InnerProduct(x*frobCl, x) eq (3+ (2*bt-1)*(rt41+rt42))/(1+4*bt);

assert id-x notin ox;
assert exists(ox_pair){o : o in orbs | id - x in o};

// for the pair -rt41 and -rt42 we get 1/(1+4*bt)-rt3
conj3 := (1+(1+2*bt)*(rt41+rt42))/2/(1+4*bt);
assert conj3 eq 1/(4*bt+1) -rt3;
min_rt3 := MinimalPolynomial(rt3);
assert Degree(min_rt3) eq 2;
assert conj3 in Conjugates(rt3);

assert InnerProduct((id-x)*frobCl, (id-x)) eq (3 -(2*bt-1)*(rt41+rt42))/(1+4*bt);

y := 1/2/rt1*( rt2*(ACl.1-ACl.3) + ACl.2+ACl.4 - ACl.5);

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

// Check for more axes
poss := FindMatchingIdempotents(ACl.1,orbs);

assert #poss eq 2;
P<t> := PolynomialRing(F);
assert CharacteristicPolynomial(ACl.1) - CharacteristicPolynomial(orbs[2,1]) eq bt*t*(5*t^3 - (18*bt+5)*t^2 + 2*bt*(8*bt+9)*t - 16*bt^2);
// can't have bt = 0

assert CharacteristicPolynomial(ACl.1) - CharacteristicPolynomial(id-ACl.1) eq (1-2*bt)*t*(3*t^3 - 6*t^2 + (4-bt)*t +bt-1);
// Can't have bt = 1/2

// So no extra axes

// -------------------------------------
//
// Now check the bad values
// as before don't need to check bt = 1/4, 1/8 as the algebra is isomorphic to 4Y and 4A in these cases

// --------------------
//
// bt = -1/4
bt := -1/4;
A, gen, frob := M4J(bt);

F := QQ;
t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;

assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits
I := IdempotentIdeal(A);

FCl := AlgebraicClosure(F);

P<t> := PolynomialRing(F);
// For bt = -1/4, rt1 from above degenerates to be 0

p4 := t^2 + (1-2*bt)*t + bt^2;
roots := [ r[1] : r in Roots(p4, FCl)];
rt41 := Sqrt(FCl!roots[1]/(12*bt^2-1));
rt42 := Sqrt(FCl!roots[2]/(12*bt^2-1));

// The minimal poly for rt41 and rt42 has now degenerated to be a quadratic;
assert MinimalPolynomial(rt41) eq t^2-2*t-1;
assert rt41 ne rt42;
// so we have the two roots of this quadratic
// So we don't need to fix the signs, this holds automatically.

assert rt41*rt42 eq bt/(1-12*bt^2);
assert rt41 + rt42 eq 2;

rt3 := 1;
assert 1/(2*bt+1)*( 1 -2*(1+4*bt)*rt3) eq 2;


Simplify(FCl:Partial:=true); // Needed so that the equality checking works below
Prune(FCl);

ACl := ChangeRing(A, FCl);
frobCl := ChangeRing(frob, FCl);

vars := Variety(I, FCl);
idems := [ ACl![t[i] : i in [1..#t]] : t in vars];

GCl := ChangeRing(G, FCl);
orbs := {@ {@ ACl!u : u in Orbit(GCl, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

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

x := rt3*ACl![1,1,1,1,1] + rt41*(ACl.1+ACl.2) + rt42*(ACl.3+ACl.4);

assert IsIdempotent(x);
evals, espace, FL := IdentifyFusionLaw(x);
assert #FL eq 5;
assert Order(Grading(FL)) eq 2;
assert MiyamotoInvolution(x) eq f_FCl;

assert exists(ox){o : o in orbs | x in o};
assert #ox eq 4;
assert x*f_FCl in ox;
assert InnerProduct(x*frobCl, x) eq 1/(2*bt+1)*(2 +2*(1-2*bt)*rt3);
assert InnerProduct(x*frobCl, x) eq 10;

// check for new axes
poss := FindMatchingIdempotents(ACl.1, orbs);

assert #poss eq 1;
P<t> := PolynomialRing(F);
assert CharacteristicPolynomial(AdjointMatrix(ACl.1)) - CharacteristicPolynomial(AdjointMatrix(x)) eq 3/4*t*(t^3 + 11/2*t^2-3/2*t-5);
// So no new axes

// ---------------------------------
//
// bt = 1/sqrt{12}
//
F := QQ;
FCl := AlgebraicClosure(F);
r := Sqrt(FCl!3);

for sgn in [+1,-1] do
  bt := sgn/2/r;

  rt1 := Sqrt(FCl!(1-4*bt)*(1+4*bt));
  rt2 := Sqrt(FCl!(1-8*bt));
  
  A, gens, frob := M4J(bt);

  t1 := PermutationMatrix(F, [1,4,3,2,5]);
  t2 := PermutationMatrix(F, [3,2,1,4,5]);

  f := PermutationMatrix(F, [2,1,4,3,5]);
  G := sub<GL(5,F) | t1,t2,f>;

  assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

  ACl := ChangeRing(A, FCl);
  frobCl := ChangeRing(frob, FCl);

  I := IdempotentIdeal(ACl);
  assert VarietySizeOverAlgebraicClosure(I) eq 24;

  vars := Variety(I, FCl);
  idems := [ ACl![t[i] : i in [1..#t]] : t in vars];

  // Simplify takes a long time, but partial is quick
  Simplify(FCl:Partial:=true);
  Prune(FCl);

  GCl := ChangeRing(G, FCl);
  orbs := {@ {@ ACl!u : u in Orbit(GCl, Vector(v))@} : v in idems @};
  Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

  // Bug with magma means that this will fail.  But it is missing id-ACl.5 which is clearly an idempotent.
  // Should have 24 idempotents agreeing with variety size above
  // Fails second time through, I think because the field has grown
    
  assert #Set(vars) eq 24;
  assert #orbs eq 10;
  assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^4 *};

  // Orbits of size 1
  // 0, A.5, id and id-A.5
  // need bt \neq -1/4
  so, id := HasOne(ACl);
  assert so;
  assert id eq 1/(4*bt+1)*ACl![1,1,1,1,1];
  assert InnerProduct(id*frobCl, id) eq 6/(4*bt+1);

  assert IsIdempotent(ACl.5);
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
  // axes, id - axes, y and id -y
  assert {@ ACl.i : i in [1..4] @} in orbs;

  assert {@ id-ACl.i : i in [1..4] @} in orbs;
  assert InnerProduct((id-ACl.1)*frobCl, (id-ACl.1)) eq (5-4*bt)/(1+4*bt);


  y := 1/2/rt1*( rt2*(ACl.1-ACl.3) + ACl.2+ACl.4 - ACl.5);

  assert IsIdempotent(id/2+y);
  assert exists(oy){o : o in orbs | id/2+y in o};
  assert #oy eq 4;
  assert (id/2+y)*f_FCl in oy;

  assert id/2-y notin oy;
  assert exists(oy_pair){o : o in orbs | id/2 - y in o};

  assert InnerProduct((id/2+y)*frobCl, id/2+y) eq 3/(4*bt+1);
  assert InnerProduct((id/2-y)*frobCl, (id/2-y)) eq 3/(4*bt+1);
  
  poss := FindMatchingIdempotents(ACl.1, orbs);

  assert #poss eq 2;
  P<t> := PolynomialRing(F);
  p1 := CharacteristicPolynomial(AdjointMatrix(ACl.1)) - poss[1,2];
  assert p1 ne 0;
  p2 := CharacteristicPolynomial(AdjointMatrix(ACl.1)) - poss[2,2];
  assert p2 ne 0;
end for;



////////// Nilpotent elements ////////////////////////////////////
A, gen, frob := M4J();
F<bt> := BaseRing(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;

assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

N := NilpotentIdeal(A);
assert VarietySizeOverAlgebraicClosure(N) eq 1;  // so no non-trivial nilpotent elements


// Now bt = -1/4
A, gen, frob := M4J(-1/4);
F := BaseRing(A);

N := NilpotentIdeal(A);
P := Generic(N);

assert Radical(N) eq ideal<P| P.1-P.5,P.2-P.5,P.3-P.5,P.4-P.5>;


