/*
******************************

Code to verify properties of the 4B(al, al^2/2) algebra

******************************
*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";

QQ := Rationals();

// =========================================================
//
// 4B(al, al^2/2)
//
// =========================================================
A, gens, frob := M4B();
F<al> := BaseRing(A);
bt := al^2/2;

// Confirm the algebra is indeed a 2-generated Monster type algebra

assert sub<A | gens> eq A;
assert HasMonsterFusionLaw(gens[1]: fusion_values:=[al, bt]);
assert HasMonsterFusionLaw(gens[2]: fusion_values:=[al, bt]);
assert IsFrobeniusForm(frob, A);

// We have al \neq 2 as bt = 2^2/2 = 2 = al

// identity
so, id := HasOne(A);
assert so;
assert id eq A![1,1,1,1,1-al]/(al+1);
// so algebra has an identity iff al \neq -1

// <<a_0, a_2 >> = 3C(al)
assert Dimension(sub<A|A.1,A.3>) eq 3;
c := -2/al*(A.1*A.3 - al/2*(A.1+A.3));
assert c eq A.5;
assert c^2 eq c;
assert c in sub<A|A.1,A.3> meet sub<A|A.2,A.4>;

assert frob[1,2] eq al^2/4;
assert frob[1,3] eq al/2;
// So the projection graph is always the complete graph

assert Determinant(frob) eq 1/16*(al-2)^4*(al+1)^2;
// Since the characteristic is not 2 and al \neq 2, just need to check al = -1

A, gens, frob := M4B(-1);
// Note that char \neq 3 as then bt = (-1)^2/2 = 1/2 = -1 = al

// no identity
assert not HasOne(A);

P<lm> := PolynomialRing(QQ);
assert CharacteristicPolynomial(frob) eq lm^2*(lm-3/2)^2*(lm-2);
// Since char \neq 3, Radical has dimension at most 2 in any char.

R := NullSpace(frob);
assert Dimension(R) eq 2;

r1 := A![1,0,1,0,1];
r2 := A![0,1,0,1,1];
assert Vector(r1) in R;
assert Vector(r2) in R;
// the radical is spanned by the annihilators in the two 3C(-1) algebras

// moreover, the radical is the annihilator
ann := Annihilator(A);
assert r1 in ann and r2 in ann;

// clearly the subalgebra intersection is not contained in R
int := sub<A|A.1,A.3> meet sub<A|A.2,A.4>;
assert int.1 eq A.5;
assert A!int.1 notin R;

// Since the radical is the annihilator, every 1-dimensional subspace is an ideal.
// The extra symmetry automorphism maps r1 to r2, so there are only two SYMMETRIC subideals in R

// We have 4B(-1,1/2)^x
I1 := ideal<A|r1+r2>;
assert Dimension(I1) eq 1;

// Second symmetric quotient
I2 := ideal<A|r1-r2>;
assert Dimension(I2) eq 1;

B, quo := quo<A|I2>;

n := B![1,0,1,1];
z1 := B.4;
e := B![1,0,-1,0];
f := B![-1,2,-1,0];

assert z1^2 eq z1;
assert forall{x:x in [n,z1,e,f]|x*n eq 0};
assert e*z1 eq -e;
assert f*z1 eq -f;
assert e*f eq 0;

assert 1/2*(e-z1+n) eq A.1@quo;
assert 1/2*(f-z1+n) eq A.2@quo;

// This is the multiplication for IY_3(-1,1/2,0) = \widehat{S}(b, -1)^\circ. Hence, B is isomorphic to IY_3(-1,1/2,0).

// It is clear that n is the Ann for this algebra, and it is known that the algebra has a quotient IY_3(-1,1/2,0)^x = S(b, -1)^\circ;
assert n eq r1@quo;


// An example of a 1-dimensional ideal giving a non-symmetric quotient
B, quo := quo<A|R.1>;
so, id := HasOne(B);

// Check the images of a_0 and a_1 to see that they have slightly different fusion laws (both subsets of the Monster), so the ideal is non-symmetric.  Similarly for R.2 and hence any 1-dim ideal in R gives a non-symmetric quotient

//------------------------------

// Idempotents

//------------------------------

// These are some calculations which support a theoretical proof

A, gens, frob := M4B();
F<al> := BaseRing(A);

bas := [A.1-A.3,A.2-A.4,A.1+A.3-al*A.5, A.2+A.4-al*A.5, A![1,1,1,1,1-al]];
AA := ChangeBasis(A, bas);

I := IdempotentIdeal(AA);

P<lm0,lm1,mu0,mu1,nu> := Generic(I);

P0 := 2*(1-al^2)*mu0 + 2*(al+1)*nu - 1;
P1 := 2*(1-al^2)*mu1 + 2*(al+1)*nu - 1;
Q0 := (al+1)*mu0 + 2*(al+1)*nu - 1;
Q1 := (al+1)*mu1 + 2*(al+1)*nu - 1;

assert Basis(I) eq [ lm0*P0, lm1*P1, (1-2*al)/(al+1)*lm0^2 + al*(al-2)/(al+1)*lm1^2 + mu0*Q0,
                                     (1-2*al)/(al+1)*lm1^2 + al*(al-2)/(al+1)*lm0^2 + mu1*Q1,
                                     -al*(al-2)/(al+1)*(lm0^2 + lm1^2) + nu*((al+1)*nu-1)];


// Check the orbits and lengths

// --------------------------
//
// For  al \neq -1

FCl := AlgebraicClosure(F);
// Need to add roots
rt1 := Sqrt(FCl!(al^2-4*al+1)/(al^4-2*al^3-2*al+1));
rt2 := Sqrt(FCl!(1-2*al)/(al^4 - 2*al^3 - 2*al + 1));

I := IdempotentIdeal(AA); 
assert #Variety(I, FCl) eq 32;

Simplify(FCl);
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

y := rt1/2/(al+1)*ACl![al, al, al, al, -1-al^2] + rt2/2*ACl![1,1,-1,-1,0];

assert id/2+y eq rt2/2*( (ACl.1-ACl.3) + (ACl.2-ACl.4)) + rt1/2/(al+1)*(ACl![1,0,1,0,-al] + ACl![0,1,0,1,-al]) + (1-(1-al)*rt1)/2/(al+1)*ACl![1,1,1,1,1-al];

// The complete set of idempotents

so, id02 := HasOne(sub<ACl|ACl.1,ACl.3>);
id02 := ACl!id02;

idems := [ ACl!0, ACl.5, ACl.1, id, id - ACl.5, id02, id - id02, id - ACl.1, id02-ACl.1, id - (id02-ACl.1), id/2+y, id/2-y];

orbs := {@ {@ ACl!u : u in Orbit(GCl, Vector(v))@} : v in idems @};  // Need to have found the order for Orbit to work
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

// So we have all the idempotents
assert #orbs eq 12;
assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^6 *};
assert #(&join orbs) eq 32;

// We now check for properties of the idempotents


// Orbits of size 1
// There is the zero vector, and A.5, id and id-A.5

// need al \neq -1
assert id eq 1/(al+1)*ACl![1,1,1,1,1-al];
assert InnerProduct(id*frobCl, id) eq (5 - al)/(al + 1);

assert HasJordanFusionLaw(A.5: fusion_value:=al);
assert Dimension(Eigenspace(A.5, 0)) eq 2;
assert Dimension(Eigenspace(A.5, al)) eq 2;
assert MiyamotoInvolution(A.5) eq t1*t2;

assert InnerProduct(ACl.5*frobCl, ACl.5) eq 1;

assert HasJordanFusionLaw(id-ACl.5: fusion_value:=1-al);
assert Dimension(Eigenspace(id-ACl.5, 1)) eq 2;
assert Dimension(Eigenspace(id-ACl.5, 1-al)) eq 2;
assert MiyamotoInvolution(ACl.5) eq t1*t2;

assert InnerProduct((id-ACl.5)*frobCl, (id-ACl.5)) eq 2*(2 - al)/(al + 1);


// Orbits of size 2
// Each 3C subalgebra has its own identity.  For <<a0, a2>> we have id02 and then id02 - A.5
assert id02 eq 1/(al+1)*(ACl.1+ACl.3+ACl.5);
assert IsIdempotent(id02);

assert exists(oid02){o : o in orbs | id02 in o};
assert #oid02 eq 2;

assert InnerProduct(id02*frobCl, id02) eq 3/(al + 1);

assert HasJordanFusionLaw(id02: fusion_value:=al);
assert Dimension(Eigenspace(id02, 1)) eq 3;
assert MiyamotoInvolution(id02) eq t1;

// id - id02
assert id - id02 eq (id02)*ChangeRing(f, FCl) -ACl.5;
assert IsIdempotent(id02-ACl.5);
assert id02 - ACl.5 eq id - id02*ChangeRing(f, FCl);

assert exists(oidmid02){o : o in orbs | id-id02 in o};
assert #oidmid02 eq 2;
assert id02 notin oidmid02;

assert InnerProduct((id-id02)*frobCl, (id-id02)) eq (2-al)/(al + 1);

assert HasJordanFusionLaw(id02-ACl.5: fusion_value:=1-al);
assert Dimension(Eigenspace(id02-ACl.5, 0)) eq 3;
assert MiyamotoInvolution(id02-ACl.5) eq f*t1*f;

// orbits of size 4
// the axes, id - axes
// there is also the orbit of x := id02 - A.1 and id - x

assert InnerProduct((id-ACl.1)*frobCl, (id-ACl.1)) eq 2*(2-al)/(al + 1);

// id02 - a_0
x := id02 - ACl.1;
assert IsIdempotent(x);

assert exists(ox){o : o in orbs | x in o};
assert #ox eq 4;

assert InnerProduct(x*frobCl, x) eq (2-al)/(al + 1);

assert HasMonsterFusionLaw(x: fusion_values:=[1-al, al-bt]);
assert Dimension(Eigenspace(x, 0)) eq 2;
assert MiyamotoInvolution(x) eq t1;

assert exists(oidmx){o : o in orbs | id-x in o};
assert #oidmx eq 4;
assert id - x notin ox;

assert InnerProduct((id-x)*frobCl, (id-x)) eq 3/(al + 1);


// Final two orbits: y and id-y
assert IsIdempotent(id/2 + y);

assert exists(oyp){o : o in orbs | id/2+y in o};
assert #oyp eq 4;

evals, espace, FL := IdentifyFusionLaw(id/2 + y);
assert #FL eq 5;
assert Order(Grading(FL)) eq 2;
assert MiyamotoInvolution(id/2 + y) eq f;

assert IsIdempotent(id/2 - y);
assert exists(oym){o : o in orbs | id/2-y in o};
assert #oym eq 4;
assert id/2-y notin oyp;

assert InnerProduct((id/2 + y)*frobCl, (id/2 + y)) eq (5-al-rt1*(al^2-4*al+1))/2/(al + 1);
assert InnerProduct((id/2 - y)*frobCl, (id/2 - y)) eq (5-al+rt1*(al^2-4*al+1))/2/(al + 1);

// -------------------
//
// Check for characteristic polynomial matching Monster type

poss := CheckForMatchingCharactisticPoly(ACl.1, orbs);

assert #poss eq 4;

// Check each case

assert poss[1,1] eq ACl.5;
I := poss[1,3];
// There is only one variable and it corresponds to al
P<t> := Generic(I);
assert Basis(I) eq [ t*(t-2) ];
// but al is not 0, or 2


I := poss[2,3];
// There is only one variable and it corresponds to al
P<t> := Generic(I);
assert Basis(I) eq [ t^2 + 2, 2*t, 4];
// The characteristic is not 2 (The only solution here is char = 2 and so then al = 0)

// The next two cases involve the root
assert poss[3,1] eq id/2+y;
I := poss[3,4]; P := Generic(I);
assert poss[3,3] eq [* <rt1, P.1>, <al, P.2> *];
// Two variables, rt1 and al
assert Basis(I) eq [ 3*(P.1^2 -1), 3*(P.1 - 1)*(P.2 + 1), 12*(P.1-1), (P.2 - 2)*(P.2 + 1) ];
// From the last equation, either al = 2, a contradiction, or al = -1
// But we are in the al \neq -1 case

// Same as for the last case
assert poss[4,1] eq id/2-y;
I := poss[4,4]; P := Generic(I);
assert poss[4,3] eq [* <rt1, P.1>, <al, P.2> *];
assert Basis(I) eq [ 3*(P.1^2 -1), 3*(P.1 + 1)*(P.2 + 1), 12*(P.1+1), (P.2 - 2)*(P.2 + 1) ];
// This is exactly as above, except for rt1 being -rt1
// Same contradiction as before
 
// So no new Monster type axes in any characteristic, or for any values of the parameters al \neq -1, 1/2


//  -------------------------------------
//
// Need to check the exceptional cases, which are:
//
// al = -1, 1/2 and roots of al^2-4*al+1, al^4-2*al^3-2*al+1

// when al = 1/2, 4B(al, bt) is isomorphic to 4Y(1/2,bt) and the idempotents for this are known
// --------------------
//
// al = -1

al := -1;
F := QQ;

A, gens, frob := M4B(al);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;

assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

I := IdempotentIdeal(A);

assert Dimension(I) eq 1;

prim := RadicalDecomposition(I);

prim0 := [ J : J in prim | Dimension(J) eq 0];
prim1 := [ J : J in prim | Dimension(J) ne 0];

P := Generic(I);
assert #prim0 eq 2;
assert ideal<P | [P.i : i in [1..5]]> in prim0;
assert ideal<P | [P.i : i in [1..4]] cat [P.5-1]> in prim0;

// This corresponds to the zero vector and A.5 = c

assert #prim1 eq 1;
J := prim1[1];

assert P.1+P.2+P.3+P.4-1 in J;

// These idempotents come from the quotient

ep := A.1-A.3;
fp := A.2-A.4;
z1p := A.5;
np := A.2+A.4+A.5;

r := A.1-A.2+A.3-A.4;

// r is in the annihilator, so just need to check the other products
assert ep^2 eq 2*np - 3*z1p + 2*r;
assert ep*fp eq 0;
assert ep*z1p eq -ep;
assert ep*np eq 0;

assert fp^2 eq 2*np - 3*z1p;
assert fp*z1p eq -fp;
assert fp*np eq 0;

assert z1p^2 eq z1p;
assert z1p*np eq 0;

assert np^2 eq 0;

F<lm,mu> := FunctionField(QQ, 2);
AF := ChangeRing(A, F);

x := 1/2*(lm*AF!Eltseq(ep) + mu*AF!Eltseq(fp) + AF.2+AF.4)+ lm^2/2*AF!Eltseq(r);

assert x^2 - x eq -3/4*(lm^2+mu^2-1)*AF!Eltseq(z1p) + 1/2*(lm^2+mu^2-1)*AF!Eltseq(np);
// So this is indeed an idempotent whenever lm^2+mu^2 = 1

P<t> := PolynomialRing(F);
assert CharacteristicPolynomial(AdjointMatrix(x)) eq t^2*(t+1)*(t-1)*(t-1/2) -3/4*(lm^2+mu^2-1)*t^2*(t -1/2);
// So they always have the correct char poly for Monster type

u01 := AF!Eltseq(r);
u02 := AF!Eltseq(np);
ual := lm*AF!Eltseq(ep) + mu*AF!Eltseq(fp) + 3*AF!Eltseq(z1p) -AF!Eltseq(np) - lm^2*AF!Eltseq(r);
ubt := mu*AF!Eltseq(ep) - lm*AF!Eltseq(fp) + 2*lm*mu*AF!Eltseq(r);

assert x*u01 eq 0;
assert x*u02 eq 0;
assert x*ual eq -ual + (lm^2+mu^2-1)*AF![0,1,0,1,-1/2];
assert x*ubt eq 1/2*ubt;

// Check the fusion law
// Both n and r are in the annihilator
// so just need to check al*al, al*bt and bt*bt

assert ual*ual eq -12*x + 8*u02 + 8*lm^2*u01 + (lm^2+mu^2-1)*( 2*(AF.2+AF.4) - AF.5 );
// This is always in { 1, 0}

assert ual*ubt eq -3*ubt + 8*lm*mu*u01;
// from this we require lm = 0, or mu = 0 for it to be of Monster type
// In particular, this breaks the grading unless this is true, so we don't get another automorphism

assert ubt*ubt eq 3/2*(lm^2 + mu^2)*x + 1/2*(lm^2 + mu^2)*u02 + (2*mu^2 -3/2*lm^2*(lm^2 + mu^2))*u01 -3/4*(lm^2 + mu^2)*ual;
// This is always in {1, 0, al}

// So for Monster type, we require lm = 0, mu = \pm 1, or lm = \pm 1, mu = 0.
// This gives exactly a0, a1, a2, a_-1

// So all the characteristic polys are the same and we have infinitely many new axes.

F<lm,mu> := PolynomialRing(QQ, 2);
F<lm,mu>, phi := quo<F|lm^2+mu^2-1>;
AF := ChangeRing(A, F);

x := 1/2*(lm*AF!Eltseq(ep) + mu*AF!Eltseq(fp) + AF.2+AF.4)+ lm^2/2*AF!Eltseq(r);

assert IsIdempotent(x);

P<t> := PolynomialRing(F);
assert CharacteristicPolynomial(AdjointMatrix(x)) eq t^2*(t-1)*(t+1)*(t-1/2);

u01 := AF!Eltseq(r);
u02 := AF!Eltseq(np);
ual := lm*AF!Eltseq(ep) + mu*AF!Eltseq(fp) + 3*AF!Eltseq(z1p) -AF!Eltseq(np) - lm^2*AF!Eltseq(r);
ubt := mu*AF!Eltseq(ep) - lm*AF!Eltseq(fp) + 2*lm*mu*AF!Eltseq(r);

assert x*u01 eq 0;
assert x*u02 eq 0;
assert x*ual eq -ual;
assert x*ubt eq 1/2*ubt;

assert ual*ual eq -12*x + 8*u02 + 8*lm^2*u01;
// This is always in { 1, 0}

assert ual*ubt eq -3*ubt + 8*lm*mu*u01;
// from this we require lm = 0, or mu = 0 for it to be of Monster type
// In particular, this breaks the grading unless this is true, so we don't get another automorphism

assert ubt*ubt eq 3/2*x + 1/2*u02 +(2*mu^2 -3/2*lm^2)*u01 -3/4*ual;
// This is always in {1, 0, al}

// So for Monster type, we require lm = 0, mu = \pm 1, or lm = \pm 1, mu = 0.
// This gives exactly a0, a1, a2, a_-1


// --------------------------------------
//
// roots of al^2-4*al+1
F := QQ;
FCl := AlgebraicClosure(F);

P<t> := PolynomialRing(F);

p := t^2-4*t+1;
roots := [ r[1] : r in Roots(p, FCl)];

for al in roots do
  I := IdempotentIdeal(A);
  assert Dimension(I) eq 0;
  assert VarietySizeOverAlgebraicClosure(I) eq 28;

  A, gens, frob := M4B(al);
  so, id := HasOne(A);
  so, id02 := HasOne(sub<A|A.1,A.3>);
  id02 := A!id02;

  rt2 := Sqrt(FCl!(1-2*al)/(al^4 - 2*al^3 - 2*al + 1));
  y := rt2/2*A![1,1,-1,-1,0];

  idems := [ A!0, A.5, A.1, id, id - A.5, id02, id - id02, id - A.1, id02-A.1, id - (id02-A.1), id/2+y ];

  t1 := MiyamotoInvolution(A.1);
  t2 := MiyamotoInvolution(A.2);
  f := PermutationMatrix(F, [2,1,4,3,5]);
  G := sub<GL(5,F) | t1,t2,f>;

  assert Order(G) eq 8;
  GCl := ChangeRing(G, FCl);

  orbs := {@ {@ A!u : u in Orbit(GCl, Vector(v))@} : v in idems @};  // Need to have found the order for Orbit to work
  Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

  // So we have all the idempotents
  assert #orbs eq 11;
  assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^5 *};
  assert #(&join orbs) eq 28;

  assert IsIdempotent(id/2+y);
  assert exists(oy){ o : o in orbs | id/2+y in o};
  assert id/2-y in oy;  // The two orbits have collapsed into one
  assert InnerProduct((id/2+y)*frob, (id/2+y)) eq (5-al)/2/(al + 1);
  evals, espace, FL := IdentifyFusionLaw(id/2+y);
  Gr, gr := Grading(FL);
  assert Order(Gr) eq 2;
  assert MiyamotoInvolution(id/2+y) eq f;
end for;

// --------------------------------
//
// roots of al^4-2*al^3-2*al+1

F := QQ;
FCl := AlgebraicClosure(F);

P<t> := PolynomialRing(F);

p := t^4 -2*t^3 -2*t+1;
roots := [ r[1] : r in Roots(p, FCl)];

Simplify(FCl);
Prune(FCl);

for r in roots do
  al := r;
  
  A, gens, frob := M4B(al);
  t1 := MiyamotoInvolution(A.1);
  t2 := MiyamotoInvolution(A.2);

  f := PermutationMatrix(F, [2,1,4,3,5]);
  G := sub<GL(5,F) | t1,t2,f>;

  assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

  I := IdempotentIdeal(A);
  assert Dimension(I) eq 0;
  assert VarietySizeOverAlgebraicClosure(I) eq 24;

  idems := {@ A![t[i] : i in [1..#t]] : t in Variety(I, FCl) @};

  // Bug with magma means that this will fail.  But it is missing id-ACl.5 which is clearly an idempotent.
  // Should have 24 idempotents agreeing with variety size above
  // Fails second time through, I think because the field has grown
  assert #idems eq 24;

  G := ChangeRing(G, FCl);
  orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
  Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

  assert #orbs eq 10;
  assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^4 *};

  // Orbits of size 1
  // need al \neq -1
  // There is the zero vector, and A.5, id and id-A.5
  so, id := HasOne(A);
  assert so;
  assert IsIdempotent(A.5);

  // Orbits of size 2
  // Each 3C subalgebra has its own identity id_3C and then id_3C - A.5
  id_3C := 1/(al+1)*(A.1+A.3+A.5);
  assert IsIdempotent(id_3C);
  assert IsIdempotent(id_3C-A.5);

  // orbits of size 4
  // the axes, id - axes
  // there is also the orbit of x := id_3C - A.1 and id - x
  x := id_3C - A.1;
  assert IsIdempotent(x);
  assert IsIdempotent(id-x);
end for;


////////////       Nilpotent elements     //////////////////////////////////
A, gens, frob := M4B();
FCl := AlgebraicClosure(BaseRing(A));

N := NilpotentIdeal(A);
assert Variety(Radical(N), FCl) eq [<0,0,0,0,0>];

//------------------------------
// check al = -1
A, gens, frob := M4B(-1);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(QQ, [2,1,4,3,5]);
G := sub<GL(5,QQ) | t1,t2,f>;

I := IdempotentIdeal(A);
P := Generic(I);
assert Dimension(I) eq 1;

prim := PrimaryDecomposition(I);    
assert #prim eq 3;

prim0 := [ J : J in prim | Dimension(J) eq 0];
prim1 := [ J : J in prim | Dimension(J) ne 0];

// There are two idempotents in the dim 0 part
FCl := AlgebraicClosure(QQ);
assert Set(&cat [ Variety(J, FCl) : J in prim0 ]) eq {<0,0,0,0,0>, <0,0,0,0,1>};

assert #prim1 eq 1;
// This comes from the nilpotent elements in the quotient IY3(-1,1/2,0)
// can do similar to above, but haven't





