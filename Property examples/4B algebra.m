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
A, gen, frob := M4B();
F<al> := BaseRing(A);
bt := al^2/2;
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

A, gen, frob := M4B(-1);
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

// ---------------------------------------------------
//
// Check singular locus
//

A, gen, frob := M4B();
II := IdealOfSingularPoints(A);
primII := RadicalDecomposition(II);
P := Generic(II);

assert #primII eq 38;

// For al = 1/2, 4B is isomorphic to 4Y(1/2,1/8) which has infinitely many idempotents.  So we can deal with this case there
bad := [ J : J in primII | P.6-1 notin J and P.6-1/2 notin J];
assert forall{ J : J in primII | P.6+1 in J};

// So al = -1 is a case we need to look at seperately.  NB this is the only case where bt = 1/2.

// ------------------------
//
// Check the generic case

A, gen, frob := M4B();
F<al> := BaseRing(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;

assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

FCl := AlgebraicClosure(F);
// Need to add roots
r := Sqrt(FCl!(al^2-4*al+1)/(al^4-2*al^3-2*al+1));
s := Sqrt(FCl!(1-2*al)/(al^4 - 2*al^3 - 2*al + 1));
A := ChangeRing(A, FCl);
frob := ChangeRing(frob, FCl);
idems := FindAllIdempotents(A);
Simplify(FCl);
Prune(FCl);
// Need to check al = 1/2 and roots of al^2-4*al+1, al^4-2*al^3-2*al+1


G := ChangeRing(G, FCl);
orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #orbs eq 12;
assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^6 *};

// Orbits of size 1
// need al \neq -1
// There is the zero vector, and A.5, id and id-A.5
so, id := HasOne(A);


assert HasJordanFusionLaw(A.5: fusion_value:=al);
assert Dimension(Eigenspace(A.5, 0)) eq 2;
assert Dimension(Eigenspace(A.5, al)) eq 2;
assert MiyamotoInvolution(A.5) eq t1*t2;

assert HasJordanFusionLaw(id-A.5: fusion_value:=1-al);
assert Dimension(Eigenspace(id-A.5, 1)) eq 2;
assert Dimension(Eigenspace(id-A.5, 1-al)) eq 2;
assert MiyamotoInvolution(A.5) eq t1*t2;

assert InnerProduct(id*frob, id) eq (-al + 5)/(al + 1);
assert InnerProduct(A.5*frob, A.5) eq 1;
assert InnerProduct((id-A.5)*frob, (id-A.5)) eq (-2*al + 4)/(al + 1);




// Orbits of size 2
// Each 3C subalgebra has its own identity id_3C and then id_3C - A.5
id_3C := 1/(al+1)*(A.1+A.3+A.5);
assert IsIdempotent(id_3C);
assert HasJordanFusionLaw(id_3C: fusion_value:=al);
assert Dimension(Eigenspace(id_3C, 1)) eq 3;
assert MiyamotoInvolution(id_3C) eq t1;

assert id - id_3C eq (id_3C)*ChangeRing(f, FCl) -A.5;
assert IsIdempotent(id_3C-A.5);
assert HasJordanFusionLaw(id_3C-A.5: fusion_value:=1-al);
assert Dimension(Eigenspace(id_3C-A.5, 0)) eq 3;
assert MiyamotoInvolution(id_3C-A.5) eq f*t1*f;

assert InnerProduct(id_3C*frob, id_3C) eq (3)/(al + 1);
assert InnerProduct((id-id_3C)*frob, (id-id_3C)) eq (2-al)/(al + 1);


// orbits of size 4
// the axes, id - axes
// there is also the orbit of x := id_3C - A.1 and id - x
x := id_3C - A.1;
assert IsIdempotent(x);
assert HasMonsterFusionLaw(x: fusion_values:=[1-al, al-bt]);
assert Dimension(Eigenspace(x, 0)) eq 2;
assert MiyamotoInvolution(x) eq t1;

// Final two orbits: y and id-y
y := id/2 + r/2/(al+1)*A![al, al, al, al, -1-al^2] + s/2*A![-1,-1,1,1,0];
assert IsIdempotent(y);
evals, espace, FL := IdentifyFusionLaw(y);
assert #FL eq 5;
assert Order(Grading(FL)) eq 2;
assert MiyamotoInvolution(y) eq f;

assert InnerProduct((id-A.1)*frob, (id-A.1)) eq (4-2*al)/(al + 1);
assert InnerProduct((x)*frob, (x)) eq (2-al)/(al + 1);
assert InnerProduct((id-x)*frob, (id-x)) eq (3)/(al + 1);

assert InnerProduct((y)*frob, (y)) eq (5-al-r*(al^2-4*al+1))/2/(al + 1);
assert InnerProduct((id-y)*frob, (id-y)) eq (5-al+r*(al^2-4*al+1))/2/(al + 1);

// -------------------
//
// Check for new axes
poss := FindMatchingIdempotents(A.1,orbs);

assert #poss eq 2;
P<t> := PolynomialRing(F);
assert CharacteristicPolynomial(AdjointMatrix(A.1))-poss[1,2] eq al*(2-al)/2*t^2*(t^2 - (al+1)*t +al);
// but al neq 1, 2

assert CharacteristicPolynomial(AdjointMatrix(A.1))-poss[2,2] eq (1-al)*t*( (al+3)*t^3 - 2*(al+3)*t^2 + (4-al)*(al + 2)/2*t +(al^2-2)/2);
// but al neq 1

// So no new axes

//  -------------------------------------
//
// Need to check the exceptional cases, which are:
//
// al = -1, 1/2 and roots of al^2-4*al+1, al^4-2*al^3-2*al+1

// --------------------
//
// al = -1

al := -1;
F := QQ;

A, gen, frob := M4B(al);

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
// So this is indeed an idempotent

P<t> := PolynomialRing(F);
assert CharacteristicPolynomial(AdjointMatrix(x)) eq t^2*(t+1)*(t-1)*(t-1/2) -3/4*(lm^2+mu^2-1)*t^2*(t -1/2);

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

assert ubt*ubt eq 3/2*x + 1/2*u02 +1/2*(7*mu^2-3)*u01 -3/4*ual;
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

assert ubt*ubt eq 3/2*x + 1/2*u02 +1/2*(7*mu^2-3)*u01 -3/4*ual;
// This is always in {1, 0, al}

// So for Monster type, we require lm = 0, mu = \pm 1, or lm = \pm 1, mu = 0.
// This gives exactly a0, a1, a2, a_-1


// -----------------
//
// al = 1/2
// Don't need to do this as the algebra is isomorphic to 4Y here

al := 1/2;
F := QQ;

A, gen, frob := M4B(al);

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
assert ideal<P | [P.i-2/3 : i in [1..4]] cat [P.5-1/3]> in prim0;

// These are 0 and the identity
so, id := HasOne(A);
assert so;
assert id eq 1/3*A![2,2,2,2,1];

assert #prim1 eq 4;

// These two ideals lie in the subalgebras <a_0, a_2, c> and <a,1, a_-1,c> which are both isomorphic to 3C(1/2) \cong S(-1)
// We know this has infinitely many idempotents
so, id3C := HasOne(sub<A|A.1,A.3>);
assert so;
assert id3C eq 2/3*(A.1+A.3+A.5);
// Idempotents have the form 1/2(id + u) where u has b(u,u) = 2
e := 2/3*(2*A.1-A.3-A.5);
f := 2/3*(2*A.3-A.1-A.5);

assert A.1 eq 1/2*(id3C + e);
assert A.3 eq 1/2*(id3C + f);
// idempotents have the form 1/2(lm e + mu f + id3C) where lm^2 + mu^2 - lm*mu = 1
// this is 1/3*( (2lm -mu+1) a_0 + (2mu -lm+1)a_2 + (1-lm-mu)c)
// Can see that the sum of the coefficients is 1,
// so we get P.1+P.3+P.3-1 is a relation
// also lm = (P.1-P.5)
// mu = (P.3-P.5)

J0 := ideal<P | P.2, P.4, P.1+P.3+P.5-1, (P.1-P.5)^2 + (P.3-P.5)^2 - (P.1-P.5)*(P.3-P.5) -1>;
assert J0 in prim1;

// we have identity minus this
// id = 1/3*A![2,2,2,2,1];
// so replace P.1 with 2/3-P.1,  and P.5 with 1/3-P.5
J0pair := ideal<P | 2/3-P.2, 2/3-P.4, (2/3-P.1)+(2/3-P.3)+(1/3-P.5)-1, (P.1-P.5-1/3)^2 + (P.3-P.5-1/3)^2 - (P.1-P.5-1/3)*(P.3-P.5-1/3) -1>;
assert J0pair in prim1;

// Now have the same for the subalgebra <a1, a_{-1}, c>, so we get the other two

F<lm,mu> := PolynomialRing(QQ, 2);
F<lm,mu>, phi := quo<F|lm^2+mu^2-lm*mu-1>;
AF := ChangeRing(A, F);

x := 1/3*( (2*lm-mu+1)*AF.1 + (2*mu-lm+1)*AF.3 + (1-lm-mu)*AF.5);

//assert x^2 eq x + 1/6*(lm^2+mu^2-lm*mu-1)*(AF.1 + AF.3 +AF.5);

assert IsIdempotent(x);

P<t> := PolynomialRing(F);

//assert CharacteristicPolynomial(AdjointMatrix(x)) eq t^2*(t-1)*(t+ 1/8*(lm+mu-2))*(t-1/2) - 1/4*(lm^2+mu^2-lm*mu-1)*t*( t^2 +1/8*(lm+mu-6)*t -1/16*(lm+mu-2));

assert CharacteristicPolynomial(AdjointMatrix(x)) eq t^2*(t-1)*(t + 1/8*(lm+mu-2))*(t-1/2); 

// For this to be Monster type (1/2, 1/8), we require lm+mu-2 = -1, ie lm+mu =1
// Using lm^2 + mu^2 -lm*mu = 1, we get
// this gives lm=1, mu=0, or lm=0, mu=1
// Which are a_0 and a_2

// Check the id-x
id := AF!Eltseq(id);
assert CharacteristicPolynomial(AdjointMatrix(id-x)) eq (t-1)^2*t*(t - 1/8*(lm+mu+6))*(t-1/2); 
// So this can't be of Monster type as the axis is not primitive.


// --------------------------------------
//
// roots of al^2-4*al+1
F := QQ;
FCl := AlgebraicClosure(F);

P<t> := PolynomialRing(F);

p := t^2-4*t+1;
roots := [ r[1] : r in Roots(p, FCl)];

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
  assert VarietySizeOverAlgebraicClosure(I) eq 28;

  s := Sqrt(FCl!(1-2*al)/(al^4 - 2*al^3 - 2*al + 1));
  
  idems := {@ A![t[i] : i in [1..#t]] : t in Variety(I, FCl) @};

  Simplify(FCl);
  Prune(FCl);

  // Bug with magma means that this will fail.  But it is missing id-ACl.5 which is clearly an idempotent.
  // Should have 28 idempotents agreeing with variety size above
  // Fails second time through, I think because the field has grown
  assert #idems eq 28;

  G := ChangeRing(G, FCl);
  orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
  Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

  assert #orbs eq 11;
  assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^5 *};

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

  y := id/2 +s/2*(A.1+A.2) - s/2*(A.3+A.4);

  assert IsIdempotent(y);
  assert exists(oy){ o : o in orbs | y in o};
  assert id-y in oy;
  assert InnerProduct((y)*frob, (y)) eq (5-al)/2/(al + 1);
  // This is equivalent to r being 0 in the definition in the generic case.
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
A, gen, frob := M4B(-1);

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





