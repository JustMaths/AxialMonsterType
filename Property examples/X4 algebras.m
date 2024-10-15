/*

Code to verify properties of the 2-generated axial algebras of Monster type

*/
AttachSpec("2-gen Monster.spec");
AttachSpec("../AxialTools/AxialTools.spec");

QQ := Rationals();
ZZ := Integers();
/*
******************************

X(4) axet

Look in the survey paper folder for other code!!

******************************
*/
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

so, id := HasOne(B);
assert so;
assert id eq B![0,0,4/(bt-1/2)];
// Need bt not 1/2 to have an identity
assert B.1*B.2-(B.1+B.2)/2 eq (bt-1/2)*id;
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
assert Dimension(NullSpace(frob)) eq 2;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
u := A.1-A.2+A.3-A.4;
assert u in R and A.5 in R;

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
assert B.1*B.2-(B.1+B.2)/2 eq -id/4;
// Hence B is S(0) as 1/8(0-2) = -1/4

// A.5 spans the annihilator of the algebra
assert forall{i  : i in [1..5] | A.i*A.5 eq 0};
I := ideal<A|A.5>;
assert Dimension(I) eq 1;

// This is Yabe's quotient 4A(1/4,1/2)^x
// This is of Monster type
B, quo := quo<A|I>;

// There are no other ideals except these
// as A.5 spans the annihilator and
assert u*u eq 8*A.5;



// =========================================================
//
// 4B(al, al^2/2)
//
// =========================================================
A, gen, frob := M4B();
F<al> := BaseRing(A);
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

// no identity
assert not HasOne(A);

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
e := B![1,0,1,0];
f := B![-1,2,-1,0];
// Can check that this is IY_3(-1,1/2,0)^x = \widehat{S}(b, -1)^\circ;

// An example of a 1-dimensional ideal giving a non-symmetric quotient
B, quo := quo<A|R.1>;
so, id := HasOne(B);

// Check the images of a_0 and a_1 to see that they have slightly different fusion laws (both subsets of the Monster), so the ideal is non-symmetric.  Similarly for R.2 and hence any 1-dim ideal in R gives a non-symmetric quotient



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
x := A.1+A.3;
y := A.2+A.4;
assert HasMonsterFusionLaw(x: fusion_values := {@ 4*bt, 2*bt@});
assert HasMonsterFusionLaw(x: fusion_values := {@ 4*bt, 2*bt@});
// They have Monster type (4bt, 2bt)
// NB need bt ne 1/4

B, inc := sub<A|x,y>;
assert Eigenvalues(B!x) eq {<1,1>, <0,1>, <4*bt,1>};
assert Eigenvalues(B!y) eq {<1,1>, <0,1>, <4*bt,1>};
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

// no identity
assert not HasOne(A);

R := NullSpace(frob);
assert Dimension(R) eq 1;
assert A!R.1 eq A![1,1,1,1,1];

// The radical is the annihilator
ann := Annihilator(A);
assert A!R.1 eq ann.1;

// Quotient is 4J(-1/2, -1/4)^x
B, quo := quo<A|R.1>;


// Check double axes for bt = 1/4
A, gen, frob := M4J(1/4);
// Check double axes
x := A.1+A.3;
y := A.2+A.4;
assert HasJordanFusionLaw(x: fusion_value := 1/2);
assert HasJordanFusionLaw(y: fusion_value := 1/2);
// They are Jordan 1/2 axes with a 3-dim 1-space
assert Dimension(Eigenspace(x,1)) eq 3;
assert Dimension(Eigenspace(y,1)) eq 3;

B, inc := sub<A|x,y>;
assert Dimension(B) eq 3;
assert IsAssociative(B);
// It is a sort of 3C(1)
// axes have a 2-dim 1-space and a 1-dim 0-space
assert Eigenvalues(B!x) eq {<1,2>, <0,1>};
assert Eigenvalues(B!y) eq {<1,2>, <0,1>};
c := B.1+B.2 - 2*B.1*B.2;
assert c^2 eq c;



// =========================================================
//
// 4Y(1/2, bt)
//
// =========================================================
A, gen, frob := M4Y_bt();
F<bt> := BaseRing(A);

// identity
so, id := HasOne(A);
assert so;
assert id eq A![-1/2,-1/2,-1/2,-1/2,(6*bt-1)/(4*bt)]/(2*bt-1);
// Since bt \neq 1/2, algebra always has an identity

// Subalgebras
B, inc := sub<A|A.1,A.3>;
assert Dimension(B) eq 3;
assert Eigenvalues(B!A.1) eq {<1,1>, <0,1>, <1/2,1>};
assert Eigenvalues(B!A.3) eq {<1,1>, <0,1>, <1/2,1>};
so, id := HasOne(B);
assert so;
assert id eq (-1/2*(A.1+A.3) + (4*bt-1)/(4*bt)*A.5)/(2*bt-1);
// Since bt \neq 1/2, B has an identity
assert A.1*A.3-(A.1+A.3)/2 eq 4*bt*(2*bt-1)*id;
// so dl = 64bt(2bt-1) + 2 and <<a_0, a_2>> = S(dl)

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



// =========================================================
//
// 4Y(al, (1-al^2)/2 )
//
// =========================================================
A, gen, frob := M4Y_al();
F<al> := BaseRing(A);

// identity
so, id := HasOne(A);
assert so;
assert id eq A![1,1,1,1,-al-2]/al;
// so the algebra always has an identity

// Subalgebras
B, inc := sub<A|A.1,A.3>;
assert Dimension(B) eq 3;
assert Eigenvalues(B!A.1) eq {<1,1>, <0,1>, <al,1>};
assert Eigenvalues(B!A.3) eq {<1,1>, <0,1>, <al,1>};
c := A.1+A.3-2/al*A.1*A.3;
assert c^2 eq c;
// So <<a_0, a_2 >> = 3C(al)

int := B meet sub<A|A.2,A.4>;
assert Dimension(int) eq 1;
assert A.5 in int;

assert frob[1,5] eq 1-al/2;
// So A.1*A.5 \neq 0 if al \neq 2

so,  idB := HasOne(B);
assert so;
assert idB -c in int;

// Check projection graph
assert frob[1,2] eq -1/4*(al-2)*(al+1);
assert frob[1,3] eq al/2;
// So the projection graph is complete except when al = 2 (al \neq -1 for the algebra)
// If al = 2, then the projection graph has two connected components
// But if an ideal does contain any axis, then it contains them all.
// THIS GOES FOR ALL THE ALGEBRAS

assert Determinant(frob) eq -1/16*al^4*(al-2)^3/(al+1);
// Since the characteristic is not 2 and al \neq 0 or -1, we just need to check al = 2

A, gen, frob := M4Y_al(2);

R := NullSpace(frob);
assert Dimension(R) eq 3;
a := A.1-A.3;
b := A.2-A.4;
c := A.5;
assert a in R;
assert b in R;
assert c in R;

// Quotient is F^2
B, quo := quo<A|[A|u : u in Basis(R)]>;
assert IsAssociative(B);
assert Dimension(B) eq 2;

int := sub<A|A.1,A.3> meet sub<A|A.2,A.4>;
assert c in int;

// Can show that R has no non-trivial proper ideals.
// NB The Miyamoto group inverts a and b and fixes c
// So G-module structure is a trivial module \oplus 2 copies of the sign module

assert A.1*c eq -1/2*a + 3/2*c;
assert A.3*c eq 1/2*a + 3/2*c;

assert A.2*c eq -1/2*b + 3/2*c;
assert A.4*c eq 1/2*b + 3/2*c;

assert A.1*a eq 1/2*a - 3/2*c;
assert A.3*a eq 1/2*a + 3/2*c;





// Isomorphism with 4B algebra
B := M4B();
B1, inc1 := sub<B|B.1, B.3>;
B2, inc2 := sub<B|B.2, B.4>;
so, id1 := HasOne(B1);
so, id2 := HasOne(B2);

// NB we need to be able to divide by al+1 to get both identities
assert id1@inc1 eq 1/(al+1)*(B.1+B.3+B.5);

a1 := id1-B.1;
a2 := id2-B.2;
a3 := id1-B.3;
a4 := id2-B.4;
x := B.5;

// We get Monster type axes for (1-al, al*(1-al/2))
evals, espace, FL := IdentifyFusionLaw(a1: eigenvalues := [1,0,1-al, al*(1-al/2)]);

AL := 1-al;
BT := al*(1-al/2);
assert BT eq (1-AL^2)/2;

assert HasMonsterFusionLaw(a1: fusion_values:=[AL, BT]);
assert HasMonsterFusionLaw(a2: fusion_values:=[AL, BT]);
assert sub<B | a1, a2> eq B;

// We claim that the isomorphism is a1, a2, a3, a4, x maps to the given generators of 4Y(al, (1-al^2)/2)
// We check the multiplication
assert a1^2 eq a1;
assert a1*a2 eq BT/2*(a1+a2-a3-a4) +(AL+1)^2/4*x;
assert a1*a3 eq (AL-1)/2*(a1+a3) + (AL+1)/2*x;
assert a1*x eq (AL-1)/2*(-a1+a3) + (AL+1)/2*x;
assert x^2 eq x;




// =========================================================
//
// H_4
//
// =========================================================
A, gen, frob := HighwaterQuotient(4);

// identity
so, id := HasOne(A);
assert so;
assert id eq A![1/4,1/4,1/4,1/4,-1/3, -1/6];
// Since the characteristic is not 2, or 3, the algebra always has an identity

// The subalgebra is a 3C(2)
assert A.1*A.3 ne 0;
B, inc := sub<A|A.1,A.3>;
assert Dimension(B) eq 3;
assert HasJordanFusionLaw(B!A.1: fusion_value:=2);
c := A.1+A.3-A.1*A.3;
assert c^2 eq c;

int := B meet sub<A|A.2,A.4>;
assert Dimension(int) eq 1;
so, idB := HasOne(B);
assert so;
assert idB - c in int;

// The projection graph is connected
assert frob[1,2] eq 1;

// The nullspace is spanned by the difference of axes and all the sigma elements
R := Nullspace(frob);
assert Dimension(R) eq 3 + 2;

// The Miyamoto group is V4
// The G-module structure of R is two different sign modules and three trivial modules
s1 := A.1-A.3;
s2 := A.2-A.4;
tr1 := A.1+A.3-(A.2+A.4);
tr2 := A.5;
tr3 := A.6;

assert forall{v : v in [s1,s2,tr1,tr2,tr3] | v in R};

// TO COMPLETE
assert A.1*s1 eq 1/2*s1 - A.6;
assert A.2*s1 eq 1/2*s1;
assert A.3*s1 eq 1/2*s1 + A.6;
assert A.4*s1 eq 1/2*s1;
assert A.5*s1 eq -3/4*s1;
assert A.6*s1 eq -3/2*s1;

assert A.1*s2 eq 1/2*s2;
assert A.2*s2 eq 1/2*s2 - A.6;
assert A.3*s2 eq 1/2*s2;
assert A.4*s2 eq 1/2*s2 + A.6;
assert A.5*s2 eq -3/4*s2;
assert A.6*s2 eq -3/2*s2;

assert A.1*A.6 eq -3/4*s1 + 3/2*A.6;
assert A.2*A.6 eq -3/4*s2 + 3/2*A.6;
assert A.3*A.6 eq 3/4*s1 + 3/2*A.6;
assert A.4*A.6 eq 3/4*s2 + 3/2*A.6;
assert A.5*A.6 eq 3/4*A.6;
assert A.6*A.6 eq 3/2*A.6;

I := ideal<A | A.1-A.3>;
assert Dimension(I) eq 3;
// I has no subideals

B, phi := quo<A | I>;
assert HasJordanFusionLaw(A.1@phi: fusion_value:=2);
assert HasJordanFusionLaw(A.2@phi: fusion_value:=2);
assert sub<B | A.1@phi, A.2@phi> eq B;
// so the quotient is a 3C(2);

assert A.1*tr1 eq 1/2*tr1 - (2*A.5-A.6);
assert A.2*tr1 eq 1/2*tr1 + (2*A.5-A.6);
assert A.3*tr1 eq 1/2*tr1 - (2*A.5-A.6);
assert A.4*tr1 eq 1/2*tr1 +(2*A.5-A.6);
assert A.5*tr1 eq -3/2*tr1;
assert A.6*tr1 eq 0;

assert A.1*(2*A.5-A.6) eq -3/4*tr1 + 3/2*(2*A.5-A.6);
assert A.2*(2*A.5-A.6) eq 3/4*tr1 + 3/2*(2*A.5-A.6);
assert A.3*(2*A.5-A.6) eq -3/4*tr1 + 3/2*(2*A.5-A.6);
assert A.4*(2*A.5-A.6) eq 3/4*tr1 + 3/2*(2*A.5-A.6);
assert A.5*(2*A.5-A.6) eq 3/2*(2*A.5-A.6);
assert A.6*(2*A.5-A.6) eq 0;

// Can see from eg A.5* that there is no subideal of J
J := ideal<A | tr1, 2*A.5-A.6>;
// Can't be isomorphic to any other X4 algebra above, as no other can give (al,bt) = (2, 1/2)
// Quotient has dimension 4 and axial dimension 3
// Quotient is isomorphic to IY_3(2, 1/2, 0)
B, phi := quo<A | J>;

// find the basis
bas := [ (B.1-B.3), 2*B.2-(B.1+B.3), 1/2*(B.1+B.3) -2*B.4, 4/3*B.4];
V := VectorSpaceWithBasis([Vector(v) : v in bas]);
StrB := [[ Coordinates(V,Vector(bas[i]*bas[j])) : i in [1..#bas]] : j in [1..#bas]];

IY3, frob := SplitSpinFactor(IdentityMatrix(QQ,2), 2);
Str_IY3 := [[ Eltseq(v) : v in r ] : r in BasisProducts(IY3) ];

assert StrB eq Str_IY3;
// R is the direct sum of these two ideals.  So no other ideals.

// =========================================================
//
// IY_3(al, 1/2, 0)
//
// =========================================================
Id2 := IdentityMatrix(QQ, 2);
A, frob := SplitSpinFactor(Id2);
F<al> := BaseRing(A);

a0 := 1/2*(A.1 + al*A.3+(al+1)*A.4);
a1 := 1/2*(A.2 + al*A.3+(al+1)*A.4);
a2 := 1/2*(-A.1 + al*A.3+(al+1)*A.4);
a3 := 1/2*(-A.2 + al*A.3+(al+1)*A.4);

t0 := MiyamotoInvolution(a0);
t1 := MiyamotoInvolution(a1);
assert a2 eq a0*t1;
assert a3 eq a1*t0;

// subalgebras is 3C(2)
assert a0*a2 ne 0;
c := a0 + a2 - 2/al*a0*a2;
assert c^2 eq c;

// They intersect in the 2-dim subalgebra which is the difference of axes.
int := sub<A|a0,a2> meet sub<A|a1,a3>;
assert Dimension(int) eq 2;

assert InnerProduct(a0*frob, a0) eq (al+1);
assert InnerProduct(a0*frob, a2) eq 1/2*al*(al+1);
assert InnerProduct(a0*frob, a1) eq 1/4*(al+1)*(al+2);

assert Determinant(frob) eq -(al-2)^3*(al+1)^3;
// So just need to check al = -1 and al = 2
// Note that these can't both be true at the same time.
// As otherwise, char is 3 and so al = -1 = 2 = 1/2 = bt

// Check al = 2

A, frob := SplitSpinFactor(Id2, 2);

R := NullSpace(frob);
assert Dimension(R) eq 3;

a0 := 1/2*(A.1 + 2*A.3 + 3*A.4);
a1 := 1/2*(A.2 + 2*A.3 + 3*A.4);
a2 := 1/2*(-A.1 + 2*A.3 + 3*A.4);
a3 := 1/2*(-A.2 + 2*A.3 + 3*A.4);

x := a0-a2;
y := a1-a3;

assert x in R;
assert y in R;
assert A.4 in R;

// G-module structure is the sum of two different sign modules and a trivial
assert A.1*x eq -3*A.4;
assert A.2*x eq 0;
assert A.3*x eq 2*x;
assert A.4*x eq -x;

assert A.1*y eq 0;
assert A.2*y eq -3*A.4;
assert A.3*y eq 2*y;
assert A.4*y eq -y;

assert A.1*A.4 eq -x;
assert A.2*A.4 eq y;
assert A.3*A.4 eq 0;
assert A.4*A.4 eq A.4;

// no subideals - same as H4

// Check al = -1

A, frob := SplitSpinFactor(Id2, -1);

R := NullSpace(frob);
assert Dimension(R) eq 3;

a0 := 1/2*(A.1 - A.3);
a1 := 1/2*(A.2 - A.3);
a2 := 1/2*(-A.1 - A.3);
a3 := 1/2*(-A.2 - A.3);

x := a0-a2;
y := a1-a3;

assert x in R;
assert y in R;
assert A.3 in R;

// G-module structure is the sum of two different sign modules and a trivial
assert A.1*x eq -3*A.3;
assert A.2*x eq 0;
assert A.3*x eq -x;
assert A.4*x eq 2*x;

assert A.1*y eq 0;
assert A.2*y eq -3*A.3;
assert A.3*y eq -y;
assert A.4*y eq 2*y;

assert A.1*A.3 eq -x;
assert A.2*A.3 eq -y;
assert A.3*A.3 eq A.3;
assert A.4*A.3 eq 0;

// So the ideal has no subideals

// =========================================================
//
// An exceptional isomorphism
//
// =========================================================
A := M4A(1/8);
B := M4J(1/8);

// Need to get the right basis
z := B.1*B.2 - 3/16*(B.1+B.2) - 1/16*(B.3+B.4);
bas := [B.1, B.2, B.3, B.4, z];
V := VectorSpaceWithBasis([Vector(v) : v in bas]);
StrB := [[ Coordinates(V,Vector(bas[i]*bas[j])) : i in [1..5]] : j in [1..5]];
StrA := [[ Eltseq(v) : v in r ] : r in BasisProducts(A) ];

assert StrA eq StrB;
// Hence M4A(1/4,1/8) and M4J(1/4,1/8) are isomorphic



