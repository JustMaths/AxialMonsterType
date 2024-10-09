/*

Code to verify properties of the 2-generated axial algebras of Monster type

*/
AttachSpec("2-gen Monster.spec");
AttachSpec("../AxialTools/AxialTools.spec");

QQ := Rationals();
/*
******************************

X(4) axet

Look in the survey paper folder for other code!!

******************************
*/
// ============
//
// 4A(1/4, bt)
//
// ============
A, gen, frob := M4A();
F<bt> := BaseRing(A);

// <<a_0, a_2 >> = 2B
assert A.1*A.3 eq 0;

// Check double axes
x := A.1+A.3;
y := A.2+A.4;
// They have Monster type (1/2, 2bt)
// NB need bt ne 1/2

B, inc := sub<A|x,y>;
assert Dimension(B) eq 3;

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
// Since bt can't be 0, we just need to check bt = 1/2


A, gen, frob := M4A(1/2);




// Check double axes
x := A.1+A.3;
y := A.2+A.4;
// They have Jordan type 1/2, but have a 3-dim 1-space

B, inc := sub<A|x,y>;
// in B, the axes are primitve Jordan type 1/2
assert Dimension(B) eq 3;

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

// ============
//
// 4B(al, al^2/2)
//
// ============
A, gen, frob := M4B();
F<al> := BaseRing(A);

assert Dimension(sub<A|A.1,A.3> meet sub<A|A.2,A.4>);

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

// al \neq 2, so just need to check al = -1

A, gen, frob := M4B(-1);

R := NullSpace(frob);
assert Dimension(R) eq 2;

int := sub<A|A.1,A.3> meet sub<A|A.2,A.4>;
assert A!int.1 notin R;

I1 := ideal<A|R.1+R.2>;
assert Dimension(I1) eq 1;

// This is 4B(-1,1/2)^x

I2 := ideal<A|R.1-R.2>;
assert Dimension(I2) eq 1;

B, quo := quo<A|I2>;

n := B![1,0,1,1];
z1 := B.4;
e := B![1,0,1,0];
f := B![-1,2,-1,0];

// Can check that this is IY_3(-1,1/2,0)^x = \widehat{S}(b, -1)^\circ;

B, quo := quo<A|R.1>;
so, id := HasOne(B);

// Check the images of a_0 and a_1 to see that they have slightly different fusion laws (both subsets of the Monster), so the ideal is non-symmetric.  Similarly for R.2 and hence any 1-dim ideal in R gives a non-symmetric quotient


// ============
//
// 4J(2bt, bt)
//
// ============
A, gen, frob := M4J();

F<bt> := BaseRing(A);

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
assert Dimension(B) eq 3;
c := B.1+B.2 - 1/(2*bt)*B.1*B.2;
assert c^2 eq c;
// So B is a 3C(4bt)


assert frob[1,2] eq bt;
// So the projection graph always has an edge between a_1 and a_2
// The projection graph is a square

assert Determinant(frob) eq 2*(2*bt-1)^2*(4*bt+1);
// Since bt \neq 1/2, just need to check bt = -1/4

A, gen, frob := M4J(-1/4);

R := NullSpace(frob);
assert Dimension(R) eq 1;

// It is 4J(-1/2, -1/4)^x
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
c := B.1+B.2 - 2*B.1*B.2;
assert c^2 eq c;

// ============
//
// 4Y(1/2, bt)
//
// ============
A, gen, frob := M4Y_bt();
F<bt> := BaseRing(A);

// Subalgebras
B, inc := sub<A|A.1,A.3>;
assert Dimension(B) eq 3;
so, id := HasOne(B);
id := id@inc;
assert so;
assert A.1*A.3-(A.1+A.3)/2 eq 4*bt*(2*bt-1)*id;

// so dl = 64bt(2bt-1) + 2 and <<a_0, a_2>> = S(dl)

assert Dimension(B meet sub<A|A.2,A.4>) eq 1;
assert A.5 in int;
assert frob[1,5] eq 2*bt;
// A.5 is not in the 0-eigenspace of A.1

assert frob[1,2] eq 4*bt^2;
assert frob[1,3] eq (4*bt-1)^2;
// So the projection graph always has an edge between a_1 and a_2 and for bt neq 1/4 it has an edge between a_1 and a_3
// The projection graph is complete if bt \neq 1/4 and a square if bt = 1/4

assert Determinant(frob) eq 2^8*bt^2*(2*bt-1)^6;

// Since bt \neq 0, 1/2, there are no quotients

// ============
//
// 4Y(al, (1-al^2)/2 )
//
// ============
A, gen, frob := M4Y_al();
F<al> := BaseRing(A);

// Subalgebras
B, inc := sub<A|A.1,A.3>;
assert Dimension(B) eq 3;
c := A.1+A.3-2/al*A.1*A.3;
assert c^2 eq c;
// So <<a_0, a_2 >> = 3C(al)

assert Dimension(B meet sub<A|A.2,A.4>) eq 1;
assert A.5 in B meet sub<A|A.2,A.4>;

assert frob[1,5] eq 1-al/2;
// So A.1*A.5 \neq 0 if al \neq 2

so,  idB := HasOne(B);
assert so;
assert idB -c in int;

assert frob[1,2] eq -1/4*(al-2)*(al+1);
assert frob[1,3] eq al/2;
// So the projection graph is complete except when al = 2 (al \neq -1 for the algebra)
// If al = 2, then the projection graph has two connected components
// But if an ideal does contain any axis, then it contains them all.
// THIS GOES FOR ALL THE ALGEBRAS
 
assert Determinant(frob) eq -1/16*al^4*(al-2)^3/(al+1);

// al \neq -1, so just need to check al = 2

A, gen, frob := M4Y_al(2);

R := NullSpace(frob);
assert Dimension(R) eq 3;

int := sub<A|A.1,A.3> meet sub<A|A.2,A.4>;
assert A.5 in int;

// Can show that R has no non-trivial proper ideals.
a := A.1-A.3;
b := A.2-A.4;
c := A.5;
// Also c = intersection of the subalgebras is in R

assert a in R;
assert b in R;
assert c in R;

// The Miyamoto group inverts a and b and fixes c


assert A.1*a eq 1/2*a - 3/2*c;
assert A.3*a eq 1/2*a + 3/2*c;
assert A.2*a eq -3/2*a;
assert A.4*a eq -3/2*a;
assert A.5*a eq -a;




// Isomorphism
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

// We claim that the isomorphism is a1, a2, a3, a4, x maps to the given generators of 4Y(al, (1-al^2)/2)
// We check the multiplication
assert a1^2 eq a1;
assert a1*a2 eq BT/2*(a1+a2-a3-a4) +(AL+1)^2/4*x;
assert a1*a3 eq (AL-1)/2*(a1+a3) + (AL+1)/2*x;
assert a1*x eq (AL-1)/2*(-a1+a3) + (AL+1)/2*x;
assert x^2 eq x;


// ============
//
// H_4
//
// ============
A := HighwaterQuotient(4);

// The subalgebra is a 3C(2)
assert A.1*A.3 ne 0;
B, inc := sub<A|A.1,A.3>;
assert Dimension(B) eq 3;
c := A.1+A.3-A.1*A.3;
assert c^2 eq c;

int := B meet sub<A|A.2,A.4>;
assert Dimension(int) eq 1;
so, idB := HasOne(B);
assert so;
assert idB - c in int;

// ============
//
// IY_3(al, 1/2, 0)
//
// ============
A, frob := SplitSpinFactor(IdentityMatrix(Rationals(), 2));
F<al> := BaseRing(A);

a0 := 1/2*(A.1 + al*A.3+(al+1)*A.4);
a1 := 1/2*(A.2 + al*A.3+(al+1)*A.4);

t0 := MiyamotoInvolution(a0);
t1 := MiyamotoInvolution(a1);

G := sub<GL(4,F)| t0, t1>;
assert #{ x*g : x in [a0,a1], g in G} eq 4;

a2 := a0*t1;

// subalgebras is 3C(2)
assert a0*a2 ne 0;
c := a0 + a2 - 2/al*a0*a2;
assert c^2 eq c;

a3 := a1*t0;
int := sub<A|a0,a2> meet sub<A|a1,a3>;
assert Dimension(int) eq 2;

det := Determinant(frob);
assert det eq -(al-2)^3*(al+1)^3;

// ==============
//
// An exceptional isomorphism
//
// ==============
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



