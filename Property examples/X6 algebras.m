AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");



///////////////////////////////////////////////////////////////////////////////////////////

////////////////                  6A(al, (-al^2)/(4(2al-1)))

//////////////////////////////////////////////////////////////////////////////////////////

A , gen, frob := M6A();
F<al> := BaseRing(A);

bt := -al^2/4/(2*al-1);
// Identity
so, id := HasOne(A);
assert so;
assert id eq 1/(12*al^2-al-2) * ( 2*(2*al-1)*A![1,1,1,1,1,1,0,0] + (5*al -2)*A.7 + (4*(2*al-1)*(3*al-1))/(3*al-2)*A.8);
// Always has an identity unless 12*al^2-al-2=0 or al = 2/3

// 0-Eigenvalues
u1 := al*A.1-(A.4+A.7);
u2 := al*(3*al-2)*(7*al-3)/(2*al-1)*A.1 - 2*(3*al-2)*(A.3+A.5) - 2*(5*al-2)*A.8;
u3 := (3*al-2)*(A.2+A.6 -al/2/(2*al-1)*A.4) +al*A.8;

// f[1,4] = f[2,5] = f[3,6] neq 0, f[1,3] neq 0, f[1,5] neq 0. \\ Check Quadratics
// The projection graph is connected 

Orbit1 := [A.1, A.3, A.5];
Orbit2 := [A.2, A.4, A.6];

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

assert A.1*t2 in Orbit1;
assert A.1*t2*t1 in Orbit1;
assert A.2*t1 in Orbit2;
assert A.2*t1*t2 in Orbit2;

assert  InnerProduct(Vector(A.1*t2)*frob, Vector(A.2*t1)) eq 1/2*al;

// So there are no Ideals containing Axes.



bt := (-al^2)/(4*(2*al-1));



assert Determinant(frob) eq (-1/2^15)*(al-1)^3*(3*al-2)*(7*al-4)^5*(12*al^2-1*al-2)*(al^2+4*al-2)^4/(2*al-1)^11;
// since al can't be 1, we only need to check al = 2/3, al = 4/7, 12*al^2-1*al-2=0 and al^2+4*al-2 = 0

// Need to check whether these can occur simultaneously.

// Supose that al = 2/3 and al = 4/7, then char \neq 3, 7 in either case
// So we need, 14-12 = 2 = 0 requiring that char = 2, a contradiction

//----------------
// Suppose al = 2/3, then char \neq 3.
assert Evaluate(al^2+4*al-2, 2/3) = 10/9;
// So these can be simultaneously 0 if char = 5;
// In char 5, al^2+4*al-2 = al^2 - al - 2 = (al-2)(al+1)
assert GF(5)!(2/3) eq -1;
// bt is
assert GF(5)!(Evaluate(bt,2/3)) eq 3;
// So this is an ok solution.

assert Evaluate(12*al^2-1*al-2, 2/3) = 8/3;
// this can't be 0 since char \neq 2

//-----------------
// Suppose al = 4/7, then char \neq 7.  Also note that char \neq 3 as otherwise, al = 1.
assert Evaluate(al^2+4*al-2, 4/7) = 2*3*5/49;
// So these can be simultaneously 0 if char = 5
// In char 5, al^2+4*al-2 = al^2 - al - 2 = (al-2)(al+1)
// This is the other solution from above
assert GF(5)!(4/7) eq 2;
// bt is
assert GF(5)!(Evaluate(bt,4/7)) eq 3;
// So this is an ok solution.

assert Evaluate(12*al^2-1*al-2, 4/7) = 2*3*11/49;
// So these can be simultaneously 0 if char = 11
// In char 11, 12*al^2-1*al-2 = al^2 - al - 2 = (al-2)(al+1)
assert GF(11)!(4/7) eq -1;
// bt is
assert GF(11)!(Evaluate(bt,4/7)) eq 1;
// So this is NOT a solution.


// suppose that al^2+4*al-2 = 0 and 12*al^2-1*al-2=0, then
assert 12*(al^2+4*al-2) - (12*al^2-1*al-2) eq 49*al -22;
// Note that we can't have characteristic 7, or 11 as otherwise this can't be 0.
// So we require al = 22/49 and to be a root of the equations
assert Evaluate(al^2+4*al-2, 22/49) eq -6/7^4;
assert Evaluate(12*al^2-1*al-2, 22/49) eq -2^3*3^2/7^4;
// so we require char = 3, however, then al = 22/49 = 1, a contradiction.

/*
So can split into cases:

1. al = 2/3
  a. char \neq 5
  b. char = 5

2. al = 4/7
  a. char \neq 5
  b. char = 5

3. al^2+4*al-2=0
  a. Not char eq 5 (this case is covered above)

4. 12*al^2-1*al-2=0

*/

// NB Clearly in cases 1 and 2, char \neq 3.  For (3), if char = 3, then poly is al^2+1+1 = (al-1)^2, so we don't need to consider this case.  For (4), in char 3, this becomes (al-1), so again we don't need to consider this.  So, for the ideals, char \neq 2,3 and so we always have ordinary rep theory


/////////////////////////////////////////////////////////////////////////////////////////////////
//
// Case 1
//
A, gen, frob:= M6A(2/3);

P<t> := PolynomialRing(Rationals());
charpoly := CharacteristicPolynomial(frob);
assert charpoly eq t*(t-5/3)*(t - 5/6)^2*(t - 1/6)^2*(t^2 - 10/3*t + 5/3);

// Clearly the nullspace is 1-dimensional unless char is 5.


// double check characteristics which this has a larger nullspace
// Since the characteristic of F is not 2 or 3, in any characteristic the nullspace of frob is the same as the nullspace of 6*frob
M := HermiteForm(ChangeRing(6*frob, Integers()));
assert Diagonal(M) eq [ 1, 1, 1, 5, 10, 10, 30, 0 ];
// So nullspace is indeed larger iff field is char 5



// the Radical is 1 dim
assert Dimension(Nullspace(frob)) eq 1;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
u := A.8;
assert u in R;
assert u in Annihilator(A);
assert Dimension(Annihilator(A)) eq 1;
// So the radical is the annihilator

// The quotient is 7 dimensional
B, quo := quo<A|R>;
assert sub<B|B.1,B.2> eq B;  // so B is 2-generated
B.1 eq A.1@quo;
B.2 eq A.2@quo;

assert HasMonsterFusionLaw(B.1: fusion_values:=[2/3,-1/3]);
assert Dimension(Eigenspace(B.1,0)) eq 2;
assert Dimension(Eigenspace(B.1,2/3)) eq 2;
assert Dimension(Eigenspace(B.1,-1/3)) eq 2;



// This quotient is also of Monster type and is 6A(2/3,−1/3)^x

// -------------------------------------
A, gen, frob:= M6A(GF(5)!2/3);

// the Radical is 5 dim
assert Dimension(Nullspace(frob)) eq 5;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;

// Inside R we have the annihilator still
assert A.8 in Annihilator(A);
assert Dimension(Annihilator(A)) eq 1;

u1 := A.8;
u2 := &+[A.i : i in [1..6]] + 3*A.7 + A.8;
u3 := A.1+A.3+A.5 - (A.2+A.4+A.6);

u4 := A.1-A.3+A.4-A.6;
u5 := A.2-A.6-(A.3-A.5);

assert forall{ u : u in [u1,u2,u3,u4,u5] | u in R};
assert IsIndependent([u1,u2,u3,u4,u5]);
// So u1, .., u5 is a basis for R

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
Miy := sub<GL(8,5)|t1,t2>;
assert Order(Miy) eq 6;

// Ordinary rep theory, so, by Maschke's theorem, R decomposes as the direct sum of irreducibles
// u1, u2,u3 each generate 1-dim modules, <u4, u5> is 2-dim, so G-modules structure is 1+1+1+2

// Now consider what the possible G-modules are for ideals.

assert forall{ u : u in [u1,u2,u4,u5] | IsZero(A.7*u)};
assert A.7*u3 eq -u3;
// So whenever we see u3 in the decomposition, we have (u3)

U3 := ideal<A|u3>;
assert Dimension(U3) eq 4;
assert u2 in U3 and u4 in U3 and u5 in U3;

// Note that u1 \notin U3, so we have R = <<u1>> \oplus U3 and this is invariant under multiplication by A
// So just need to check for subideals of U3

// First check for a 1-dimensional ideal - must be a linear combination of u2 and u3
assert u2^2 eq -u2;
assert u2*u3 eq 3*u3;
assert u3^2 eq 3*u2;
// So if the linear combination is a*u2 + b*u3, multiplying by u2, we see that we need a=-k*a and b = 3*kb for some k, a contradiction.  So, whever you see u2 in the decomposition, you get u3 also, and vice versa.

assert A.1*u2 eq -u2 + 3*u3 + 2*u4-u5;
// So <<u2,u3>> is not a 2-dim ideal

assert u4*u4 eq 2*u2 + u4+3*u5;
// So <<u4,u5>> is also not a 2-dim ideal.

// Hence there are no proper ideal of U3.
B, quo := quo<A|U3>;
assert HasMonsterFusionLaw(B.1: fusion_values:=[4,3]);
assert Dimension(Eigenspace(B.1,0)) eq 1;
assert Dimension(Eigenspace(B.1,4)) eq 1;
assert Dimension(Eigenspace(B.1,3)) eq 1;
// So B is of Monster type.  It has a 1-dim annihilator

bas := [B.1,B.3,A.5@quo,3*u1@quo];
BB := ChangeBasis(B, bas);

assert [[ Eltseq(e) : e in r] : r in BasisProducts(BB)] eq [[ Eltseq(e) : e in r] : r in BasisProducts(M3A(GF(5)!4, GF(5)!3))];
// So the quotient is equal to 3A, however, the 6 axes are all distinct.

// The quotient by u1 is still 6A(2/3,−1/3)^x


////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Case 2
//
A, gen, frob:= M6A(4/7);
// NB that the characteristic is clearly not 7

// Also not 3, as al = 1 and not 11 as bt = 1
assert GF(11)!Evaluate(bt,4/7) eq 1;

P<t> := PolynomialRing(Rationals());
charpoly := CharacteristicPolynomial(frob);
assert charpoly eq t^5*(t - 15/7)*(t^2 - 34/7*t + 165/49);

assert 165 eq 3*5*11;
// if char \neq 5, then since 165 and 15 can are never zero as char is not 3,7,11, nullspace is always 5 dim.


// double check characteristics which this has a larger nullspace
// Since the characteristic of F is not 7, in any characteristic the nullspace of frob is the same as the nullspace of 7*frob
M := HermiteForm(ChangeRing(7*frob, Integers()));
assert Diagonal(M) eq [ 1, 5, 0, 0, 0, 0, 0, 0];

// So nullspace is indeed larger iff field is char 5


// Look at the general case first

// the Radical is normally 5 dim
assert Dimension(Nullspace(frob)) eq 5;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
u1 := A.1 - A.3;
u3 := A.3 - A.5;
u2 := A.2 - A.4;
u4 := A.4 - A.6;
u5 := A.8;
assert u1 in R and u2 in R and u3 in R and u4 in R and u5 in R;
assert IsIndependent([u1,u2,u3,u4,u5]);

// The quotient is 3 dimensional
B, quo := quo<A|R>;
assert sub<B|B.1,B.2> eq B;  // so B is 2-generated
B.1 eq A.1@quo;
B.2 eq A.2@quo;
HasJordanFusionLaw(B.1:fusion_value:=4/7);
HasJordanFusionLaw(B.2:fusion_value:=4/7);
// So the quotient is a 3C(4/7)

// Now check for other ideals of R
// Char \neq 3, so ordinary rep theory
// It is clear that the submodule structure is <u1,u3> \oplus <u_2,u_4> \oplus <u5>

// No 1-dim ideal.
assert ideal<A|u5> eq R;

// No 4 dim ideal
assert ideal<A|u2> eq R;

// Just need to check for 2-dim ideals.  This must be a diagonal copy inside the 2+2
// Consider the group structure

// Edit to match the text **************************************

t2 := MiyamotoInvolution(A.2);
assert u1*t2 eq -u1;
assert u4*t2 eq -u4;
// so must have a*u1 + b*u4 for some a and b
assert (A.1+A.3)*u1 eq u1;
assert (A.1+A.3)*u4 eq 6/7*u1-2/7*u4;
// So there are no subideals


//------------------------------------
// Now check char 5
A, gen, frob := M6A(GF(5)!4/7);
assert GF(5)!4/7 eq 2;

assert Dimension(Nullspace(frob)) eq 7;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
u1 := A.1 - A.3;
u3 := A.3 - A.5;
u2 := A.2 - A.4;
u4 := A.4 - A.6;
u5 := A.8;
u6 := A.1+A.2+A.3 - 3*A.7;
u7 := A.4+A.5+A.6 - 3*A.7;

// From above, u1, .., u5 in R
assert u6 in R and u7 in R;
assert IsIndependent([u1,u2,u3,u4,u5,u6,u7]);

// Module structure is now 1+1+1+2+2

// Still no 2-dim ideals where the group acts non-trivially
// As above, would have a*u1 + b*u4 for some a and b
assert (A.1+A.3)*u1 eq u1;
assert (A.1+A.3)*u4 eq 6/7*u1-2/7*u4;

I1 := ideal<A|u1>;
assert Dimension(I1) eq 5;
assert u5 in I1;
// This is the 5-dimensional ideal above

// Only other possibility is a sum of trivial modules
assert A.8*u6 in I1;
assert A.8*u7 in I1;
assert A.1*u6 notin I1;
assert A.1*u7 in I1;
assert not IsZero(A.8*u6) and not IsZero(A.8*u7) and not IsZero(A.1*u7);
// So the only ideals are I1 and R

// Here 3C(4/7) = 3C(2)
// it has a 2-dim ideal, with a quotient 1A.  This agrees.

////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Case 3
//

// al^2+4*al-2=0
// And not (char eq 5 and al = -1, or 2) as this is covered above.

// NB char \neq 3 as then al^2 + al +1 = al^2 -2al + 1 = (al-1)^2.


// This has roots -2 \pm r, where r = \sqrt(6)
P<t> := PolynomialRing(Rationals());
F := SplittingField(t^2-6);
r := -SquareRoot(F!6);
assert r eq F.1;

// bt is 1/2 in both cases
assert Evaluate(bt, -2-r) eq 1/2;
assert Evaluate(bt, -2+r) eq 1/2;

// Two roots to check
A, gen, frob := M6A(-2-r);

assert Dimension(Nullspace(frob)) eq 4;

// Can't use char poly check as for GF(19) we get a t^5 in the char poly of frob, but only a 4-dim nullspace.

// To check whether frob can have a larger nullspace  over some characteristics, we perform Gaussian elimination by hand.  We take care not to:
// multiply any row by any prime power, except powers of 2, 3, or 5.
// add a scalar multiple of a row to annother where the scalar has denominator a forbidden prime power.

M := frob;

AddRow(~M, 1, 1, 4);
AddRow(~M, 1, 2, 5);
AddRow(~M, 1, 3, 6);
AddRow(~M, -1, 4, 5);
AddRow(~M, -1, 4, 6);

AddRow(~M, -1, 2, 3);
AddRow(~M, 1, 1, 3);
AddRow(~M, -2, 3, 4);

AddRow(~M, -2, 3, 7);

AddRow(~M, -5/4*r, 7,8);

AddRow(~M, -r/4, 7, 3);
AddRow(~M, -3, 3, 8);

SwapRows(~M, 4, 7);

SwapRows(~M, 1, 4);
MultiplyRow(~M, -1, 1);
AddRow(~M, -1, 1, 4);
AddRow(~M, -1/8*(-r+4), 1, 2);

AddRow(~M, 1, 2, 4);

SwapRows(~M, 3, 4);

// The matrix is now in Row Echelon Form
assert M[1,1] eq 1;
assert forall{ j : j in [2..8] | M[j,1] eq 0};

assert M[2,2] eq 1/8*(r+4);
assert forall{ j : j in [3..8] | M[j,2] eq 0};

assert M[3,3] eq -3/8*(r+4);
assert forall{ j : j in [4..8] | M[j,3] eq 0};

assert Eltseq(M[4]) eq [0,0,0,0,0,0, -5/4*(r +2), -5/4*(r+3)];

// The last 4 rows are all zero
assert forall{ j : j in [5..8] | IsZero(M[j])};

// Note that r = -4 iff 6 = r^2 = 16 iff char eq 5
// Since char \neq 5, rows M[2,2] and M[3,3] are always non-zero

// Note that the last row can only be zero if r = -2 and r = -3, a contradiction.
// Hence rank of M=frob is always 4 in any char.

R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;

B, quo := quo<A|R>;

// We identify the quotient
AL := -2-r;

z1 := B.4;
z2 := 1/5*(-2*r + 2)*(B.1-B.2+B.3) - 1/5*(r + 4)*B.4;
e := 2*B.1-AL*z1 -(AL+1)*z2;
f := 2*B.2-AL*z1 -(AL+1)*z2;
assert IsIndependent([z1,z2,e,f]);

// check the structure constants wrt this basis
assert z1^2 eq z1;
assert z2^2 eq z2;
assert z1*z2 eq 0;

assert e*z1 eq AL*e;
assert f*z1 eq AL*f;
assert e*z2 eq (1-AL)*e;
assert f*z2 eq (1-AL)*f;

z := AL*(AL-2)*z1 + (AL-1)*(AL+1)*z2;
assert e^2 eq -z;
assert f^2 eq -z;
assert e*f eq -1/2*z;

// So B is isomorphic to the split spin factor algebra with mu = 1/2 - this is IY_3(-2-r, 1/2, 1/2)

// Need to check for sub ideals of R

r1 := A.1-A.3 + A.4 - A.6;
r2 := A.3-A.5 - (A.2 - A.6);
r3 := A.1+A.3+A.5 + 1/2*(6+3*r)*A.7 -(r+3)*A.8;
r4 := A.2+A.4+A.6 + 1/2*(6+3*r)*A.7 -(r+3)*A.8;

assert forall{ v : v in [r1,r2,r3,r4] | v in R};
assert IsIndependent([r1,r2,r3,r4]);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(8,F)|t1,t2>;
M := GModule(G);
// <r1, r2> is a 2-dim irreducible module
// r3 and r4 both generate trivial modules
// the module structure of R is 2 + 1 + 1

// check whether there are 1 dim ideal of 1+1 submodule
assert r1*r3 eq 1/2*(11*r + 27)*r1;
assert r1*r4 eq 1/2*(11*r + 27)*r1;

assert r2*r3 eq 1/2*(11*r + 27)*r2;
assert r2*r4 eq 1/2*(11*r + 27)*r2;
// NB 11*r+27 \neq 0 as char \neq 3
assert 27^2 - 11^2*6 eq 3;

// For a 1-dim module, require no component of r1, or r2 in the above.  So only possible is
u := r3-r4;

// However, 
assert 6*A.1*u eq (r+3)*(2*r1+r2+r4) - (2*r+3)*r3;
// NB r \eq -3, otherwise 6 = 9, but char \neq 3
assert ideal<A|u> eq R;

// Therefore no 1-dim subideals.  And if a subideal contains a constituent of < r3,r4>, then it also contains <r1,r2>

// Only other option is a 2-dim ideal spanned by r1, r2

assert 6*r1^2 eq 2*(-r-3)*r1 + 4*(-r-3)*r2 + (-r+6)*(r3+r4);
// NB r \neq 6 as this requires 6 = r^2 = 36 and so 30 = 0 and hence char is 2,3,5, a contradiction
// Hence an ideal containg r1 always contains a scalar multiple of r3+r4
assert  ideal<A|r1,r2> eq R;

// So no subideals.

// ---------------------------------

A, gen, frob := M6A(-2+r);

assert Dimension(Nullspace(frob)) eq 4;

// Add in Gaussian Ellimination  **********************************


R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;

B, quo := quo<A|R>;

// Again, B \cong IY_3(r-2,1/2,1/2)
AL := -2+r;

z1 := B.4;
z2 := 1/5*(2*r + 2)*(B.1-B.2+B.3) - 1/5*(-r + 4)*B.4;
e := 2*B.1-AL*z1 -(AL+1)*z2;
f := 2*B.2-AL*z1 -(AL+1)*z2;

assert z1^2 eq z1;
assert z2^2 eq z2;
assert z1*z2 eq 0;

assert e*z1 eq AL*e;
assert f*z1 eq AL*f;
assert e*z2 eq (1-AL)*e;
assert f*z2 eq (1-AL)*f;

z := AL*(AL-2)*z1 + (AL-1)*(AL+1)*z2;
assert e^2 eq -z;
assert f^2 eq -z;
assert e*f eq -1/2*z;

// Need to check for sub ideals of R

r1 := A.1-A.3 + A.4 - A.6;
r2 := A.3-A.5 - (A.2 - A.6);
r3 := A.1+A.3+A.5 + 1/2*(6-3*r)*A.7 + (r-3)*A.8;
r4 := A.2+A.4+A.6 + 1/2*(6-3*r)*A.7 + (r-3)*A.8;

assert forall{ v : v in [r1,r2,r3,r4] | v in R};
assert IsIndependent([r1,r2,r3,r4]);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(8,F)|t1,t2>;
M := GModule(G);
// the module structure of R is 2 + 1 + 1

// Any ideal with a non-trivial Miy action is all of R
assert  ideal<A|r1,r2> eq R;

// check whether there are 1 dim ideal of 1+1 submodule
assert A.1*r3 eq 1/2*(-2*r + 5)*(2*r1+r2) + 1/2*(3*r - 7)*r3 + 1/2*(-2*r + 5)*r4;
assert A.1*r4 eq 1/6*(-5*r + 12)*(2*r1 + r2) + 1/6*(7*r - 18)*r3 + 1/6*(-5*r + 12)*r4;

// For a 1-dim module, require no component of r1, or r2 in the above.  So only possible is
u := 1/6*(-5*r + 12)*r3 - 1/2*(-2*r + 5)*r4;
assert IsZero(A.1*u);
// However
assert ideal<A|u> eq R;
// So no subideals.


////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Case 4
//

// 12*al^2-1*al-2=0
// not char 2 or 3

// This has roots (1 \pm r)/24, where r = \sqrt(97)
P<t> := PolynomialRing(Rationals());
F := SplittingField(t^2-97);
r := -SquareRoot(F!97);
assert r eq F.1;

// bt is
assert Evaluate(bt, (1-r)/24) eq (53-5*r)/192;
assert Evaluate(bt, (1+r)/24) eq (53+5*r)/192;

// Two roots to check
A, gen, frob := M6A((1+r)/24);

assert Dimension(Nullspace(frob)) eq 1;

// Check that this nullspace doesn't become larger over a field with char p

// Check the characteristic polynomial of frob

PP<lm> := PolynomialRing(F);
p := CharacteristicPolynomial(frob);

assert p eq lm*(lm + 1/768*(41*r - 295))^2*(lm + 1/96*(5*r - 43))*(lm + 1/192*(r - 239))^2*(lm^2 - 1/768*(775*r + 9943)*lm + 1/24576*(31175*r + 358295));

// So nullspace can have dim larger than 1 if one of the other factors is simultaneously 0 for some char.

// lm + 1/768*(41*r - 295)
// this is zero only if 41*sqrt(97) = 295
// only if 41^2*97 = 295^2
assert 41^2*97 - 295^2 eq 2^8*3^3*11;
// check char 11
assert (GF(11)!3)^2 eq 97;
// so roots at 3 and -3
assert GF(11)!41*3 ne GF(11)!295;
assert -GF(11)!41*3 eq GF(11)!295;
// But for -3 we have
assert GF(11)!Evaluate(bt, (1-3)/24) eq 1;
// So in char 11, only one algebra, for al = (1+3)/24

// lm + 1/96*(5*r - 43)
assert 5^2*97 - 43^2 eq 2^6*3^2;
// no extra char to check

// (lm + 1/192*(r - 239))^2
assert 239^2-97 eq 2^6*3^4*11;
// check char 11
assert Sqrt(GF(11)!97) ne GF(11)!239;

// lm^2 - 1/768*(775*r + 9943)*lm + 1/24576*(31175*r + 358295)
// This has a factor of lm iff 31175*r + 358295 = 0
assert 358295^2-97*31175^2 eq 2^14 * 3^2 * 5^2 * 11 * 29^2;
// check char 11
assert 31175*Sqrt(GF(11)!97) ne -GF(11)!358295;
// check char 29
assert not IsPower(GF(29)!97,2);
// So we require GF(29^2) to get sqrt(97) and so char 29 doesn't give a solution either

// Hence nullspace has dim 1 in all chars.

Ann := Annihilator(A);
assert Dimension(Ann) eq 1;

R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
assert R eq Ann;

// So the quotient has Monster type
B, quo := quo<A|R>;
assert HasMonsterFusionLaw(B.1 : fusion_values:= [(1+r)/24, (53+5*r)/192]);
assert Dimension(Eigenspace(B.1, 0)) eq 2;
assert Dimension(Eigenspace(B.1, (1+r)/24)) eq 2;
assert Dimension(Eigenspace(B.1, (53+5*r)/192)) eq 2;

// ---------------------

A, gen, frob := M6A((1-r)/24);

assert Dimension(Nullspace(frob)) eq 1;

// Check that this nullspace doesn't become larger over a field with char p

// Check the characteristic polynomial of frob

PP<lm> := PolynomialRing(F);
p := CharacteristicPolynomial(frob);

assert p eq lm*(lm + 1/768*(-41*r - 295))^2*(lm + 1/96*(-5*r - 43))*(lm + 1/192*(-r - 239))^2*(lm^2 - 1/768*(-775*r + 9943)*lm + 1/24576*(-31175*r + 358295));

// NB bt = -al^2/(4*(2*al-1));
AL := (1-r)/24;
assert -AL^2/(4*(2*AL-1)) eq 1/192*(-5*r+53);
assert (192-53)^2 - 25*97 = 2^9*3*11;
// bt eq 1 in this case, so no char 11
assert -((1-Sqrt(GF(11)!97))/24)^2/(4*(2*((1-Sqrt(GF(11)!97))/24)-1)) eq 1;
// This is as above when we checked for polys coinciding at the begining.

// lm + 1/768*(-41*r - 295)
// this is zero only if -41*sqrt(97) = 295
// only if 41^2*97 = 295^2
assert 41^2*97 - 295^2 eq 2^8*3^3*11;

// lm + 1/96*(-5*r - 43)
assert 5^2*97 - 43^2 eq 2^6*3^2;

// (lm + 1/192*(-r - 239))^2
assert 239^2-97 eq 2^6*3^4*11;

// lm^2 - 1/768*(-775*r + 9943)*lm + 1/24576*(-31175*r + 358295)
// This has a factor of lm iff -31175*r + 358295 = 0
assert 358295^2-97*31175^2 eq 2^14 * 3^2 * 5^2 * 11 * 29^2;
// check char 29
assert not IsPower(GF(29)!97,2);
// So we require GF(29^2) to get sqrt(97) and so chr 29 doesn't give a solution either

// Hence nullspace has dim 1 in all chars.

Ann := Annihilator(A);
assert Dimension(Ann) eq 1;

R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
assert R eq Ann;

// So the quotient has Monster type
B, quo := quo<A|R>;
assert HasMonsterFusionLaw(B.1 : fusion_values:= [(1-r)/24, (53-5*r)/192]);
assert Dimension(Eigenspace(B.1, 0)) eq 2;
assert Dimension(Eigenspace(B.1, (1-r)/24)) eq 2;
assert Dimension(Eigenspace(B.1, (53-5*r)/192)) eq 2;


// -----------------------------------------
//
// idempotents
//
// -----------------------------------------
load "Find idempotents.m";

A , gen, frob := M6A();
F<al> := BaseRing(A);

I := IdempotentIdeal(A);



///////////////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////             6J(2bt, bt)

///////////////////////////////////////////////////////////////////////////////////////////////////////////

A, gens, frob := M6J();
F<bt> := BaseRing(A);

so, id:= HasOne(A);
assert so;
assert id eq 1/(7*bt+1)*A![1,1,1,1,1,1,1,1];

assert Determinant(frob) eq -(2*bt-1)^2*(bt-2)^5*(7*bt+1)/16;

// Since al = 2*bt \neq 1, the only solutions are bt = 2, -1/7




// Since al = 2*bt \neq 1, the only solutions are bt = 2, -1/7

// Since bt neq 0, none of the entries in frob are 0 
// The projection graph is strongly connected 
// No Ideals conataining Axes

Orbit1 := [A.1, A.3, A.5];
Orbit2 := [A.2, A.4, A.6];

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

assert A.1*t2 in Orbit1;
assert A.1*t2*t1 in Orbit1;
assert A.2*t1 in Orbit2;
assert A.2*t1*t2 in Orbit2;

assert  InnerProduct(Vector(A.1*t2)*frob, Vector(A.2*t1)) eq bt;

// So there are no Ideals containing Axes.






// can have bt-2 and bt+1/7 iff char eq 3, or 5.  Can't have char 3 as {1, bt, 2bt} if bt = 2 are not distinct.
// Char 5 works


//////////////////////////////////////////////////////////////////////////////////////////////////////////////

A, gen, frob := M6J(-1/7);

// the Radical is 1 dim
assert Dimension(Nullspace(frob)) eq 1;

P<lm> := PolynomialRing(Rationals());
p := CharacteristicPolynomial(frob);
assert p eq lm^5*(lm+3)*(lm^2 - 14*lm - 75);

// lm + 3 \neq 0, but we can have (lm^2 - 14*lm - 75) iff char is 5
// This is also when bt = 2 and bt = -1/7 coincide.
// Deal with this later

R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
u := A.1+A.2+A.3+A.4+A.5+A.6+A.7+A.8;
assert u in R;

// The Radical being 1 dimensional does not have any sub ideals

// The radical is the annihilator
assert Dimension(Annihilator(A)) eq 1;

// The quotient is 7 dimensional
B, quo := quo<A|R>;
assert sub<B|B.1,B.2> eq B;  // so B is 2-generated
B.1 eq A.1@quo;
B.2 eq A.2@quo;

// The quotient Generating Axes B.1 and B.2 follow the monster fusion law as we mod out by the annihilator


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////

A, gen, frob := M6J(2);
// NB char \neq 3

P<lm> := PolynomialRing(Rationals());
p := CharacteristicPolynomial(frob);
assert p eq lm^5*(lm+3)*(lm^2 - 14*lm - 75);

// Same char poly as for bt = -1/7

// the Radical is 5 dim
assert Dimension(Nullspace(frob)) eq 5;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
u1 := A.1-A.3;
u3 := A.3-A.5;
u2 := A.2-A.4;
u4 := A.4-A.6;
u5 := A.7-1/2*A.8;
assert u1 in R and u2 in R and u3 in R and u4 in R and u5 in R;

// The quotient is 3 dimensional
B, quo := quo<A|R>;
assert sub<B|B.1,B.2> eq B;  // so B is 2-generated
B.1 eq A.1@quo;
B.2 eq A.2@quo;

// The generating axes follow Jordan fusion law
assert HasJordanFusionLaw(B.1: fusion_value:=4);

// So this is 3C(4) = 3C(al);

//----------

// Check for subideals

// NB char neq 2, 3, so ordinary rep theory
// Submodule structure is <<u1, u3>> \oplus << u2, u4>> \oplus << u5>>

assert u1*u5 eq -3*u4;
assert u4*u5 eq -3*u1;
// so no 1-dim subideals
// And if we have any component of u5, then we have all of R

// Check for 2-dim ideals
// Check action of Miy

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

assert u1*t1 eq u1+u3;
assert u3*t1 eq -u3;

assert u2*t1 eq -u4;
assert u4*t1 eq -u4;


assert u1*t2 eq -u1;
assert u4*t2 eq -u4;

// So must pair u1 with u4 to get a * u1 + b * u4
assert A.1*u1 eq 2*u1;
assert A.1*u4 eq 2*u4 -2*u5;
// so b = 0
assert A.4*u1 eq 2*u1 -2*u5;
// so a = 0

// Hence no subideals over any char

//----------
// check when char = 5 and bt = 2 = -1/7

A, gen, frob := M6J(GF(5)!2);

assert Dimension(Nullspace(frob)) eq 6;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
u1 := A.1-A.3;
u3 := A.3-A.5;
u2 := A.2-A.4;
u4 := A.4-A.6;
u5 := A.7-1/2*A.8;
u6 := &+[ A.i : i in [1..8]];

assert u1 in R and u2 in R and u3 in R and u4 in R and u5 in R and u6 in R;

Ann := Annihilator(A);
assert u6 in Ann;
Assert Dimension(Ann) eq 1;

// So we still have the same cases as above and they are disjoint
// R = 1+5
// Quotient by the 5-dim ideal is 3C(-1), which has a 1-dim quoitient, so this agrees

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

//////////////////             6Y(1/2, 2)

///////////////////////////////////////////////////////////////////////////////////////////////////////////

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



