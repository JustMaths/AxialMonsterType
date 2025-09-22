AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");


///////////////////////////////////////////////////////////////////////////////////////////

////////////////                  6A(al, (-al^2)/(4(2al-1)))

//////////////////////////////////////////////////////////////////////////////////////////

A , gen, frob := M6A();
F<al> := BaseRing(A);

bt := -al^2/4/(2*al-1);

assert bt-1 eq (-al^2-8*al+4)/(4*(2*al-1));
assert al-bt eq al*(9*al-4)/(4*(2*al-1));


// Identity
so, id := HasOne(A);
assert so;
assert id eq 1/(12*al^2-al-2) * ( 2*(2*al-1)*A![1,1,1,1,1,1,0,0] + (5*al -2)*A.7 + (4*(2*al-1)*(3*al-1))/(3*al-2)*A.8);
// Always has an identity unless 12*al^2-al-2=0 or al = 2/3

// 0-Eigenvalues
u1 := al*A.1-(A.4+A.7);
u2 := al*(3*al-2)*(7*al-3)/(2*al-1)*A.1 - 2*(3*al-2)*(A.3+A.5) - 2*(5*al-2)*A.8;
u3 := (3*al-2)*(A.2+A.6 -al/2/(2*al-1)*A.4) +al*A.8;

assert A.1*u1 eq 0;
assert A.1*u2 eq 0;
assert A.1*u3 eq 0;

v1 := al*A.1 -2*(2*al-1)*(A.3+A.5-A.8);
v2 := A.4-A.7;

assert A.1*v1 eq al*v1;
assert A.1*v2 eq al*v2;

// The orbit projection graph is connected 
assert frob[1,4] eq al/2;
// So there are no Ideals containing Axes.

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

1. al = 2/3 and char \neq 5

2. al = 4/7 and char \neq 5

3. al^2+4*al-2=0
  a. Not char eq 5
  b. char 5, al = 2/3 = -1
  c. char 5, al = 4/7 = 2

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

// the Radical is 5-dim if char is not 5
assert Dimension(Nullspace(frob)) eq 5;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;
u1 := A.1 - A.3;
u2 := A.1 - A.5;
u3 := A.4 - A.6;
u4 := A.4 - A.2;
z := A.8;
assert u1 in R and u2 in R and u3 in R and u4 in R and z in R;
assert IsIndependent([u1,u2,u3,u4,z]);

// The quotient is 3 dimensional
B, quo := quo<A|R>;
assert sub<B|A.1@quo, A.2@quo> eq B;  // so B is 2-generated
assert HasJordanFusionLaw(A.1@quo : fusion_value:=4/7);
assert HasJordanFusionLaw(A.2@quo : fusion_value:=4/7);
// So the quotient is a 3C(4/7)

// Now check for other ideals of R
// Char \neq 3, so ordinary rep theory
// It is clear that the submodule structure is <u1,u3> \oplus <u_2,u_4> \oplus <u5>

// No 1-dim ideal.  Any constituent with z also contains <u1,u2> and <u3,u4> in any characteristic (NB al=4/7 => char \neq 7)
assert -7/2*A.1*z eq u1 + u2 + z;
assert -7/2*A.4*z eq u3 + u4 + z;

assert ideal<A|z> eq R;

// Now suppose that I contains a submodule isomorphic to the 2-dim irreducible
// So it contains some diagonal copy inside 2+2
// Clearly u1 pairs with u3 and u2 pairs with u4

assert 7*A.1*u1 eq  u1 + 5*u2 + 3*z;
assert 7*A.1*u3 eq  2*( u1+u2 - u3 + u4 +z);

assert 7*A.1*u2 eq  5*u1 + u2 + 3*z;
assert 7*A.1*u4 eq  2*( u1+u2 + u3 - u4 +z);

// Must contain z, unless possibly char = 5 and take u1+u3 and u2+u4

// Unless we are in this case, by the above, must contain u1,u2,u3 and u4

// So no subideals

////////////////////////////////////////////////////////////////////////////////////////////////////////
//
// Case 3
//
// al^2+4*al-2=0

// First assume not (char eq 5 and al = -1, or 2)

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
// Let \zeta be a square root of 6
for zt in [r, -r] do
  AL := -2+zt;
  A, gen, frob := M6A(AL);

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

  AddRow(~M, 5/4*zt, 7,8);

  AddRow(~M, zt/4, 7, 3);
  AddRow(~M, -3, 3, 8);

  SwapRows(~M, 4, 7);

  SwapRows(~M, 1, 4);
  MultiplyRow(~M, -1, 1);
  AddRow(~M, -1, 1, 4);
  AddRow(~M, -1/8*(zt+4), 1, 2);

  AddRow(~M, 1, 2, 4);

  SwapRows(~M, 3, 4);

  // The matrix is now in Row Echelon Form
  assert M[1,1] eq 1;
  assert forall{ j : j in [2..8] | M[j,1] eq 0};

  assert M[2,2] eq 1/8*(-zt+4);
  assert forall{ j : j in [3..8] | M[j,2] eq 0};

  assert M[3,3] eq -3/8*(-zt+4);
  assert forall{ j : j in [4..8] | M[j,3] eq 0};

  assert Eltseq(M[4]) eq [0,0,0,0,0,0, 5/4*AL, 5/4*(AL-1)];  // is zero in char 5

  // The last 4 rows are all zero
  assert forall{ j : j in [5..8] | IsZero(M[j])};

  // Note that zt = -4 iff 6 = zt^2 = 16 iff char eq 5
  // Since char \neq 5, rows M[2,2] and M[3,3] are always non-zero

  // Note that the last row cannot be zero
  // Hence rank of M=frob is always 4 in any char.

  R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;

  B, quo := quo<A|R>;

  // We identify the quotient
  z1 := A.7@quo;
  z2 := 2/15*(2*zt-3)*A.8@quo; // NB in char 5 we just map 1/2A.8@quo and then this should be in the annihilator of the algebra
  e := 2/3*(A.1-A.3 + A.1-A.5)@quo;
  f := 2/3*(-(A.1 - A.3) + 2*(A.1-A.5) )@quo;

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

  // So B is isomorphic to the split spin factor algebra with mu = 1/2 - this is IY_3(AL, 1/2, 1/2)


  // Need to check for sub ideals of R
  // be careful to make the analysis valid in char 5 where possible and be explicit where extra work is required
  
  r1 := A.1-A.3 + A.4 - A.6;
  r2 := A.1-A.5 + A.4 - A.2;
  r3 := A.1+A.3+A.5 - (A.2+A.4+A.6);
  r4 := A.1+A.3+A.5+A.2+A.4+A.6 -3*AL*A.7 +2*(AL-1)*A.8;

  assert forall{ v : v in [r1,r2,r3,r4] | v in R};
  assert IsIndependent([r1,r2,r3,r4]);

  t1 := MiyamotoInvolution(A.1);
  t2 := MiyamotoInvolution(A.2);
  G := sub<GL(8,F)|t1,t2>;
  M := GModule(G);
  // <r1, r2> is a 2-dim irreducible module
  // r3 and r4 both generate trivial modules
  // the module structure of R is 2 + 1 + 1

  // First consider an ideal I which has a constituent <r1,r2>
  assert 6*r1^2 eq -2*(AL-1)*r1 + 4*(AL-1)*r2 + (zt+6)*r4;
  assert 4*(A.1-A.4)*r1 eq (4-zt)*r3;
  assert 4-zt eq 2-AL;

  // at least one of zt-6 and 4-zt are not zero.  Otherwise zt = 4 = -6, hence char = 5 and zt = -1
  
  // Hence I contains a constituent which is a trivial module

  // So now may assume that I is a trivial module. 
  assert r3^2 eq zt/2*r4;
  assert r3*r4 eq 3/2*(9*zt-22)*r3;
  assert r4^2 eq 1/2*(5*zt-12)*r4;
  
  assert zt^2*9^2 -22^2 eq 2;
  assert 5^2*zt^2-12^2 eq 6;
  // so neither is zero in any characteristic
  
  // Suppose that the trivial constituent of I is spanned by a linear combination a*r3 + b*r4.  Multiplying by r4, we see that we need 3/2*(9*zt-22) = 1/2*(5*zt-12).  But then,
  
  assert 3/2*(9*zt-22) - 1/2*(5*zt-12) eq 11*zt -27;
  assert 27^2 -11^2*6 eq 3;
  // Hence if I contains a constituent which is a trivial module, it contains the entire <r3,r4>
  
  assert (A.1-A.3)*r3 eq 1/2*(1-AL)*r1;
  // Hence if I contains a constituent which is a trivial module, then it contains <r1,r2> also
  
  // So no subideals unless possibly char = 5 AND zt = 1
end for;

// This quotient is also of Monster type and is 6A(2/3,−1/3)^x

// ====================================================================================
//
// GF(5) and al = 2/3 = -1 = -2 + zeta, where zt = 1 is a square root of 6 = 1
//
//
A, gen, frob:= M6A(GF(5)!2/3);
AL := GF(5)!2/3;
assert AL eq -1;
zt := GF(5)!1; // when compared to the -2 \pm \sqrt{6} case

// the Radical is 5 dim
assert Dimension(Nullspace(frob)) eq 5;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;

// Inside R we have the annihilator still
assert A.8 in Annihilator(A);
assert Dimension(Annihilator(A)) eq 1;

r1 := A.1-A.3 + A.4 - A.6;
r2 := A.1-A.5 + A.4 - A.2;
r3 := A.1+A.3+A.5 - (A.2+A.4+A.6);
r4 := A.1+A.3+A.5+A.2+A.4+A.6 -3*AL*A.7 +2*(AL-1)*A.8;

r5 := A.8;

assert forall{ u : u in [r1,r2,r3,r4,r5] | u in R};
assert IsIndependent([r1,r2,r3,r4,r5]);
// So r1, .., r5 is a basis for R

// As zt \neq -1, the subideal analysis is the same as for al = -2 \pm \sqrt{6}

// < r1, r2, r3, r4 > and <z> are disjoint and so are complements.

// It remains to check the quotients

// The quotient by r5 is still 6A(2/3,−1/3)^x

B, quo := quo<A|r1,r2,r3,r4>;

z1 := A.7@quo;
n := 1/2*A.8@quo; // NB this differs by a scalar from the al = -2+rt version
e := 2/3*(A.1-A.3 + A.1-A.5)@quo;
f := 2/3*(-(A.1 - A.3) + 2*(A.1-A.5) )@quo;

assert IsIndependent([z1,n,e,f]);

// check the structure constants wrt this basis
assert z1^2 eq z1;
assert n^2 eq 0;
assert z1*n eq 0;

assert e*z1 eq AL*e;
assert f*z1 eq AL*f;
assert e*n eq 0;
assert f*n eq 0;

z := 3*z1 - 2*n;
assert e^2 eq -z;
assert f^2 eq -z;
assert e*f eq -1/2*z;
// So this is widehat(S)(b,-1)^\circ \cong IY_3(-1,1/2,1/2)

// NB that the quotient by R corresponds to the quotient of B by the nilpotent ideal <n> = <z@quo>

// NB also that B is also isomorphic as an algebra to 3A(4,3) in char 5.
assert HasMonsterFusionLaw(B.1: fusion_values:=[4,3]);
assert Dimension(Eigenspace(B.1,0)) eq 1;
assert Dimension(Eigenspace(B.1,4)) eq 1;
assert Dimension(Eigenspace(B.1,3)) eq 1;
// So B is of Monster type.  It has a 1-dim annihilator

bas := [B.1,B.3,A.5@quo,3*r5@quo];
BB := ChangeBasis(B, bas);

assert [[ Eltseq(e) : e in r] : r in BasisProducts(BB)] eq [[ Eltseq(e) : e in r] : r in BasisProducts(M3A(GF(5)!4, GF(5)!3))];
// So the quotient is equal to 3A, however, the 6 axes are all distinct.


// ====================================================================
//
// Char 5 and al = 2 = 4/7 = -2 -zeta, where zeta = -1 is a sqrt of 6=1
//
//
A, gen, frob := M6A(GF(5)!4/7);
AL := GF(5)!4/7;
assert AL eq 2;
zt := -GF(5)!1; // when compared to the -2 \pm \sqrt{6} case

// Need to edit - error somewhere!!!!!!!!!

assert Dimension(Nullspace(frob)) eq 7;
R := ideal<A| [A!x : x in Basis(Nullspace(frob))]>;

u1 := A.1 - A.3;
u2 := A.1 - A.5;

u3 := A.4 - A.6;
u4 := A.4 - A.2;

r3 := A.1+A.3+A.5 - (A.2+A.4+A.6);
r4 := A.1+A.3+A.5+A.2+A.4+A.6 -3*AL*A.7 +2*(AL-1)*A.8;

r5 := A.8;

assert forall{ v : v in [u1,u2,u3,u4,r3,r4,r5] | v in R};
assert IsIndependent([u1,u2,u3,u4,r3,r4,r5]);

// Module structure is now 2+2+1+1+1

// We have ideals from above:
// from al = 4/7, have < u1,u2,u3,u4,r5 >
// from al = -2+zt have <u1+u3, u2+u4, r3, r4>

U47 := ideal<A | u1, u2, u3, u4, r5>;
Uzt := ideal<A | u1+u3, u2+u4, r3, r4>;

assert Dimension(U47) eq 5;
assert Dimension(Uzt) eq 4;

// These intersect in an ideal
int := U47 meet Uzt;
assert int eq ideal<A | u1+u3, u2+u4>;
assert Dimension(int) eq 2;

// NB in the subideal analysis of al = -2+zt, only this 2-dim ideal is a possible subideal (when zt = -1 in char 5).
// NB in the subideal analysis for al = 4/7, possible subideals are the above intersection only.

B, quo := quo<A|int>;

assert sub<B | A.1@quo, A.2@quo> eq B;
assert HasMonsterFusionLaw(A.1@quo : fusion_values:= [GF(5) | 2, 1/2]);

// This is a quotient of the Highwater algebra
assert forall{ i : i in [1..4] | A.i@quo eq B.i};
assert (A.1-A.2+A.4-A.5)@quo eq 0;
// so this is the minimal relation on the axes

// This quotient is isomorphic to a quotient of the highwater algebra by the identity on the axes generated by
// a_1 - a_2 + a_4 - a_5
HW, gensHW, frobHW := HighwaterQuotient([GF(5)| 1,-1,0,1,-1]);

sg1 := A.1@quo*A.2@quo - 1/2*(A.1+A.2)@quo;
sg2 := A.1@quo*A.3@quo - 1/2*(A.1+A.3)@quo;

bas := [ A.i@quo : i in [1..4]] cat [sg1, sg2];
assert IsIndependent(bas);

BB := ChangeBasis(B, bas);

assert [ [ Eltseq(r) : r in R] : R in BasisProducts(BB)] eq [[ Eltseq(r) : r in R] : R in BasisProducts(HW)];
// hence they are indeed isomorphic


// Here 3C(4/7) = 3C(2)
// it has a 2-dim ideal, with a quotient 1A.  This agrees with the quotient A/R


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

assert  InnerProduct(Vector(A.1*t2)*frob, Vector(A.2*t1)) eq bt;
// Since bt neq 0, none of the entries in frob are 0 
// The projection graph is strongly connected 
// So there are no Ideals containing Axes.

// can have bt=2 and bt=-1/7 iff char eq 3, or 5.  Can't have char 3 as {1, bt, 2bt} if bt = 2 are not distinct.
// Char 5 works


//////////////////////////////////////////////////////////////////////////////////////////////////////////////

A, gen, frob := M6J(-1/7);

// the Radical is 1 dim
assert Dimension(Nullspace(frob)) eq 1;

P<lm> := PolynomialRing(Rationals());
p := CharacteristicPolynomial(frob);
assert p eq lm*(7*lm-15)*(7*lm-9)*(7*lm-8)*(14*lm-15)^4/2^4/7^7;

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
u3 := A.1-A.5;
u2 := A.4-A.6;
u4 := A.4-A.2;
u5 := A.7-1/2*A.8;
assert u1 in R and u2 in R and u3 in R and u4 in R and u5 in R;

assert A.1*u5 eq -u4-u2 + 2*u5;

assert A.1*u1 eq u1-u3;
assert A.1*u2 eq 2*u2-2*u5;

// So no subideals


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

////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////         6Y Idempotents            //////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////
load "Find idempotents.m";
QQ := Rationals();

A, gen, frob := M6Y();

t1 := PermutationMatrix(QQ, [1,4,3,2,5]);
t2 := PermutationMatrix(QQ, [3,2,1,4,5]);
f := PermutationMatrix(QQ, [2,1,4,3,5]);

G := sub<GL(5, QQ) | t1, t2, f>;

I, AP := IdempotentIdeal(A);
assert Dimension(I) eq 1;

P := BaseRing(AP);

prim := PrimaryDecomposition(I);
assert #prim eq 8;

prim0 := [ J : J in prim | Dimension(J) eq 0];
prim1 := [ J : J in prim | Dimension(J) ne 0];

assert {* VarietySizeOverAlgebraicClosure(J) : J in prim0 *} eq {* 1^^4 *};
vars := {@ A![ e : e in t] : t in Variety(J), J in prim0 @};

x1 := A![-2/3,1/3,1/3,0,0];
x2 := A![1/3,-2/3,1/3,0,0];
x3 := A![1/3,1/3,-2/3,0,0];

assert HasJordanFusionLaw(x1: fusion_value:=-1);
assert Dimension(Eigenspace(x1, 0)) eq 3;
assert Dimension(Eigenspace(x1, -1)) eq 1;

assert InnerProduct(x1*frob, x1) eq 0;
// Same holds for x2 and x3
