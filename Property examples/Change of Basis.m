/*

Details change of bases for the 2-generated Monster type algebras from the ones given by Yabe

*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");

QQ := Rationals();

function HasSameStructureConstants(A, B)
  Astr := [ [ Eltseq(v) : v in R] : R in BasisProducts(A)];
  Bstr := [ [ Eltseq(v) : v in R] : R in BasisProducts(B)];
  return Astr eq Bstr;
end function;
// ---------------------
//
// 3A
//
// ---------------------
// None
A, gen, frob := M3A();
AY, _, frobY := III(:specialise:="3A");
assert HasSameStructureConstants(A, AY);

// ---------------------
//
// 4A
//
// ---------------------
// None
A, gen, frob := M4A();
AY, _, frobY := IV1(:specialise:="4A");
assert HasSameStructureConstants(A, AY);

// ---------------------
//
// 4B
//
// ---------------------
// Choose the third axis in <<a_0, a_2>> \cong 3C \cong <<a_1,a_3>>, which is contained in the intersection of these two subalgebras
A, gen, frob := M4B();
AY, _, frobY := IV2(:specialise:="4B");
F<al> := BaseRing(A);

assert AY.1+AY.3 - 2/al*AY.1*AY.3 eq AY![1, 1, 1, 1, 4/al^2];

bas := [AY.i : i in [1..4]] cat [ AY![1, 1, 1, 1, 4/al^2] ];
AY_new := ChangeBasis(AY, bas);

// Change of basis matrix is always full rank in any characteristic
assert Determinant(Matrix(bas)) eq 4/al^2;

assert HasSameStructureConstants(A, AY_new);

// ---------------------
//
// 4J
//
// ---------------------
// Joshi's double Matsuo algebra Table 7 (p4226) in paper with Galt, Joshi, Mamontov, Shpectorov, Staroletov
// We use Joshi's basis, but reordered d1, d3, d2, d4, w
A, gen, frob := M4J();
AY, _, frobY := IV1(:specialise:="4J");
F<bt> := BaseRing(A);

assert 2*(AY.1+AY.2) - 2/bt*AY.1*AY.2 eq -AY![1, 1, 1, 1, 2/bt];

bas := [AY.i : i in [1..4]] cat [ -AY![1, 1, 1, 1, 2/bt] ];
AY_new := ChangeBasis(AY, bas);

// Change of basis matrix is always full rank in any characteristic
assert Determinant(Matrix(bas)) eq -2/bt;

assert HasSameStructureConstants(A, AY_new);

// ---------------------
//
// 4Y_bt
//
// ---------------------
// The two subalgebras <<a_0, a_2>>, <<a_1,a_3>> \cong S(dl), with dl = 2^5*bt*(2*bt-1) + 2, provided bt \neq 1/4.  If $bt = 1/4, then they are S(2)^\circ and don't intersect.
// We choose the 5th basis vector as generically the intersection of these two subalgebras, we normalise so that it is an idempotent.
A, gen, frob := M4Y_bt();
AY, _, frobY := IV2(:specialise:="4Y_bt");
F<bt> := BaseRing(A);

assert 1/2*(AY.1+AY.3) + 1/(4*bt-1)*AY.1*AY.3 eq 1/2*(AY.1+AY.2+AY.3+AY.4) + 1/bt*AY.5;

// this change of basis is valid when bt = 1/4 too.  Just the above equation doesn't hold anymore.
bas := [AY.i : i in [1..4]] cat [ 1/2*(AY.1+AY.2+AY.3+AY.4) + 1/bt*AY.5];
AY_new := ChangeBasis(AY, bas);

// Change of basis matrix is always full rank in any characteristic
assert Determinant(Matrix(bas)) eq 1/bt;

assert HasSameStructureConstants(A, AY_new);

// ---------------------
//
// 4Y_al
//
// ---------------------
// <a_0, a_2> \cong <a_1, a_3> \cong 3C(al), but they intersect not in the third axis, c, but in 1_U-c, where 1_U is the one for the 3C(al).  We choose this element which is also an idempotent (but an axis of Jordan type 1,0, 1-al in the 3C(al)) as the fifth basis element.
// NB that al \neq -1, so we always have a 1_U in the 3C(al).
A, gen, frob := M4Y_al();
AY, _, frobY := IV2(:specialise:="4Y_al");
F<al> := BaseRing(A);

B := sub<AY| AY.1,AY.3>;
assert Dimension(B) eq 3;
so, id_B := HasOne(B);
assert so;
assert id_B eq 1/(al+1)*( 2*(AY.1+AY.3) + (al-1)/al*(AY.2+AY.4) -4/al/(al+1)*AY.5);

c := AY.1+AY.3 - 2/al*AY.1*AY.3;
w := id_B - c;

assert w eq 1/(al+1)*( (1-al)*(AY.1+AY.2+AY.3+AY.4) +4/(al+1)*AY.5 );
// Since al \neq -1, this is always a valid change of basis

bas := [AY.i : i in [1..4]] cat [ w];
AY_new := ChangeBasis(AY, bas);

// Change of basis matrix is always full rank in any characteristic
assert Determinant(Matrix(bas)) eq 4/(al+1)^2;

assert HasSameStructureConstants(A, AY_new);

// ---------------------
//
// 5A
//
// ---------------------
// The Miyamoto group for 5A is D_{10}
// However, the 5A algebra has an extra involutory automorphism phi, and the full automorphism group is a Frobenius group of order 20.
// We pick our last basis vector so it is inverted by this automorphism.
A, gen, frob := M5A();
AY, _, frobY := V1();
F<al> := BaseRing(A);
bt := (5*al-1)/8;

phi_AY := Matrix(F,[[ 1,0,0,0,0,0],
               [ 0,0,1,0,0,0],
               [ 0,0,0,0,1,0],
               [ 0,1,0,0,0,0],
               [ 0,0,0,1,0,0],
               [ -bt/2,-bt/2,-bt/2,-bt/2,-bt/2,-1]]);

// phi_AY is an automorphism of AY
assert forall{ <i,j> : i,j in [1..6] | (AY.i*phi_AY)*(AY.j*phi_AY) eq (AY.i*AY.j)*phi_AY};

// can divide by bt as bt \neq 0
w := &+[ AY.i : i in [1..5]] + 4/bt*AY.6;

assert w*phi_AY eq -w;

bas := [AY.i : i in [1..5]] cat [w];
AY_new := ChangeBasis(AY, bas);

// Change of basis matrix is always full rank in any characteristic
CoB := Matrix(bas);
assert Determinant(CoB) eq 4/bt;

assert HasSameStructureConstants(A, AY_new);

// phi now has a much better structure
phi := Matrix(F,[[ 1,0,0,0,0,0],
               [ 0,0,1,0,0,0],
               [ 0,0,0,0,1,0],
               [ 0,1,0,0,0,0],
               [ 0,0,0,1,0,0],
               [ 0,0,0,0,0,-1]]);

// phi is an automorphism of A
assert forall{ <i,j> : i,j in [1..6] | (A.i*phi)*(A.j*phi) eq (A.i*A.j)*phi};

assert CoB*phi_AY*CoB^-1 eq phi;

// ---------------------
//
// 6A
//
// ---------------------
// In 6A, <<a_0,a_2,a_4>> \cong 3A(al, bt) and <<a_0, a_3>> \cong 3C(al)
// So we choose c to be the third basis vector in the 3C(\al)
// This is in the common intersection of the three 3C subalgebras <<a_0, a_3>>, <<a_1, a_4>> and <<a_2, a_5>>
// There are two 3A subalgebras <<a_0,a_2,a_4>> and <<a_1,a_3,a_5>> and these intersect in a 1-dim subalgebra.
// We choose the z to be in here with some scaling

A, gen, frob := M6A();
AY, _, frobY := VI2();
F<al> := BaseRing(A);
bt := (-al^2)/4/(2*al-1);

// NB Yabe's algebra is not defined for al = 2/5, but our 6A is and is still a Monster type algebra.

c := AY.1+AY.4 - 2/al*AY.1*AY.4;
assert c eq 1/al*( 2*(2*al-1)*AY![1,1,1,1,1,1,0,0] +2*al*(3*al-1)/bt/(al-bt)*AY.7 + 8*(2*al-1)/(5*al-2)*AY.8);

// 3A current last basis vector is
z_3A := AY.1*AY.3 -(al+bt)/2*(AY.1+AY.3) -(al-bt)/2*AY.5;
assert z_3A eq 1/4*(3*al-2)*(AY.1+AY.3+AY.5) + (3*al-2)*(5*al-2)/8/(2*al-1)*(AY.2+AY.4+AY.6)
              - (3*al-2)*(5*al-2)^2/(al-bt)/(2*al-1)/4/al*AY.7 + AY.8;
// If we use this with c for CoB, then get a problem with al=2/5 again.

B1 := sub<AY | AY.1, AY.3>;
B2 := sub<AY | AY.2, AY.4>;
assert Dimension(B1 meet B2) eq 1;

z := -(3*al-2)/al*( AY![1,1,1,1,1,1,0,0] - 2*(5*al-2)/(al-bt)/al*AY.7 + 8*(2*al-1)/(3*al-2)/(5*al-2)*AY.8);
assert z in B1 meet B2;

bas := [AY.i : i in [1..6]] cat [c, z];
AY_new := ChangeBasis(AY, bas);

assert Determinant(Matrix(bas)) eq 4*al/bt^2/(5*al-2);

assert HasSameStructureConstants(A, AY_new);

// ---------------------
//
// 6J
//
// ---------------------
A, gen, frob := M6J();
// This is a (2bt, bt) algebra

AY, _, frobY := VI1();
// Yabe writes this as an (al, al/2) algebra
F<al> := BaseRing(A);
bt := al/2;

u := AY.1+AY.4 - 2/al*AY.1*AY.4;
w := 2*(AY.1+AY.2) - 2/bt*AY.1*AY.2;

bas := [AY.i : i in [1..6]] cat [u, w];
AY_new := ChangeBasis(AY, bas);

// There is a change from (al, al/2) to (2bt, bt)

phi := hom<F->F | [2*al]>;
assert Determinant(Matrix(bas))@phi eq -2/al^2;

Astr := [ [ Eltseq(v) : v in R] : R in BasisProducts(A)];
AY_newstr := [ [ Eltseq(v)@phi : v in R] : R in BasisProducts(AY_new)];

assert Astr eq AY_newstr;

// ---------------------
//
// 6Y
//
// ---------------------
A, gen, frob := M6Y();
AY, _, frobY := IV3();

bas := [AY.1, AY.3, AY.2+AY.3-AY.4, -AY.3+AY.4, AY.5];
AY_new := ChangeBasis(AY, bas);

assert Determinant(Matrix(bas)) eq -1;

assert HasSameStructureConstants(A, AY_new);

// ---------------------
//
// IY3
//
// ---------------------


// ---------------------
//
// IY5
//
// ---------------------
// None
A, gen, frob := IY5();
AY, _, frobY := V2();

assert HasSameStructureConstants(A, AY);

