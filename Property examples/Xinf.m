/*

Check the algebras which normally have the infinite axet

*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");

Attach("../Yabe_algebras.m");

QQ := Rationals();
ZZ := Integers();
// =========================================================
//
// IY3
//
// =========================================================






// Check isomorphisms
// mu = -1 gives 3 axes
M := Matrix(Rationals(),2,2,[1,-1/2,-1/2,1]);
A, frob := SplitSpinFactor(M);
F<al> := BaseRing(A);

a1 := 1/2*(A.1+al*A.3+(al+1)*A.4);
a2 := 1/2*(A.2+al*A.3+(al+1)*A.4);

t1 := MiyamotoInvolution(a1,1/2);
t2 := MiyamotoInvolution(a2,1/2);
assert Order(t1*t2) eq 3;

a3 := a1*t2;

so, id := HasOne(A);
assert so;
assert id eq A.3+A.4;

lm := -al*(3*al^2+3/2*al-3/2)/(4*(2*al-1));
assert lm eq -3/8*al*(al+1);
z := lm*id;

bas := [a1,a2,a3,z];
assert forall{v : v in bas | z*v eq lm*v};

assert a1*a2 eq (al+1/2)/2*(a1+a2) + (al-1/2)/2*a3 + z;

// So IY_3(al,1/2,-1/2) \cong 3A(al, 1/2)


// Look at char 3
M := Matrix(GF(3),2,2,[1,1,1,1]);
A, frob := SplitSpinFactor(M);
F<al> := BaseRing(A);

a1 := 1/2*(A.1+al*A.3+(al+1)*A.4);
a2 := 1/2*(A.2+al*A.3+(al+1)*A.4);

t1 := MiyamotoInvolution(a1,1/2);
t2 := MiyamotoInvolution(a2,1/2);
assert Order(t1*t2) eq 3;

a3 := a1*t2;
so, id := HasOne(A);
assert so;
assert id eq A.3+A.4;

// So this is not isomorphic to 3A(al,1/2) in char 3 as 3A has no id and instead has an annihilator.
// The quotient 3A/Ann \cong 3C(-1) in char 3.

assert Dimension(Nullspace(frob)) eq 1;
R := ideal<A|[ A!v : v in Basis(Nullspace(frob))]>;
assert A.1-A.2 in R;

B,quo := quo<A|R>;
// We are quotienting by difference of axes, so all axes are equal in the quotient.
assert a1-a2 in R and a1-a3 in R;


// There are additional axes in the quotient
z1 := A.3;
assert HasJordanFusionLaw(z1@quo: fusion_value:=al);
d := 1/2*(-A.1 + al*A.3+(al+1)*A.4);

assert HasJordanFusionLaw(d@quo: fusion_value:=al);
assert a1*z1- al/2*(a1+z1-d) in R;
// so quotient is 3C(al), but the image of our generating axes only gives us 1 axis, not 2.


// =========================================================
//
// IY5
//
// =========================================================
A, gens, frob := V2();
F<al> := BaseRing(A);

assert not HasOne(A);

// Subalgebras??
// No axial subalgebras - show that a_0 and a_i generate A

// So no ideals containing an axis
assert forall{i : i in [2..5] | frob[1,i] eq 1};

R := ideal<A | [A!Vector(v) : v in Basis(NullSpace(frob))]>;

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(6,F)|t1,t2>;

z := A.6;
u1 := A![1,-4,6,-4,1,0];


assert z in R and u1 in R;

// A has a 1-dim annihilator
Ann := Annihilator(A);
assert Dimension(Ann) eq 1 and u1 in Ann;


// z and u1 span the fixed submodule of G
M := GModule(G);
fix := Fix(M);  // The fixed submodule
assert Dimension(fix) eq 2;
assert M!Vector(z) in fix;
assert M!Vector(u1) in fix;

assert z^2 eq (2*al-3)*(2*al-1)/32*u1;
assert A.3*z eq (2*al-1)/8*( (A.2+A.4) - 2*A.3 + 4*z );
// So the fixed submodules is not an ideal.

// Look at module structure of M
N4 := sub<M | M.1-M.2>;
assert Dimension(N4) eq 4;
// take differences: M.1-M.2 - (M.2-M.3) = M.1-2*M.2+M.3
N3 := sub<M | M.1-2*M.2+M.3>;
assert Dimension(N3) eq 3;
// take differences: M.1-2*M.2+M.3 - (M.1-2*M.2+M.3) = M.1-3*M.2+3*M.3-M.4
N2 := sub<M | M.1-3*M.2+3*M.3-M.4>;
assert Dimension(N2) eq 2;
// take differences: M.1-3*M.2+3*M.3-M.4 - (M.2-3*M.3+3*M.4-M.5) = M.1-4*M.2+6*M.3-4*M.4+M.5
// And this is the annihilator

// So the module structure of the radical is 1+4, where <z> \oplus N4

// We have the annihilator
I1 := ideal<A | A![1,-4,6,-4,1,0]>;
assert Ann eq I1;
B1, quo1 := quo<A | I1>;
assert not HasOne(B1);
assert Dimension(Annihilator(B1)) eq 0;


// Try differences of differences of axes
I2 := ideal<A | A![1,-3,3,-1,0,0]>;
assert Dimension(I2) eq 2;
B2, quo2 := quo<A|I2>;

// This is a new algebra!!
assert A.1@quo2 eq B2.1 and A.2@quo2 eq B2.2;
assert sub<B2 | B2.1, B2.2> eq B2;
assert HasMonsterFusionLaw(B2.1:fusion_values:=[al,1/2]);
assert Dimension(Eigenspace(B2.1, 0)) eq 1;
assert Dimension(Eigenspace(B2.1, al)) eq 1;
assert Dimension(Eigenspace(B2.1, 1/2)) eq 1;
// It is 4-dim and has al in eigenspace

assert not HasOne(B2);
assert Dimension(Annihilator(B2)) eq 1;
assert B2![1,-2,1,-2/(al-1/2)] in Annihilator(B2);

// trying to look at the module obtained by differences again doesn't work
II := ideal<A | A![1,-2,1,0,0,0]>;
assert Dimension(II) eq 4;

// quotient by the annihilator, not the differences again
I3 := ideal<A | A![1,-2,1,0,0,-2/(al-1/2)]>;
assert Dimension(I3) eq 3;
B3, quo3 := quo<A | I3>;

assert A.1@quo3 eq B3.1 and A.2@quo3 eq B3.2;
assert sub<B3 | B3.1, B3.2> eq B3;
assert HasMonsterFusionLaw(B3.1:fusion_values:=[al,1/2]);
assert Dimension(Eigenspace(B3.1, 0)) eq 0;
assert Dimension(Eigenspace(B3.1, al)) eq 1;
assert Dimension(Eigenspace(B3.1, 1/2)) eq 1;

u := B3![1,-2,1];

w := B3.1*B3.2;
assert w*w eq (1/4-al)*(B3.1+B3.2) - (2*al+1/2)*w;
// This is Maddy Whybrow's example in fusion law d in
// Graded 2-generated axial algebras, https://arxiv.org/abs/2005.03577


// u is the common al eigenspace
assert forall{ i : i in [1..3] | B3.i*u eq al*u};

//
I4 := ideal<A | A.1-2*A.2+A.3>;
assert Dimension(I4) eq 4;
basI4 := [z, u1, (A.1+A.3)-2*A.2, (A.2+A.4)-2*A.3];
assert IsIndependent(basI4);
assert forall{ v : v in basI4 | v in I4};

B4, quo4 := quo<A | I4>;
assert Dimension(B4) eq 2;
assert A.1@quo4 eq B4.1 and A.2@quo4 eq B4.2;
assert B4.1*B4.2 eq 1/2*(B4.1+B4.2);
// so the quotient is S(2)^\circ





