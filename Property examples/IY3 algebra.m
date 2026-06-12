/*
**********************************

Code to verify properties of the IY_3(al, 1/2; mu) algebra

**********************************
*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");

Attach("../Yabe_algebras.m");

load "Find idempotents.m";
QQ := Rationals();
// =========================================================
//
// IY3
//
// =========================================================
A, gens, frob := IY3();
F<al> := BaseRing(A);
bt := 1/2;

// Confirm the algebra is indeed a 2-generated Monster type algebra

assert sub<A | gens> eq A;
assert HasMonsterFusionLaw(gens[1]: fusion_values:=[al, bt]);
assert HasMonsterFusionLaw(gens[2]: fusion_values:=[al, bt]);
assert IsFrobeniusForm(frob, A);

// The matrix [[1,mu],[mu,1]] has rank drop iff mu = pm 1.  This gives a non-trivial radical to the resulting algebra.
// This algebra should be simple provided al ne -1,2 and mu ne \pm 1

//////////////////////////////
// First case, if mu = 1
// This is the exceptional algebra
F<al> := FunctionField(QQ);
A, gens, frob := IY3(al,1);

_, _, FL := IdentifyFusionLaw(A.1: eigenvalues:=[1,0,al,1/2]);
Gr, gr := Grading(FL);
assert Order(Gr) eq Infinity();
assert NumberOfGenerators(Gr) eq 1;
assert IsAbelian(Gr);
// So the axes here are Z-graded
assert 2@gr eq 2*Gr.1;
assert 3@gr eq 2*Gr.1;
assert 4@gr eq Gr.1;
// But we can use a C_2-grading

null := NullSpace(frob);
assert Dimension(null) eq 3;
R := ideal<A | [A!v : v in Basis(null)]>;

assert A.1-A.2+A.3-2*A.4 in R and A.3 in R and A.4 in R;
assert A.1*(A.1-A.2+A.3-2*A.4) eq 1/2*(A.1-A.2+A.3-2*A.4);
// These vectors span the bt-, al-, 0-eigenspaces for A.1.  So these and their sums are the only candidates for ideals.

I0 := ideal<A | A.4>;
assert I0 eq Annihilator(A);
assert Dimension(I0) eq 1;

Q0, pi := quo<A | I0>;

assert A.1@pi eq Q0.1 and A.2@pi eq Q0.2;
assert Q0.1*Q0.2 eq 1/2*(Q0.1+Q0.2) + (al-1/2)*Q0.3;
assert Q0.1*Q0.3 eq al*Q0.3;
assert Q0.2*Q0.3 eq al*Q0.3;
assert Q0.3*Q0.3 eq Q0!0;
// This is Maddy Whybrow's example in fusion law (a), with bt = 1/2, x = 1 in
// Graded 2-generated axial algebras, https://arxiv.org/abs/2005.03577
assert Q0.1*(Q0.1*Q0.2) eq (al-1)*(1/2-1)*Q0.1 -al/2*Q0.2 +(al+1/2)*Q0.1*Q0.2;
assert (Q0.1*Q0.2)*(Q0.1*Q0.2) eq (1/2*(al-1)*(al+1/2-1) - al/2*(al+1/2))*(Q0.1+Q0.2)
                                    + ((1-al)*(al-1/2+1) + al^2 + 3/2*al + 2*(1/2)^2 -1/2)*Q0.1*Q0.2;

// Also type (d) when bt = 1/2 - these are isomorphic!!
// In fact, the axes here are Z-graded

Ial := ideal<A | A.3>;
assert Dimension(Ial) eq 1;

// This is \widehat{S(2)^circ}
Qal, pi := quo<A | Ial>;
assert HasJordanFusionLaw(Qal.1:fusion_value:=1/2);
assert HasJordanFusionLaw(Qal.2:fusion_value:=1/2);
assert Dimension(Annihilator(Qal)) eq 1;
assert Qal.1*Qal.2 eq 1/2*(Qal.1+Qal.2) + Qal.3;

// So I0+Ial is an ideal
// quotient is S(2)^\circ

// A.1-A.2 generates the entire R
assert A.2*(A.1-A.2+A.3-2*A.4) eq 1/2*(A.1-A.2+A.3-2*A.4) +(2*al-1)*A.3 +2*A.4;
// so (2*al-1)*A.3 +2*A.4 is in the ideal.
// but ideals must be the sum of eigenspaces, so this is all of R
assert ideal<A | A.1-A.2> eq R;

/////////////////////////////
// Second case, if mu ne 1 and al = -1

F<mu> := FunctionField(QQ);
A, gens, frob := IY3(-1, mu);

null := NullSpace(frob);
P<t> := PolynomialRing(F);
assert  CharacteristicPolynomial(frob) eq t*(t-1)*(t-3*(mu+1))*(t+3*(mu-1));
// So if mu ne -1, 1, then the dimension of the nullspace is 1

assert Dimension(null) eq 1;
R := ideal<A | [A!v : v in Basis(null)]>;
assert Annihilator(A) eq R;
assert A.4 in R;

Q, pi := quo<A|R>;
// So the eigenvalues are 1, -1, 1/2
// This is IY3(-1,1/2;mu)^\times

// The case of mu = 1 is dealt with above
// so do mu = -1

A, gens, frob := IY3(Rationals()!-1, -1);
a0 := gens[1];

null := NullSpace(frob);
assert Dimension(null) eq 2;
R := ideal<A | [A!v : v in Basis(null)]>;
assert A.1+A.2 in R and A.4 in R;
// These are the bt- and 0-eigenvectors for A.1
assert a0*(A.1+A.2) eq 1/2*(A.1+A.2);

// So these are the only candidates for a 1-dim ideal.

assert Annihilator(A) eq sub<A|A.4>;
// The quotient here is IY3(-1,1/2;1)^\times

assert gens[2]*(A.1+A.2) eq 1/2*(A.1+A.2);
// so this is a common bt-eigenspace.
Ibt := ideal<A|A.1+A.2>;
assert Dimension(Ibt) eq 1;

// It's quotient must be of Jordan type -1 and so isomorphic to 3C(-1)
Qbt, pi := quo<A|Ibt>;
a := gens[1]@pi;
b := gens[2]@pi;

c := a+b +2*a*b;
assert IsIdempotent(c);

// So the quotient by R is 3C(-1)^\times

/////////////////////////////
// Third case, if mu ne 1 and al ne -1

A, gens, frob := IY3();

P<t> := PolynomialRing(F);
assert CharacteristicPolynomial(frob) eq (t -(al+1))*(t + (al-2))*(t+(1-mu)*(al+1)*(al-2))*(t+(1+mu)*(al+1)*(al-2));
// so as expected the critical values are when mu = \pm 1 and al = -1, al = 2

// By above, can assume that mu ne 1 and al ne -1

// al = 2
A, gens, frob := IY3();
FF<al,mu> := BaseRing(A);

F<mu> := FunctionField(QQ);
phi := hom<FF->F | [2,mu]>;

A := ChangeRing(A, F, phi);
frob := ChangeRing(frob, F, phi);

null := NullSpace(frob);
assert Dimension(null) eq 3;
R := ideal<A | [ Eltseq(v) : v in Basis(null)]>;
assert A.1 in R and A.2 in R and A.4 in R;

// The Miyamoto group has a 2-dim module generated by A.1 and A.2 and fixes A.4

assert A.1*A.4 eq -A.1;
assert A.2*A.4 eq -A.2;
// hence A.4 does not span a 1-dimensional ideal
// In particular, this is R in any characteristic

assert A.1*A.1 eq -3*A.4;
assert A.2*A.2 eq -3*A.4;
assert A.1*A.2 eq -3*mu*A.4;

// If re+sf generates a proper ideal then need r + mu s = 0 = r mu + s
// Then mu^2 = 1 and so mu = 1 and r=s=1

// In this case, e+f is an ideal and so 

// so as char F ne 3, the only ideal is R

// mu = -1
A, gens, frob := IY3();
FF<al,mu> := BaseRing(A);

F<al> := FunctionField(QQ);
phi := hom<FF->F | [al,-1]>;

A := ChangeRing(A, F, phi);
frob := ChangeRing(frob, F, phi);

null := NullSpace(frob);
assert Dimension(null) eq 1;
R := ideal<A | [ Eltseq(v) : v in Basis(null)]>;
assert A.1+A.2 in R;
// This can only be the common bt-eigenspace
// So the quotient is 3C(al)


// -------------------------------------------
//
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

// NB in char 3, -1/2 = 1 and we still have the isomorphism, but it is instead with IY_3(\al, 1/2, 1)






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




// ----------------------------------------------
//
// Check idempotents
//

// Split spin factor paper covers all cases except IY3(al,1/2;1)
F<al> := FunctionField(QQ);
A, gens, frob := IY3(al,1);

I := IdempotentIdeal(A);
prim := PrimaryDecomposition(I);

assert #prim eq 2;
assert exists(J0){ J : J in prim | Dimension(J) eq 0};
assert VarietySizeOverAlgebraicClosure(J0) eq 1;
// This is the just the 0 vector

assert exists(J1){ J : J in prim | Dimension(J) eq 1};
P<t1,t2,t3,t4> := Generic(J1);

assert J1 eq ideal<P | t1+t2-1, t2^2-t2+t4/2, t3 + t4/2>;
// NB in the forbidden paper, there is an extra (2al-1) which is wrong!
// These are all axes

// ----------------------------------------------
//
// Check automorphism group when mu = 1

F<al>:=FunctionField(Rationals());
A, gens, frob := IY3(al,1);

bas := [A.1+A.2, A.1-A.2, A.3-2*A.4, A.4];
AA := ChangeBasis(A, bas);

P := PolynomialRing(F, 8);
AP := ChangeRing(AA, P);
g := Matrix([[1, P.1, P.2, P.3],
             [0, P.4, P.5, P.6],
             [0,   0, P.7, 0  ],
             [0,   0,   0, P.8]]);

assert (AP.1*AP.3)*g eq 2*al*(P.7*AP.3 + 2*P.8*AP.4);
assert (AP.1*g)*(AP.3*g) eq 2*al*P.7*(AP.3 + 2*AP.4);
// So P.7 = P.8;

assert AP.2^2*g eq -(2*al-1)*P.7*AP.3 - 4*al*P.8*AP.4;
assert (AP.2*g)*(AP.2*g) eq P.4^2*(-(2*al-1)*AP.3 - 4*al*AP.4);

assert (AP.1*AP.2)*g eq P.4*AP.2 + P.5*AP.3 + P.6*AP.4;
assert (AP.1*g)*(AP.2*g) eq P.4*AP.2 + (2*al*P.5 -(2*al-1)*P.1*P.4)*AP.3 -4*al*(P.1*P.4 -P.5)*AP.4;

assert AP.1^2*g eq 2*AP.1 + 2*P.1*AP.2 + (2*P.2 + (2*al-1)*P.7)*AP.3 + 2*(P.3 + 2*al*P.8)*AP.4;
assert (AP.1*g)*(AP.1*g) eq 2*AP.1 + 2*P.1*AP.2 + ( (2*al-1)*(1-P.1^2) + 4*al*P.2)*AP.3 + 4*al*(1 + 2*P.2 -P.1^2)*AP.4;

// So we get
assert (AP.1*AP.3)*g - (AP.1*g)*(AP.3*g) eq 4*al*(P.8-P.7)*AP.4;
assert AP.2^2*g - (AP.2*g)*(AP.2*g) eq (2*al-1)*(P.4^2-P.7)*AP.3 +4*al*(P.4^2-P.8)*AP.4;
assert (AP.1*AP.2)*g - (AP.1*g)*(AP.2*g) eq (2*al-1)*(P.1*P.4 - P.5)*AP.3 + (P.6 + 4*al*(P.1*P.4 -P.5))*AP.4;
assert AP.1^2*g - (AP.1*g)*(AP.1*g) eq (2*al-1)*( (P.1^2 - 1) - 2*P.2 + P.7)*AP.3 + 2*(P.3 + 2*al*(P.1^2 + P.8 - 2*P.2 - 1))*AP.4;

I := ideal<P | P.7-P.8, P.4^2-P.7, P.4^2-P.8, P.1*P.4 - P.5, P.6 + 4*al*(P.1*P.4-P.5), (P.1^2 - 1) - 2*P.2 + P.7, P.3 + 2*al*(P.1^2 + P.8 - 2*P.2 - 1)>;

// define everything in terms of P.1 and P.4
assert P.2 -1/2*(P.1^2+P.4^2-1) in I;
assert P.3 in I;
assert P.5 -P.1*P.4 in I;
assert P.6 in I;
assert P.7-P.4^2 in I;
assert P.8 - P.4^2 in I;

P<gm1, dl1, gm2, dl2> := PolynomialRing(F,4);

AP := ChangeRing(AA, P);

function aut(gm, dl)
  return Matrix([[1, gm, 1/2*(gm^2+dl^2-1), 0],
             [0, dl, gm*dl, 0],
             [0,   0, dl^2, 0  ],
             [0,   0,   0, dl^2]]);
end function;

g := aut(gm1, dl1);
h := aut(gm2, dl2);

assert g*h eq aut(gm1*dl2+gm2, dl1*dl2);

assert forall{<i,j> : i,j in [1..4] | (AP.i*g)*(AP.j*g) eq (AP.i*AP.j)*g};
// so g is an automorphism




