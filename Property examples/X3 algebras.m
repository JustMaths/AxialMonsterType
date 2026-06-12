/*
******************************

Code to verify properties of Monster type axial algebras with the X(3) axet

******************************
*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";

QQ := Rationals();

// =========================================================
//
// 3A(al, bt)
//
// =========================================================

// Get the algebra, generators and the frobenius form
A, gens, frob := M3A();
F<al,bt> := BaseRing(A);

// Confirm the algebra is indeed a 2-generated Monster type algebra

assert sub<A | gens> eq A;
assert HasMonsterFusionLaw(gens[1]: fusion_values:=[al, bt]);
assert HasMonsterFusionLaw(gens[2]: fusion_values:=[al, bt]);
assert IsFrobeniusForm(frob, A);

// eigenspaces

u0 := (3*al^3+3*al^2*bt-al*bt-al)*A.1 + 4*(2*al-1)*A.4;
ual := al*(al+bt-1)*A.1 + 2*al*(2*al-1)*(A.2+A.3) + 4*(2*al-1)*A.4;
ubt := A.2-A.3;

assert A.1*u0 eq 0;
assert A.1*ual eq al*ual;

assert u0*u0 eq -al*(3*al^2 + 3*al*bt - bt - 1)*u0;
assert u0*ual eq al*(al-1)*(3*al^2 + 3*al*bt - bt - 1)*ual;

assert ual^2 eq al*(3*al - bt - 1)*( -al^2*(3*al^2 + 3*al*bt - 9*al - 2*bt + 4)*A.1 + (al-1)*u0);

// The algebra has an identity if 3*al^2 + 3*al*bt - bt - 1 \neq 0
so, id := HasOne(A);
assert so;
assert id eq -4*(2*al -1)/(al*(3*al^2 + 3*al*bt - bt - 1))*A.4;


assert Determinant(frob) eq -al^2*(3*al - bt - 1)*(3*al^2 + 3*al*bt - bt - 1)*
                                  (3*al^2 + 3*al*bt - 9*al - 2*bt + 4)^3 / ( 2^9*(2*al-1)^5 );

/*

So need to check when bt = 3al-1

and 3*al^2 + 3*al*bt - bt - 1 = 0

and 3*al^2 + 3*al*bt - 9*al - 2*bt + 4 = 0

NB any pair simutaneously hold if and only if char = 3 and bt = -1.  Then all hold simultaneously

*/

// First check for when char = 3
A, gens, frob := M3A(:base_ring:=GF(3));
F<al,bt> := BaseRing(A);

assert Determinant(frob) eq -2*al^2*(bt+1)^5 / (2*al-1)^5;

// So as al \neq 0, just need to consider when bt = -1

FF<Al> := FunctionField(GF(3));
phi := hom<F->FF | [Al,-1]>;
AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

assert frob2 eq Matrix(FF, [[1,1,1,0],[1,1,1,0], [1,1,1,0], [0,0,0,0]]); 
// so nullspace is 3 dimensional
// The nullspace has G-modules structure a trivial module plus a 2-dimensional module, but the Miyamoto group S_3 is divisible by three.

assert Dimension(Annihilator(AA)) eq 1 and AA.4 in Annihilator(AA);
// so this spans a 1-dimensional ideal, which has the 3A^x as the quotient

// The sum of the axes is a 1-dim submodule of the 2-dim module and we have
I := ideal< AA | Al*(AA.1+AA.2+AA.3) + 2*AA.4>;
assert Dimension(I) eq 1;
assert AA.1*(Al*(AA.1+AA.2+AA.3) + 2*AA.4) eq Al*(Al*(AA.1+AA.2+AA.3) + 2*AA.4);
// so this is the simultaneous Al-eigenspace.  Hence the quotient is a 3C(-1);

I := ideal<AA | AA.1+AA.2+AA.3, AA.4>;
assert Dimension(I) eq 2;
// The quotient is 3C(-1)^x

// Only other possible quotient is
I := ideal<AA | AA.1-AA.2, AA.2-AA.3>;
assert Dimension(I) eq 3;
// so this is the full nullspace and has 1A as the quotient

//
// Now can assume char F \neq 3
//
A, gens, frob := M3A();
F<al,bt> := BaseRing(A);

// Let bt = 3al-1
// so 3al - 1 \neq 0

FF<Al> := FunctionField(QQ);
phi := hom<F->FF | [Al,3*Al-1]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

// Checking char poly doesn't help in this case, so
// do row and column ops carefully to calculate the nullspace over all fields

M := AddRow(frob2, -(3/2*Al - 1/2), 1,2);
AddRow(~M, -(3/2*Al - 1/2), 1,3);
AddRow(~M, 3/2*Al^2, 1,4);

// char \neq 3 and Al \neq 0,1
MultiplyRow(~M, 4/(9*Al^2*(Al-1)), 4);
SwapRows(~M, 2,4);

AddRow(~M, 3/4*(Al-1)*(3*Al-1), 2,3);
AddRow(~M, 3/4*(Al-1)*(3*Al+1), 2,4);

AddRow(~M,1,3,4);
// 3al - 1 \neq 0
MultiplyRow(~M, -2/(3*(Al-1)), 3);

assert M[1,1] eq 1 and M[2,2] eq 1 and M[3,3] eq 1;
assert IsZero(M[4]);

// so nullspace has dim 1 in all cases

assert Dimension(Nullspace(frob2)) eq 1;
u_al := Al*(AA.1+AA.2+AA.3) + 2*AA.4;
assert u_al in Nullspace(frob2);

// u_al is the common al-eiegnvector
assert AA.1*u_al eq Al*u_al;
assert IsZero(u_al^2);

// Hence quotient is 3C(3al-1);
I := ideal<AA | u_al>;

B, quo := quo<AA | I>;
assert forall{ i : i in [1..3] | AA.i@quo eq B.i};

assert HasJordanFusionLaw(B.1:fusion_value:=3*Al-1);

// -------------------------------------------------------

// 3*al^2 + 3*al*bt - bt - 1 = 0

// Note, if al = 1/3, then poly is 2/3 \neq 0.  So we can always assume that al \neq 1/3
// so, we have
// bt := (1-3*al^2)/(3al-1)

FF<Al> := FunctionField(QQ);
Bt := (1-3*Al^2)/(3*Al-1);
phi := hom<F->FF | [Al, Bt]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

P<lm> := PolynomialRing(FF);
assert CharacteristicPolynomial(frob2) eq lm*(lm - Al/(Al-1/3))*(lm - (Al-1/2)/(Al-1/3))^2;
// Since char \neq 3 and Al \neq 0, 1/2, the nullspace is dim at most 1

assert Dimension(Nullspace(frob2)) eq 1;
assert AA.4 in Nullspace(frob2);

// This is the annihilator
assert Dimension(Annihilator(AA)) eq 1 and AA.4 in Annihilator(AA);
// Note that this is exactly the case when the algebra has no identity

// So the quotient is 3A^x
I := ideal<AA | AA.4>;

B, quo := quo<AA | I>;
assert forall{ i : i in [1..3] | AA.i@quo eq B.i};

assert HasMonsterFusionLaw(B.1: fusion_values := [Al, Bt]);
assert { e[1] : e in Eigenvalues(B.1)} eq {1, Al, Bt};

// -------------------------------------------------------

// 3*al^2 + 3*al*bt - 9*al - 2*bt + 4 = 0
// Note that if al = 2/3, then the poly is -2/3 \neq 0, so we can always assume that al \neq 2/3

// Since Al ne 2/3
// This has soln bt = (3*Al^2 - 9*Al + 4)/(2-3*Al)
FF<Al> := FunctionField(QQ);
Bt := (3*Al^2 - 9*Al + 4)/(2-3*Al);
phi := hom<F->FF | [Al, Bt]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

assert Dimension(NullSpace(frob2)) eq 3;
// nullspace can't be any larger

so, id := HasOne(AA);
assert id eq -2/3*(3*Al-2)/(Al*(2*Al-1))*AA.4;
// Note that the denominator here is never zero as Al \neq 0,1/2, so we always have an identity.

z1 := AA.1 - id;
z2 := AA.2 - id;
z3 := AA.3 - id;

assert forall{z : z in [z1, z2, z3] | z in Nullspace(frob2)};

// Observe that the Miyamoto group acts on the z_i
// Sicne char F \neq 3, the radical decomposes as the sum of two irreducible modules
// A 1-dimensional trivial and a 2-dim module

assert Dimension(ideal<AA | z1+z2+z3>) eq 3;
assert Dimension(ideal<AA | z1-z2, z2-z3>) eq 3;
// So no additional ideals, hence only quotient is 1A

// --------------------------------------------

// isomorphisms

// If bt = 1/2, then it is isomorphic to IY3(al, 1/2, -1/2);
// Can see from Yabe's definition

// First assume that char F ne 3, al ne -1
F<al> := FunctionField(QQ);
A, gens, frob := M3A(al, 1/2);

e := 2/3*(2*A.1-A.2-A.3);
f := 2/3*(-A.1+2*A.2-A.3);
z1 := -2/3*(A.1+A.2+A.3 + 4/al*A.4);
z2 := 2/3*(A.1+A.2+A.3 + 4/(al+1)*A.4);

assert z1^2 eq z1;
assert z2^2 eq z2;
assert z1*z2 eq 0;
assert e*z1 eq al*e;
assert f*z1 eq al*f;
assert e*z2 eq (1-al)*e;
assert f*z2 eq (1-al)*f;

// from split spin factor paper
z := al*(al-2)*z1 + (al-1)*(al+1)*z2;

assert e^2 eq - z;
assert f^2 eq - z;
assert e*f eq -(-1/2)*z;

// so it is isomorphic to the split spin factor algebra with mu = -1/2

// if char F ne 3 and al = -1;

A := M3A(-1,1/2);
e := 2/3*(2*A.1-A.2-A.3);
f := 2/3*(-A.1+2*A.2-A.3);
z1 := -2/3*(A.1+A.2+A.3 - 4*A.4);
n := 8/3*A.4;

assert z1^2 eq z1;
assert n^2 eq 0;
assert z1*n eq 0;
assert e*z1 eq -e;
assert f*z1 eq -f;
assert e*n eq 0;
assert f*n eq 0;

// from split spin factor paper
z := 3*z1 - 2*n;

assert e^2 eq - z;
assert f^2 eq - z;
assert e*f eq -(-1/2)*z;

// If char = 3, then IY_3(al, 1/2, -1/2) = IY_3(al, -1, 1) and this has a different basis, no identity and an annihilator.

F<al> := FunctionField(GF(3));
A, gens, frob := M3A(al, F!1/2);

z := 2*A![1,1,1,0] + 1/al*A.4;
n := 2/al*A.4;

assert A.1*A.2 eq 1/2*(A.1+A.2) + (al-1/2)*z + n;
assert z^2 eq 0;
assert A.1*z eq al*z;
assert A.2*z eq al*z;
Ann := Annihilator(A);
assert Dimension(Ann) eq 1;
assert n in Ann;



// ---------------------------------------------

// Look at the idempotents

// ---------------------------------------------
A, gens, frob := M3A();
F<al,bt> := BaseRing(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(4,F) | t1,t2>;
assert Order(G) eq 6; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

// If characteristic is not three, then change basis
bas := [ 2*A.1-A.2-A.3, 2*A.2-A.1-A.3, A.1+A.2+A.3, A.4];
AA := ChangeBasis(A, bas);
I := IdempotentIdeal(AA);

P<lm0, lm1, mu, nu> := Generic(I);

p := 3*al^2 + 3*al*bt - bt -1;
pt := -al*p/4/(2*al - 1);
q := 3*al+bt+1;

P0 := (1-2*bt)*lm0 + 2*(2*bt-1)*lm1 + 2*(bt+1)*mu + 2*pt*nu -1;
P1 := (1-2*bt)*lm1 + 2*(2*bt-1)*lm0 + 2*(bt+1)*mu + 2*pt*nu -1;
Q := q*mu + 2*pt*nu -1;

assert Basis(I) eq [ lm0*P0, lm1*P1, (3-q)*(lm0^2-lm0*lm1+lm1^2) + mu*Q,
                     -6*(lm0^2 - lm0*lm1 + lm1^2 -mu^2) + nu*(pt*nu-1)];

// Assume we are in the case where lm1 = 0, lm0 \neq 0

P0_0 := Evaluate(P0, [lm0, 0, mu, nu]);
assert P0_0 eq -(2*bt-1)*lm0 + 2*(bt+1)*mu +2*pt*nu - 1;

assert Evaluate(Basis(I)[3], [ lm0, 0, mu, nu]) eq (3-q)*lm0^2 + mu*Q;

// -----------------------
//
// If pt ne 0;

// Eliminating nu, we get
E2 := Evaluate(Basis(I)[3], [ lm0, 0, mu, nu]) - mu*P0_0;
assert E2 eq (3-q)*lm0^2 + (2*bt-1)*lm0*mu + (q-2*(bt+1))*mu^2;

// We use P0_0 to eliminate nu from Basis(I)[4], to get:
E3 := -6*(lm0^2-mu^2) + 1/4/pt*( (2*bt-1)^2*lm0^2 - 4*(2*bt-1)*(bt+1)*lm0*mu + 4*(bt+1)^2*mu^2 -1);

assert E3 eq ( (2*bt-1)^2/4/pt -6 )*lm0^2 -(2*bt-1)*(bt+1)/pt*lm0*mu + ( (bt+1)^2/pt + 6 )*mu^2 - 1/4/pt;

II := ideal<P | lm1, P0_0, Basis(I)[3], Basis(I)[4]>;
assert E3 in II;

// Now note that E2 and E3 are polynomials just in lm0 and mu
// We map these into a smaller polynomial ring
PP := PolynomialRing(F, 2);
phi := hom< P -> PP | [ PP.1, 0, PP.2, 0]>;

// Clear the denominator of E3 by multiplying by al*p and map into into a poly ring over Z[al, bt]
E3 := al*p*E3;

FZ := RingOfIntegers(F); // Z[al,bt]
PPZ<s, t> := PolynomialRing(FZ, 2);

E2Z := PPZ!(E2@phi);
E3Z := PPZ!(E3@phi);

// Calculate the resultant
Res := Resultant(E2Z, E3Z, 1);

assert Res eq -FZ!((2*al-1)^2)*(3*t-1)*(3*t+1)*( FZ!(3^2*(2*al-1)*(3*al-bt-1)*(2*al*bt-al-bt-1))*t^2 + FZ!(q-3)^2 );

// So possible roots are: 1/3, -1/3, \pm (q-3)/3/(2*al-1)*r
// where r is a root such that r^2 = -(2*al-1)/(3*al-bt-1)/(2*al*bt-al-bt-1)

// When can these roots coincide?
// Only when -9*(q-3)^2*(2*al-1) eq 9*(2*al-1)^2*(3*al-bt-1)*(2*al*bt-al-bt-1)
// iff -(q-3)^2 eq (2*al-1)*(3*al-bt-1)*(2*al*bt-al-bt-1)
coincide_poly := 6*al^3 - 8*al^2 + 8*al - 3 - 2*al*(al-1)*bt;
assert (q-3)^2 + (2*al-1)*(3*al-bt-1)*(2*al*bt-al-bt-1) eq (2*bt - 1)*coincide_poly;

// bt ne 1/2, so only option is when coincide_poly is 0.  ie if
bt0 := (6*al^3 - 8*al^2 + 8*al - 3)/2/al/(al-1);

// Note that then r is in the field and we do not need to take a field extension
r0 := 2*al*(al-1)/3/(2*al^2-2*al+1);
assert Evaluate(-(2*al-1)/(3*al-bt-1)/(2*al*bt-al-bt-1), [al, bt0]) eq r0^2;
// This will cause extra solutions below which look spurious.

// Now check the roots:

// mu = 1/3
assert Evaluate(E2@phi, [PP.1, 1/3]) eq (PP.1 - 1/3)*( (3-q)*PP.1 -(3*al-bt-1)/3);

c1 := -(18*al^3 + 18*al^2*bt + 8*al*bt^2 - 14*al*bt - 4*al - 4*bt^2 + 4*bt - 1);
c2 := (18*al^3 + 18*al^2*bt - 8*al*bt^2 - 22*al*bt + 4*al + 4*bt^2 + 8*bt - 5)/3;

assert Evaluate(E3@phi, [PP.1, 1/3]) eq (PP.1 - 1/3)*( c1*PP.1 - c2 );

// So lm0 = 1/3 is always a root.
// check if the other can be a factor as well.  This happens iff (3*al-bt-1)/3/(3-q) eq c2/c1 and so
// 3*(3-q)*c2 eq (3*al-bt-1)*c1

assert 3*(3-q)*c2 - (3*al-bt-1)*c1 eq -3*(2*bt-1)*coincide_poly;

// char ne 3 and bt ne 1/2

// when coincide_poly = 0, then bt = bt0, r = r03
// deal with this case below


// mu = -1/3
assert Evaluate(E2@phi, [PP.1, -1/3]) eq (PP.1 + 1/3)*( (3-q)*PP.1 + (3*al-bt-1)/3);
assert Evaluate(E3@phi, [PP.1, -1/3]) eq (PP.1 + 1/3)*( c1*PP.1 + c2 );

// So lm0 = 1/3 is always a root.
// check if the other can be a factor as well.  This happens iff -(3*al-bt-1)/3/(3-q) eq -c2/c1 and so
// 3*(3-q)*c2 eq (3*al-bt-1)*c1
// Same as the above

// Deal with the coincide_poly = 0 case below

// Roots of the quadratic

FCl := AlgebraicClosure(F);
r := Sqrt(FCl!-(2*al-1)/(3*al-bt-1)/(2*al*bt-al-bt-1));

mu_0 := (3-q)/3/(2*al-1)*r;

// mu = mu_0
PP_FCl := ChangeRing(PP, FCl);

assert Evaluate(PP_FCl!(E2@phi), [PP_FCl.1, mu_0]) eq (3-q)*(PP_FCl.1 - (3*al-bt-1)/3/(2*al-1)*r)*(PP_FCl.1 - (3-q)/3/(2*al-1)*r);

c3 := (54*al^4 + 36*al^3*bt - 18*al^3 + 54*al^2*bt^2 - 36*al^2*bt - 36*al^2 + 8*al*bt^3 - 54*al*bt^2 - 6*al*bt + 29*al - 4*bt^3 + 12*bt^2 + 9*bt - 7)/3/(2*al-1);

assert Evaluate(PP_FCl!(E3@phi), [PP_FCl.1, mu_0]) eq (PP_FCl.1 - (3*al-bt-1)/3/(2*al-1)*r)*( c1*PP_FCl.1 - c3*r);

// So lm0 = (3*al-bt-1)/3/(2*al-1)*r is a common root

// The other is a root iff (3-q)/3/(2*al-1)*r = c3*r/c1
// iff (3-q)*c1 = 3*(2*al-1)*c2

assert (3-q)*c1 - 3*(2*al-1)*c3 eq 3*(2*bt-1)*coincide_poly;

// Note that if coincide_poly = 0, then the extra common root is -1/3 and mu_0 eq -1/3 too
assert Evaluate(c3/c1*r0, [al, bt0]) eq -1/3;
assert Evaluate((3-q)/3/(2*al-1)*r0, [al, bt0]) eq -1/3;
// This corresponds to the solution found above

// Now check for -mu_0, given by choosing -r
// switch r for -r in the above and get exactly the same

assert Evaluate(PP_FCl!(E2@phi), [PP_FCl.1, -mu_0]) eq (3-q)*(PP_FCl.1 - (3*al-bt-1)/3/(2*al-1)*(-r))*(PP_FCl.1 - (3-q)/3/(2*al-1)*(-r));
assert Evaluate(PP_FCl!(E3@phi), [PP_FCl.1, -mu_0]) eq (PP_FCl.1 - (3*al-bt-1)/3/(2*al-1)*(-r))*( c1*PP_FCl.1 - c3*(-r));

// So same behaviour with a second root when coincide_poly = 0 occurs.
// Here -mu_0 = 1/3 and the extra root is also 1/3

// Solve for nu
nu_0 := Roots(UnivariatePolynomial(Evaluate(P0, [1/3, 0, 1/3, nu])))[1,1];

assert nu_0 eq 0;
// This gives A.1

nu_0 := Roots(UnivariatePolynomial(Evaluate(P0, [-1/3, 0, -1/3, nu])))[1,1];

assert nu_0 eq 1/pt;
// This gives id-A.1

P_FCl := ChangeRing(P, FCl);
lm_0 := (3*al-bt-1)/3/(2*al-1)*r;
mu_0 := (3-q)/3/(2*al-1)*r;
nu_0 := Roots(UnivariatePolynomial(Evaluate(P_FCl!P0, [lm_0, 0, mu_0, P_FCl.4])))[1,1];

assert nu_0 eq 1/2/pt - 2*(4*al*bt+al-bt-1)/al/p*r;

// Define y

ACl := ChangeRing(A, FCl);
y := (bt-al)/(2*al-1)*r*ACl.1 + r*(ACl.2+ACl.3) + 2*(4*al*bt+al-bt-1)/al/p*r*ACl.4;

assert lm_0*ACl!Eltseq(bas[1]) + mu_0*ACl!Eltseq(bas[3]) + (nu_0-1/2/pt)*ACl!Eltseq(bas[4]) eq -y;
// This gives id/2 - y

lm_0 := (3*al-bt-1)/3/(2*al-1)*(-r);
mu_0 := (3-q)/3/(2*al-1)*(-r);
nu_0 := Roots(UnivariatePolynomial(Evaluate(P0, [lm_0, 0, mu_0, P_FCl.4])))[1,1];

assert nu_0 eq 1/2/pt - 2*(4*al*bt+al-bt-1)/al/p*(-r);

assert lm_0*ACl!Eltseq(bas[1]) + mu_0*ACl!Eltseq(bas[3]) + (nu_0-1/2/pt)*ACl!Eltseq(bas[4]) eq y;
// This gives id/2 + y





// Check the orbits and lengths

frobCl := ChangeRing(frob, FCl);

GCl := ChangeRing(G, FCl);  // Still remembers the order from above

assert #FindAllIdempotents(ACl) eq 16;
Simplify(FCl);
Prune(FCl);

// 0 is always an idempotent
// define the id
so, id := HasOne(ACl);
assert so;
assert id eq 1/pt*ACl.4;

x := r*ACl![1,1,1,0] + 2*(2*al-1)*(3*al+bt+1)/al/p*r*ACl.4;
idems := [ACl!0, id, ACl.1, id-ACl.1, id/2+x, id/2-x, id/2+y, id/2-y];

orbs := {@ {@ ACl!u : u in Orbit(GCl, Vector(v))@} : v in idems @};  // Need to have found the order for Orbit to work
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #(&join orbs) eq 16;
assert #orbs eq 8;
assert {* #o : o in orbs *} eq {* 1^^4, 3^^4 *};

// We have all the orbit representatives for the idempotents
assert { i where so := exists(i){i : i in [1..#orbs] | e in orbs[i]} : e in idems} eq {1..#orbs};

// The identity
len_id := (9*al + bt - 5)/(3*al^2 + 3*al*bt - bt - 1);
assert InnerProduct(id*frobCl, id) eq len_id;

// 1/2 \pm x
assert IsIdempotent(id/2 +x);
assert InnerProduct((id/2 +x)*frobCl, id/2 +x) eq 1/2/(3*al^2 + 3*al*bt - bt - 1)*( (9*al + bt - 5) - (3*al-bt-1)^2*r);

// There are 3 eigenvalues, 1, 0 and 
assert Dimension(Eigenspace(id/2 +x, (-3*al + bt + 1)/2*r + 1/2)) eq 2;
// But it is not Jordan type a in general as not graded.  Have a*a = {1,0,a}
evals, espace, FL := IdentifyFusionLaw(id/2 +x);
assert Order(Grading(FL)) eq 1;

// Becomes Jordan type iff bt = 1/2
// But when bt=1/2, A \cong IY_3(al,1/2,-1/2) - all idempotents are classified here.
// This algebra has 3 axes, but is isomorphic as an algebra to IY_3(al,1/2,1/2), which has 6 axes.
assert Vector(ACl.1-ACl.2) in espace[3] and Vector(ACl.2-ACl.3) in espace[3];
// This gives an automorphism which swaps our known orbit 3 axes to a second set

// the fourth idempotent fixed by the Miyamoto group is id/2 - x
assert IsIdempotent(id/2-x);

assert InnerProduct((id/2-x)*frobCl,id/2-x) eq 1/2/(3*al^2 + 3*al*bt - bt - 1)*( (9*al+bt-5) + (3*al - bt - 1)^2*r);
// Fusion law comes from x
// Now consider the idempotents in the orbits orbits of size 3
// clearly, one orbit is the axes
// another is 1 - axes

assert IsIdempotent(ACl.1) and IsIdempotent(id-ACl.1);

assert InnerProduct((id-ACl.1)*frobCl, id -ACl.1) eq (-3*al^2 - 3*al*bt + 9*al + 2*bt - 4)/(3*al^2 + 3*al*bt - bt - 1);

// 1/2 \pm y
// NB that id-y is equivalent to picking the other root -r
assert IsIdempotent(id/2 +y);

assert InnerProduct((id/2 +y)*frobCl, id/2 +y) eq 1/2/(3*al^2 + 3*al*bt - bt - 1)*( (9*al+bt-5) + (3*al - bt - 1)^2*r);
assert InnerProduct((id/2 +y)*frobCl, id/2 +y) eq InnerProduct((id/2-x)*frobCl,id/2-x);

evals, espaces, FL := IdentifyFusionLaw(id/2+y);
lm := (3*al - bt - 1)/2*r + 1/2;
mu := -(2*bt-1)*(3*al-bt-1)/(4*al - 2)*r + 1/2;
assert { e[1] : e in evals} eq {1,0,lm, mu};
assert HasAlmostMonsterFusionLaw(id/2+y:fusion_values:=[lm,mu]);

assert Order(Grading(FL)) eq 2;
assert (id/2+y)*(ACl.2-ACl.3) eq mu*(ACl.2-ACl.3);
// Miyamoto involution is the same

// Almost Monster type (lm,mu): lm*lm = {1,0,a}
u_lm := (5*al + bt - 3)*ACl.1 + (2*al-1)*(ACl.2+ACl.3) + 4*(2*al-1)/al*ACl.4;
assert (id/2+y)*u_lm eq lm*u_lm;

u_0 := al*(al-bt)*(3*al^2 + 3*al*bt - bt - 1)*ACl.1 - al*(2*al-1)*(3*al^2 + 3*al*bt - bt - 1)*(ACl.2+ACl.3)
          + 2*(2*al - 1)*( (3*al - bt - 1)*(2*al*bt - al - bt - 1)*r - (4*al*bt + al - bt - 1) )*ACl.4;
assert (id/2+y)*u_0 eq ACl!0;

// Becomes Monster type iff bt = 1/2
V := VectorSpaceWithBasis([ Vector(v) : v in [id/2+y,u_0,u_lm,ACl.2-ACl.3]]);
coord := Coordinates(V, Vector(u_lm^2));
assert coord[4] eq 0;
assert coord[3] eq -(2*al-1)*(2*bt-1);


// both x and A.4 are fixed by the Miyamoto group, so y in in an orbit of size 3

assert IsIdempotent(id/2-y);
assert InnerProduct((id/2 -y)*frobCl, id/2 -y) eq InnerProduct((id/2+x)*frobCl,id/2+x);

// Check for characteristic polynomial matching Monster type

poss := CheckForMatchingCharactisticPoly(ACl.1, orbs);

assert #poss eq 3;

// One is the case of id - axis
assert poss[1,1] eq id-ACl.1;

// The other two are 1/2id \pm y
assert { poss[2,1], poss[3,1]} eq { id/2+y, id/2-y};

// One of id/2 \pm y has the same spectrum as an axis, if and only if y has the same spectrum as A.1-id/2.
// This is 1/2, -1/2, al-1/2, bt-1/2

s := 3*al-bt-1;
t := 2*al*bt-al-bt-1;

assert r^2 eq -(2*al-1)/s/t;

P<x> := PolynomialRing(FCl);

assert CharacteristicPolynomial(y) eq (x-1/2)*(x+1/2)*(x-s/2*r)*(x+(2*bt-1)*s/2/(2*al-1)*r);

// So { s/2*r, -(2*bt-1)*s/2/(2*al-1)*r } = { al-1/2, bt-1/2 }

// If s/2*r eq al-1/2, then
// r eq (2*al-1)/s
// So -(2*al-1)/s/t = r^2 = (2*al-1)^2/s^2
// rearranging we get the following to be 0
assert (2*al-1)*t + s eq 2*(2*bt-1)*al*(al-1);
// Since bt ne 1/2, al ne 0, 1, this is a contradiction

/*
So we must have

s/2*r = bt-1/2   and    -(2*bt-1)*s/2/(2*al-1)*r = al-1/2

which is

s*r = 2*bt-1    and -(2*bt-1)/(2*al-1)*s*r = 2*al-1

Substituting sr into the second equation, we get

(2*bt-1)^2 = -(2*al-1)^2

From the first equation above, r = (2*bt-1)/s and so

-(2*al-1)/s/t = r^2 = (2*bt-1)^2/s^2 = -(2*al-1)^2/s^2

rearranging, we get the following to be 0
*/
assert s - (2*al-1)*t eq -2*(2*al^2*bt - al^2 - 2*al*bt - 2*al + bt + 1);

// So we get that bt = (al^2 + 2*al - 1)/(2*al^2 -2*al +1)
assert Evaluate(2*al^2*bt - al^2 - 2*al*bt - 2*al + bt + 1, [al, (al^2 + 2*al - 1)/(2*al^2 -2*al +1)]) eq 0;

assert Evaluate( 2*bt-1, [al, (al^2 + 2*al - 1)/(2*al^2 -2*al +1)]) eq 3*(2*al-1)/(2*al^2-2*al+1);

// But (2*bt-1)^2 = -(2*al-1)^2
// So 3^2*(2*al-1)^2/(2*al^2-2*al+1)^2 = -(2*al-1)^2
// Hence 9/(2*al^2-2*al+1)^2 = -1
// So we get the following to be 0
assert (2*al^2-2*al+1)^2 + 9 eq 2*(2*al^4 - 4*al^3 + 4*al^2 - 2*al + 5);

assert Evaluate( (2*bt-1)^2, [al, (al^2 + 2*al - 1)/(2*al^2 -2*al +1)]) eq 3^2*(2*al-1)^2/(2*al^2-2*al+1)^2;



I := poss[2,4];
P := Generic(I);

assert poss[2,3] eq [* <r, P.1>, <al, P.2>, <bt, P.3> *];

// al ne 1/2 and we assume in this case that bt ne 1/2 (as otherwise 3A \cong IY3)




// -----------------------
//
// If pt = 0
// Complete case when lm0 \neq 0 and lm1 = 0

// If p = 0, then 
assert p eq (3*al-1)*bt + 3*al^2-1;
// so bt = (1-3al^2)/(3*al-1)

F<al> := FunctionField(Integers());
bt := (1-3*al^2)/(3*al-1);

A, gens, frob := M3A(al, bt);

bas := [ 2*A.1-A.2-A.3, 2*A.2-A.1-A.3, A.1+A.2+A.3, A.4];
AA := ChangeBasis(A, bas);
I := IdempotentIdeal(AA);

P<lm0, lm1, mu, nu> := Generic(I);

p := 3*al^2 + 3*al*bt - bt -1;
pt := -al*p/4/(2*al - 1);
q := 3*al+bt+1;

P0 := (1-2*bt)*lm0 + 2*(2*bt-1)*lm1 + 2*(bt+1)*mu + 2*pt*nu -1;
P1 := (1-2*bt)*lm1 + 2*(2*bt-1)*lm0 + 2*(bt+1)*mu + 2*pt*nu -1;
Q := q*mu + 2*pt*nu -1;

assert Basis(I) eq [ lm0*P0, lm1*P1, (3-q)*(lm0^2-lm0*lm1+lm1^2) + mu*Q,
                     -6*(lm0^2 - lm0*lm1 + lm1^2 -mu^2) + nu*(pt*nu-1)];

// Assume we are in the case where lm1 = 0, lm0 \neq 0

P0_0 := Evaluate(P0, [lm0, 0, mu, nu]);
assert P0_0 eq -(2*bt-1)*lm0 + 2*(bt+1)*mu - 1;

// Equation 2
E2 := Evaluate(Basis(I)[3], [lm0, 0, mu, nu]);
assert E2 eq (3-q)*lm0^2 + q*mu^2 -mu;

// Use P0_0 to substitue for lm0 to get

E2 := (3-q)*1/(2*bt-1)^2*( 2*(bt+1)*mu -1)^2 + q*mu^2 -mu;
assert (2*bt-1)^2*E2 eq 3*(2*al-1)/(3*al-1)*( 3*mu - 1 )*( 6*al^2*mu - (1-al) );

rt := (3*al-1)/6/al^2;

xp := rt*(A.1+A.2+A.3) + 6*rt^2*A.4;
yp := (1+3*al)/(6*al^2)*A.1 - rt*(A.2+A.3) - (al+1)/al^2*rt*A.4;

assert 1/3/al*(2*A.1-A.2-A.3) + (1-al)/6/al^2*(A.1+A.2+A.3) -(3*al-1)*(al+1)/6/al^4*A.4 eq yp;

assert IsIdempotent(xp);
assert InnerProduct(xp*frob, xp) eq (3*al-1)/4/al^3;
evals, espace, FL := IdentifyFusionLaw(xp);
assert Order(Grading(FL)) eq 1; // not graded
assert evals eq { <1,1>, <0,1>, < (1-al)/2/al, 2>}; // three eigenvalues

assert IsIdempotent(yp);
assert InnerProduct(yp*frob, yp) eq (3*al-1)/4/al^3;
evals, espace, FL := IdentifyFusionLaw(yp);
Gr, gr := Grading(FL);
assert Order(Gr) eq 2;
assert MiyamotoInvolution(yp) eq MiyamotoInvolution(A.1);

// -------------------------
//
// characteristic 3

A, gens, frob := M3A(:base_ring:=GF(3));
F<al,bt> := BaseRing(A);

idems := FindAllIdempotents(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(4,F) | t1,t2>;

orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #orbs eq 8;
assert {* #o : o in orbs *} eq {* 1^^4, 3^^4 *};

// In char 3, we have
p := 3*al^2 + 3*al*bt - bt -1;
assert p eq 2*(bt+1);
// so this is non-zero iff bt \neq -1
// but -1 = 1/2 and we assume that bt \neq 1/2

// From above, think about r^2
// As 2al = -al in char 3, we have a factorisation:
assert (2*al-1)*(bt+1) eq (2*al*bt - al - bt - 1);

// So r^2 now is 1/(bt+1)^2
assert -(2*al-1)/(3*al-bt-1)/(2*al*bt-al-bt-1) eq 1/(bt+1)^2;

// idempotents in an orbit of size 1
// 0 is always an idempotent

// has an identity iff bt \neq -1
so, id := HasOne(A);
assert so;
assert id eq 2*(al+1)/(al*(bt+1))*A.4;

// since r = +/- 1/(bt+1), this is the same as the x above.
x := 1/(bt+1)*(A.1+A.2+A.3) + 2*(2*al-1)/al/p*A.4;
assert IsIdempotent(id/2+x);
assert {e[1] : e in Eigenvalues(id/2+ x)} eq {0,1};
assert not IsSemisimple(id/2 + x);

_,_,S := JordanForm(AdjointMatrix(id/2 + x));
assert exists{s : s in S | s[2] eq 2};
// So the adjoint has a jordan block of size 2, so it is not semisimple

// other idempotent is 1-x, also not semisimple
assert IsIdempotent(id/2-x);
assert not IsSemisimple(id/2-x);

// idempotents in an orbit of size 3
assert {@ A.i : i in [1..3] @} in orbs;
assert {@ id - A.i : i in [1..3] @} in orbs;

// y from above now becomes the following in char 3

y := 1/(bt+1)*( (al-bt)/(al+1)*A.1 + A.2 + A.3 + 2*(4*al*bt+al-bt-1)/al/p*A.4);

assert exists(o1){o : o in orbs | id/2 + y in o}; // so it is an idempotent
// y is not semisimple
assert not IsSemisimple(id/2+y);

assert id/2 - y notin o1;
assert exists(o1_pair){o : o in orbs | id/2-y in o};

poss := FindMatchingIdempotents(A.1, orbs);
assert #poss eq 1;

// Again we have the possibility that id-A.1 as above

// this is for id - a_i
p := CharacteristicPolynomial(id-A.1) - CharacteristicPolynomial(A.1);
P<t> := Parent(p);

assert p eq (al+bt-1)*t*(2*t^2 +1);
// so only possibility again is that bt = 1-al
// analysis above did not depend on char not 3
FF<Al> := FunctionField(GF(3));
Bt := 1-Al;
A, gens, frob := M3A(Al, Bt);

so, id := HasOne(A);
assert so;
assert HasMonsterFusionLaw(id-A.1:fusion_values:=[Al,Bt]);
t1_bt := MiyamotoInvolution(A.1, Bt);
t1_al := MiyamotoInvolution(A.1, Al);
assert MiyamotoInvolution(id-A.1, Bt) eq t1_al;
t2_bt := MiyamotoInvolution(A.2, Bt);
t2_al := MiyamotoInvolution(A.2, Al);
assert MiyamotoInvolution(id-A.2, Bt) eq t2_al;

G := sub<GL(4,FF) | t1_bt, t1_al, t2_bt, t2_al>;
assert GroupName(G) eq "S4";


//-----------------------------------------------------------------------------------------------------------
































// Check for any odd values of al,bt giving more idempotents

II := IdealOfSingularPoints(A);

prim := RadicalDecomposition(II);

// get polynomial ring - al, bt are the last two variables
P := Generic(II);
assert #prim eq 14;

// Can't have al = 1/2
Good := [ J : J in prim | P.5-1/2 notin Basis(J)];

// If bt = 1/2 then 3A is isomorphic to IY_3(al, 1/2, -1/2)

assert #[ J : J in Good | P.6-1/2 notin Basis(J)] eq 0;

// So there are no singular points we need to consider

// ---------------------------------------------

// Examine the generic case

FCl := AlgebraicClosure(F);
// Need to add one root
r := Sqrt(FCl!-(2*al-1)/(3*al-bt-1)/(2*al*bt-al-bt-1));
// So need to check seperately the cases where 3*al-bt-1, or 2*al*bt-al-bt-1 are 0
// NB that 2*al-1 \neq 0

A := ChangeRing(A, FCl);
frob := ChangeRing(frob, FCl);
idems := FindAllIdempotents(A);
Simplify(FCl);
Prune(FCl);

G := ChangeRing(G, FCl);  // Still remembers the order from above
orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};  // Need to have found the order for Orbit to work
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #orbs eq 8;
assert {* #o : o in orbs *} eq {* 1^^4, 3^^4 *};

// 0 is always an idempotent

// need to consider separately when 3*al^2 + 3*al*bt - bt - 1 = 0
so, id := HasOne(A);
assert so;
assert id eq -4*(2*al -1)/(al*(3*al^2 + 3*al*bt - bt - 1))*A.4;

len_id := (9*al + bt - 5)/(3*al^2 + 3*al*bt - bt - 1);
assert InnerProduct(id*frob, id) eq len_id;

// We also have x
x := r*(A.1+A.2+A.3) + 2*(2*al - 1)/(al*(3*al^2 + 3*al*bt - bt - 1)) * (3*al + bt + 1)*r*A.4;

assert IsIdempotent(id/2 +x);

assert InnerProduct((id/2 +x)*frob, id/2 +x) eq 1/2/(3*al^2 + 3*al*bt - bt - 1)*( (9*al + bt - 5) - (3*al-bt-1)^2*r);

// There are 3 eigenvalues, 1, 0 and 
assert Dimension(Eigenspace(id/2 +x, (-3*al + bt + 1)/2*r + 1/2)) eq 2;
// But it is not Jordan type a in general as not graded.  Have a*a = {1,0,a}
evals, espace, FL := IdentifyFusionLaw(id/2 +x);
assert Order(Grading(FL)) eq 1;

// Becomes Jordan type iff bt = 1/2
// But when bt=1/2, A \cong IY_3(al,1/2,-1/2) - all idempotents are classified here.
// This algebra has 3 axes, but is isomorphic as an algebra to IY_3(al,1/2,1/2), which has 6 axes.
assert Vector(A.1-A.2) in espace[3] and Vector(A.2-A.3) in espace[3];
// This gives an automorphism which swaps our known orbit 3 axes to a second set

// the fourth idempotent fixed by the Miyamoto group is 1-x
assert IsIdempotent(id/2-x);

assert InnerProduct((id/2-x)*frob,id/2-x) eq 1/2/(3*al^2 + 3*al*bt - bt - 1)*( (9*al+bt-5) + (3*al - bt - 1)^2*r);
// Fusion law comes from x
// Now consider the idempotents in the orbits orbits of size 3
// clearly, one orbit is the axes
// another is 1 - axes

assert IsIdempotent(A.1) and IsIdempotent(id-A.1);

assert InnerProduct((id-A.1)*frob, id -A.1) eq (-3*al^2 - 3*al*bt + 9*al + 2*bt - 4)/(3*al^2 + 3*al*bt - bt - 1);

// another idempotent
y := (bt-al)/(2*al-1)*r*A.1 + r*(A.2+A.3) + 2*(4*al*bt + al - bt - 1)/(al*(3*al^2 + 3*al*bt - bt - 1))*r*A.4;
// NB that id-y is equivalent to picking the other root -r

assert IsIdempotent(id/2 +y);

// So if the following fails then magma has picked the other root r
assert InnerProduct((id/2 +y)*frob, id/2 +y) eq 1/2/(3*al^2 + 3*al*bt - bt - 1)*( (9*al+bt-5) + (3*al - bt - 1)^2*r);
assert InnerProduct((id/2 +y)*frob, id/2 +y) eq InnerProduct((id/2-x)*frob,id/2-x);

evals, espaces, FL := IdentifyFusionLaw(id/2+y);
lm := (3*al - bt - 1)/2*r + 1/2;
mu := -(2*bt-1)*(3*al-bt-1)/(4*al - 2)*r + 1/2;
assert { e[1] : e in evals} eq {1,0,lm, mu};
assert HasAlmostMonsterFusionLaw(id/2+y:fusion_values:=[lm,mu]);

assert Order(Grading(FL)) eq 2;
assert (id/2+y)*(A.2-A.3) eq mu*(A.2-A.3);
// Miyamoto involution is the same

// Almost Monster type (lm,mu): lm*lm = {1,0,a}
u_lm := (5*al + bt - 3)*A.1 + (2*al-1)*(A.2+A.3) + 4*(2*al-1)/al*A.4;
assert (id/2+y)*u_lm eq lm*u_lm;

u_0 := al*(al-bt)*(3*al^2 + 3*al*bt - bt - 1)*A.1 - al*(2*al-1)*(3*al^2 + 3*al*bt - bt - 1)*(A.2+A.3)
          + 2*(2*al - 1)*( (3*al - bt - 1)*(2*al*bt - al - bt - 1)*r - (4*al*bt + al - bt - 1) )*A.4;
assert (id/2+y)*u_0 eq A!0;

// Becomes Monster type iff bt = 1/2
V := VectorSpaceWithBasis([ Vector(v) : v in [id/2+y,u_0,u_lm,A.2-A.3]]);
coord := Coordinates(V, Vector(u_lm^2));
assert coord[4] eq 0;
assert coord[3] eq -(2*al-1)*(2*bt-1);


// both x and A.4 are fixed by the Miyamoto group, so y in in an orbit of size 3

assert IsIdempotent(id/2-y);
assert InnerProduct((id/2 -y)*frob, id/2 -y) eq InnerProduct((id/2+x)*frob,id/2+x);




// Check to see whether there are any idempotents (for any value of al or bt) which have the same char poly as an axis.

poss := FindMatchingIdempotents(A.1, orbs);

assert #poss eq 1;
// There is one case which we need to examine

// this is for id - a_i
p := CharacteristicPolynomial(id-A.1) - CharacteristicPolynomial(A.1);
P<t> := Parent(p);

assert p eq (al+bt-1)*t*(2*t^2 -3*t +1);

// This can be identically zero iff al+bt-1 = 0
// Set bt = 1-al

FF<Al> := FunctionField(QQ);
Bt := 1-Al;

// NB we can't be in the case with no identity
assert 3*Al^2 + 3*Al*Bt -Bt-1 eq 2*(2*Al-1);

A, gens, frob := M3A(Al, Bt);

so, id := HasOne(A);
assert so;
assert HasMonsterFusionLaw(id-A.1:fusion_values:=[Al,Bt]);
// So we have 3 more Monster type axes.

// This gives six in total.  We now need to identify the automorphism group
// It must act faithfully on this set, since the axes generate the algebra.
/*
Let S be the set of six axes.
Let a,b in X.  Then a*b = 0 iff b = id-a

Now consider the action of G := Aut on S.  Let a and b now be two of the original axes.  The stabiliser of a must fix id-a, so the stabiliser G_a acts on the remaining four axes.  Consider the stabiliser in G_a of b. Since it fixes a and b and these generate the algebra, it must fix the entire algebra.  Hence G_ab = 1.  So by Orbit-Stabiliser Theorem, G can have order at most 6*4 = 24

*/

// In fact now, the fusion law is C_2 x C_2 graded as Bt*Bt = {1,0}
evals1, espace1, FL1 := IdentifyFusionLaw(A.1: eigenvalues:=[1,0,Al,Bt]);
evals2, espace2, FL2 := IdentifyFusionLaw(id-A.1: eigenvalues:=[1,0,Al,Bt]);

// We know that the eigenspaces for id-A.1 are the same as those for A.1
assert Set(espace1) eq Set(espace2);

// So the fusion law is C_2 x C_2 graded by al and bt
Gr, gr := Grading(FL1);
assert Order(Gr) eq 4;
assert not IsCyclic(Gr);
assert Order(4@gr) eq 2;
assert Order(3@gr) eq 2;
assert 3@gr ne 4@gr;

t1_bt := MiyamotoInvolution(A.1, Bt);
t1_al := MiyamotoInvolution(A.1, Al);
assert MiyamotoInvolution(id-A.1, Bt) eq t1_al;
t2_bt := MiyamotoInvolution(A.2, Bt);
t2_al := MiyamotoInvolution(A.2, Al);
assert MiyamotoInvolution(id-A.2, Bt) eq t2_al;

G := sub<GL(4,FF) | t1_bt, t1_al, t2_bt, t2_al>;
assert Order(G) eq 24;

// So this is the automorphism group, which is the Miyamoto group wrt just the grading for bt and the six axes.
// Also, the Miyamoto of the C_2 x C_2-graded fusion law.

// t1_bt switches A.2 and A.3 and so also switches id-A.2 and id-A.3
// t1_al switches A.2 and id-A.3
assert A.2*t1_al eq id-A.3;
assert A.3*t1_al eq id-A.2;

// We know that t1_bt*t2_bt is an element of order three which permutes A.1, A.2, A.3 and so also id-A.i
// [t1_al, t1_bt] = 1

// So t1_al*(t1_bt*t2_bt)*t1_al
assert A.3* t1_al*(t1_bt*t2_bt)*t1_al eq id -A.1;
// So <t1_bt*t2_bt>, which is the Sylow 3-subgroup is not normal

assert Order(t1_al*t2_al*t2_bt) eq 4;

assert t1_bt*(t1_al*t2_al*t2_bt)*t1_bt eq t2_bt*t2_al*t1_al;
// So this generates a dihedral group of order 8, which must be the Sylow 2-subgroup.

// Hence G must be S_4.

assert GroupName(G) eq "S4";

// Look at the action of G on the six axes.  It is the same as the action of S_4 on the transpositions.

// --------------------------------------------
/*

We have three exceptional situations to check:

 3*al-bt-1 = 0
 2*al*bt-al-bt-1 = 0
 3*al^2 + 3*al*bt - bt - 1 = 0

*/

// --------------------------------------------

// Look at characteristic 3

A, gens, frob := M3A(:base_ring:=GF(3));
F<al,bt> := BaseRing(A);

idems := FindAllIdempotents(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(4,F) | t1,t2>;

orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #orbs eq 8;
assert {* #o : o in orbs *} eq {* 1^^4, 3^^4 *};

// From above, think about r^2
// As 2al = -al in char 3, we have a factorisation:
assert (2*al-1)*(bt+1) eq (2*al*bt - al - bt - 1);

// So r^2 now is 1/(bt+1)^2
assert -(2*al-1)/(3*al-bt-1)/(2*al*bt-al-bt-1) eq 1/(bt+1)^2;


// idempotents in an orbit of size 1
// 0 is always an idempotent

// has an identity iff bt \neq -1
so, id := HasOne(A);
assert so;
assert id eq 2*(al+1)/(al*(bt+1))*A.4;

// since r = +/- 1/(bt+1), this is the same as the x above.
x := 1/(bt+1)*(A.1+A.2+A.3);
assert IsIdempotent(x);
assert {e[1] : e in Eigenvalues(x)} eq {0,1};
assert not IsSemisimple(x);

_,_,S := JordanForm(AdjointMatrix(x));
assert exists{s : s in S | s[2] eq 2};
// So the adjoint has a jordan block of size 2, so it is not semisimple

// other idempotent is 1-x, also not semisimple
assert IsIdempotent(id-x);
assert not IsSemisimple(id-x);

// idempotents in an orbit of size 3
assert {@ A.i : i in [1..3] @} in orbs;
assert {@ id - A.i : i in [1..3] @} in orbs;

// y from above now becomes the following in char 3

y := 1/(bt+1)*( (al-bt)/(al+1)*A.1 + A.2 + A.3 - A.4);

// y is not semisimple
assert not IsSemisimple(y);

assert exists(o1){o : o in orbs | y in o};
assert id - y notin o1;

assert exists(o1_pair){o : o in orbs | id-y in o};

poss := FindMatchingIdempotents(A.1, orbs);
assert #poss eq 1;

// Again we have the possibility that id-A.1 as above

// this is for id - a_i
p := CharacteristicPolynomial(id-A.1) - CharacteristicPolynomial(A.1);
P<t> := Parent(p);

assert p eq (al+bt-1)*t*(2*t^2 +1);
// so only possibility again is that bt = 1-al
// analysis above did not depend on char not 3
FF<Al> := FunctionField(GF(3));
Bt := 1-Al;
A, gens, frob := M3A(Al, Bt);

so, id := HasOne(A);
assert so;
assert HasMonsterFusionLaw(id-A.1:fusion_values:=[Al,Bt]);
t1_bt := MiyamotoInvolution(A.1, Bt);
t1_al := MiyamotoInvolution(A.1, Al);
assert MiyamotoInvolution(id-A.1, Bt) eq t1_al;
t2_bt := MiyamotoInvolution(A.2, Bt);
t2_al := MiyamotoInvolution(A.2, Al);
assert MiyamotoInvolution(id-A.2, Bt) eq t2_al;

G := sub<GL(4,FF) | t1_bt, t1_al, t2_bt, t2_al>;
assert GroupName(G) eq "S4";

//---------------------------------------------------

// Now need to deal with the case where 3*al^2 + 3*al*bt - bt - 1 = 0
// Saw above that then al \neq 1/3 and so
// bt := (1-3*al^2)/(3al-1)

A, gens, frob := M3A();
F<al,bt> := BaseRing(A);

FF<Al> := FunctionField(QQ);
Bt := (1-3*Al^2)/(3*Al-1);
phi := hom<F->FF | [Al, Bt]>;

A := ChangeRing(A, FF, phi);
frob := ChangeRing(frob, FF, phi);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(4,FF) | t1,t2>;

// Note that in this case, there is a non-trivial annihilator spanned by A.4, which is an ideal
// This gives a split extension of the algebra
// Hence any idempotents must either lie in the ideal (but this is nil), or in its complement
// So we should expect at most 8 idempotents

idems := FindAllIdempotents(A);
orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #idems eq 8;
assert {* #o : o in orbs *} eq {* 1^^2, 3^^2 *};

// Previously we had to add a square root of r_sq.
// But now this already has a root in the field
r_sq := phi(-(2*al-1)/(3*al-bt-1)/(2*al*bt-al-bt-1));
assert r_sq eq (Al-1/3)^2/(2*Al^2)^2;

// so set r as above to be the root of r_sq
r := (Al-1/3)/(2*Al^2);

x := r*(A.1+A.2+A.3) + 6*r^2*A.4;
assert IsIdempotent(x);
assert InnerProduct(x*frob, x) eq (3*Al-1)/4/Al^3;

// zero is also an idempotent and so these are the only two in an orbit of size 1
// For the orbits of size 3, we have the axes and

y := 1/Al*A.1 -x  + 2*r*(Al-1)/Al^2*A.4;
assert IsIdempotent(y);
assert InnerProduct(y*frob, y) eq (3*Al-1)/4/Al^3;

assert y eq (Al+1/3)/(2*Al^2)*A.1 - r*(A.2 + A.3) - r*(Al+1)/Al^2*A.4;
// These are the only idempotents.

// A.4 is the only nilpotent element up to scaling

poss := FindMatchingIdempotents(A.1, orbs);
assert #poss eq 2;

assert poss[1,1] eq x;
assert poss[2,1] eq orbs[4,1];

// this is for x
p := CharacteristicPolynomial(AdjointMatrix(x)) - CharacteristicPolynomial(AdjointMatrix(A.1));
P<t> := Parent(p);

assert p eq (2*Al-1)/Al^2/(3*Al-1)*(
          Al*(Al - 1)*t^3 + (Al + 1)*(6*Al^3 - 3*Al^2 + 1)/4*t^2 +
          -(6*Al^4 + 3*Al^3 + Al^2 - 3*Al + 1)/4*t);

// In 3A, al ne 1/2 and in this case, al ne 1/3, so, as al ne 0,1, this poly can never be identically zero.

// this is for y
p := CharacteristicPolynomial(AdjointMatrix(y)) - CharacteristicPolynomial(AdjointMatrix(A.1));
P<t> := Parent(p);

assert p eq (2*Al - 1)*(Al + 1)/Al^2/(3*Al-1)*(Al*t^3
                       + 3*(Al - 1)*(2*Al^2 + Al + 1)/4*t^2
                       - (6*Al^3 - 3*Al^2 + 4*Al - 3)/4*t);

// Al is not 1/2, 1/3,1, so the only possibility to check here is Al = -1

assert Evaluate(Bt,-1) eq 1/2;
// So Al can't be -1 either as we assume that Bt is not 1/2 (This is when 3A \cong IY3)


//---------------------------------------------------

// Now suppose 3*al-bt-1 = 0
// Hence bt = 3al-1
// As above, this is a case which has a 1-dim ideal giving a split extension

// Here the common al-eigenvalue is a nilpotent element
// This is the only nilpotent element up to scaling

A, gens, frob := M3A();
F<al,bt> := BaseRing(A);

FF<Al> := FunctionField(QQ);
Bt := 3*Al-1;
phi := hom<F->FF | [Al, Bt]>;

A := ChangeRing(A, FF, phi);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(4,FF) | t1,t2>;

idems := FindAllIdempotents(A);
orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #idems eq 8;
assert {* #o : o in orbs *} eq {* 1^^2, 3^^2 *};

// orbits of size 1
so, id := HasOne(A);
assert so;
assert id eq -2/3/Al^2*A.4;
// need char \neq 3

// orbits of size 3
// axes and 1-axes

poss := FindMatchingIdempotents(A.1, orbs);
assert #poss eq 1;

p := CharacteristicPolynomial(id-A.1) - CharacteristicPolynomial(A.1);
P<t> := Parent(p);

assert p eq (Al+Bt-1)*t*(2*t^2 -3*t +1);

// So once again we need to consider Bt = 1-Al
// But also Bt = 3*AL-1, so we get Al = 1/2 and Bt = 1/2, so this can't happen

//---------------------------------------------------

// Now suppose that 2*al*bt-al-bt-1 = 0
// since al \neq 1/2 can rearrange to get
// bt = (al+1)/(2*al-1);

A, gens, frob := M3A();
F<al,bt> := BaseRing(A);

FF<Al> := FunctionField(QQ);
Bt := (Al+1)/(2*Al-1);
phi := hom<F->FF | [Al, Bt]>;

A := ChangeRing(A, FF, phi);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(4,FF) | t1,t2>;

idems := FindAllIdempotents(A);
orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #idems eq 8;
assert {* #o : o in orbs *} eq {* 1^^2, 3^^2 *};

// orbits of size 1
so, id := HasOne(A);
assert so;
assert id eq -2/3*(2*Al-1)^2/Al^4*A.4;
// need char \neq 3

// orbits of size 3
// axes and 1-axes

poss := FindMatchingIdempotents(A.1, orbs);
assert #poss eq 1;

p := CharacteristicPolynomial(id-A.1) - CharacteristicPolynomial(A.1);
P<t> := Parent(p);

assert p eq (Al+Bt-1)*t*(2*t^2 -3*t +1);

// So once again we need to consider Bt = 1-Al
// In this case, Bt := (Al+1)/(2*Al-1);
poly := Al+1 - (2*Al-1)*(1-Al);
assert poly eq 2*(Al^2-Al+1);

// This is possible, but it comes under the analysis above.

// Nilpotent elements are scalar multiples of
n1 := -Al^2*(2*Al^2-2*Al-1)/(2*Al-1)^2*A.1 + Al^2*(A.2+A.3) + 2*A.4;
// and the orbits of n1 under Miy

n2 := Al^2*(A.1+A.2+A.3) + 2*(2*Al-1)*A.4;
