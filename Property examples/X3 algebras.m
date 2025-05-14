AttachSpec("2-gen Monster.spec");
AttachSpec("../AxialTools/AxialTools.spec");
load "Property examples/Find idempotents.m";

QQ := Rationals();

// Get the algebra, generators and the frobenius form
A, gen, frob := M3A();
F<al,bt> := BaseRing(A);

// The algebra has an identity if 3*al^2 + 3*al*bt - bt - 1 \neq 0
so, id := HasOne(A);
assert so;
assert id eq -4*(2*al -1)/(al*(3*al^2 + 3*al*bt - bt - 1))*A.4;


assert Determinant(frob) eq -al^2*(3*al - bt - 1)*(3*al^2 + 3*al*bt - bt - 1)*
                                  (3*al^2 + 3*al*bt - 9*al - 2*bt + 4)^3 / ( 2^9*(2*al-1)^5 );


// define some polys
g1 := 27*al^5 + 30*al^4*bt - 15*al^4 + 3*al^3*bt^2 - 24*al^3*bt + 39*al^3 - al^2*bt^2 + 52*al^2*bt + 29*al^2 - 56*al*bt - 56*al + 16*bt + 16;

assert CharacteristicPolynomial(frob) eq
    (lm + (3*al^2 + 3*al*bt - 9*al - 2*bt + 4)/(4*(2*al-1)))^2 *
       (lm^2 - g1/(4*(2*al-1))^2 * lm 
        -al^2*(3*al - bt - 1)*(3*al^2 + 3*al*bt - bt - 1)*(3*al^2 + 3*al*bt - 9*al - 2*bt + 4)/(32*(2*al-1)^3));

/*

So need to check when bt = 3al-1

and 3*al^2 + 3*al*bt - bt - 1 = 0

and 3*al^2 + 3*al*bt - 9*al - 2*bt + 4 = 0

*/

// First check for when char = 3
A, gen, frob := M3A(:base_ring:=GF(3));
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
A, gen, frob := M3A();
F<al,bt> := BaseRing(A);

// Let bt = 3al-1
// so 3al - 1 \neq 0

FF<Al> := FunctionField(QQ);
phi := hom<F->FF | [Al,3*Al-1]>;

AA := ChangeRing(A, FF, phi);
frob2 := ChangeRing(frob, FF, phi);

// Checkiing char poly doesn't help in this case, so
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

// ---------------------------------------------

// Look at the idempotents

// First do characteristic 3

A, gen, frob := M3A(:base_ring:=GF(3));
F<al,bt> := BaseRing(A);

idems := FindAllIdempotents(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(4,F) | t1,t2>;

orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #orbs eq 8;
assert {* #o : o in orbs *} eq {* 1^^4, 3^^4 *};

// idempotents in an orbit of size 1
// 0 is always an idempotent

// has an identity iff bt \neq -1
so, id := HasOne(A);
assert so;
assert id := 2*(al+1)/(al*(bt+1));

x := 1/(bt+1)*(A.1+A.2+A.3);
assert IsIdempotent(x);
assert {e[1] : e in Eigenvalues(x)} := {0,1};
_,_,S := JordanForm(AdjointMatrix(x));
assert exists{s : s in S | s[2] eq 2};
// So the adjoint has a jordan block of size 2, so it is not semisimple

// other idempotent is 1-x
assert IsIdempotent(id-x);

// idempotents in an orbit of size 3





// --------------------------------------------

A, gen, frob := M3A();
F<al,bt> := BaseRing(A);

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);
G := sub<GL(4,F) | t1,t2>;
assert Order(G) eq 6; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

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

G := ChangeRing(G, FCl);
orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #orbs eq 8;
assert {* #o : o in orbs *} eq {* 1^^4, 3^^4 *};

// 0 is always an idempotent

// need to consider separately when 3*al^2 + 3*al*bt - bt - 1 = 0
so, id := HasOne(A);
assert so;
assert id eq -4*(2*al -1)/(al*(3*al^2 + 3*al*bt - bt - 1))*A.4;

x := r*(A.1+A.2+A.3) + 2*(2*al - 1)/(al*(3*al^2 + 3*al*bt - bt - 1)) * ((3*al + bt + 1)*r -1)*A.4;
assert IsIdempotent(x);
// There are 3 eigenvalues, 1, 0 and 
assert Dimension(Eigenspace(x, (-3*al + bt + 1)/2*r + 1/2)) eq 2;
// But it is not Jordan type a in general as not graded.  Have a*a = {1,0,a}
evals, espace, FL := IdentifyFusionLaw(x);
assert Order(Grading(FL)) eq 1;

// the fourth idempotent fixed by the Miyamoto group is 1-x
assert IsIdempotent(id-x);
// Fusion law comes from x

// Now consider the idempotents in the orbits orbits of size 3
// clearly, one orbit is the axes
// another is 1 - axes

assert IsIdempotent(A.1) and IsIdempotent(id-A.1);

y := x + (-3*al + bt + 1)/(2*al - 1)*r*A.1 -2^2*(3*al - bt - 1)/(3*al^2 + 3*al*bt - bt - 1)*r*A.4;
assert IsIdempotent(y);
assert y eq (bt-al)/(2*al-1)*r*A.1 + r*(A.2+A.3) + 2/(al*(3*al^2 + 3*al*bt - bt - 1))*( (4*al*bt + al - bt - 1)*r - (2*al - 1) )*A.4;

evals, espaces, FL := IdentifyFusionLaw(y);
lm := (3*al - bt - 1)/2*r + 1/2;
mu := -(2*bt-1)*(3*al-bt-1)/(4*al - 2)*r + 1/2;
assert { e[1] : e in evals} eq {1,0,lm, mu};

assert Order(Grading(FL)) eq 2;
assert y*(A.2-A.3) eq mu*(A.2-A.3);
// Miyamoto involution is the same

// Almost Monster type (lm,mu): lm*lm = {1,0,a}
u_lm := (5*al + bt - 3)*A.1 + (2*al-1)*(A.2+A.3) + 4*(2*al-1)/al*A.4;
assert y*u_lm eq lm*u_lm;

u_0 := al*(al-bt)*(3*al^2 + 3*al*bt - bt - 1)*A.1 - al*(2*al-1)*(3*al^2 + 3*al*bt - bt - 1)*(A.2+A.3)
          + 2*(2*al - 1)*( (3*al - bt - 1)*(2*al*bt - al - bt - 1)*r - (4*al*bt + al - bt - 1) )*A.4;
assert y*u_0 eq A!0;

// Becomes Monster type iff bt = 1/2
V := VectorSpaceWithBasis([ Vector(v) : v in [y,u_0,u_lm,A.2-A.3]]);
coord := Coordinates(V, Vector(u_lm^2));
assert coord[4] eq 0;
assert coord[3] eq -(2*al-1)*(2*bt-1);


// both x and A.4 are fixed by the Miyamoto group, so y in in an orbit of size 3

assert IsIdempotent(id-y);


//---------------------------------------------------

// Now need to deal with the case where 3*al^2 + 3*al*bt - bt - 1 = 0
// Saw above that then al \neq 1/3 and so
// bt := (1-3*al^2)/(3al-1)

A, gen, frob := M3A();
F<al,bt> := BaseRing(A);

FF<Al> := FunctionField(QQ);
Bt := (1-3*Al^2)/(3*Al-1);
phi := hom<F->FF | [Al, Bt]>;

A := ChangeRing(A, FF, phi);

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

// zero is also an idempotent and so these are the only two in an orbit of size 1
// For the orbits of size 3, we have the axes and

y := 1/Al*A.1 -x  + 2*r*(Al-1)/Al^2*A.4;
assert IsIdempotent(y);

assert y eq (Al+1/3)/(2*Al^2)*A.1 - r*(A.2 + A.3) - r*(Al+1)/Al^2*A.4;
// These are the only idempotents.

// A.4 is the only nilpotent element up to scaling

//---------------------------------------------------

// Now suppose 3*al-bt-1 = 0
// Hence bt = 3al-1
// As above, this is a case which has a 1-dim ideal giving a split extension

// Here the common al-eigenvalue is a nilpotent element
// This is the only nilpotent element up to scaling

A, gen, frob := M3A();
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


//---------------------------------------------------

// Now suppose that 2*al*bt-al-bt-1 = 0
// since al \neq 1/2 can rearrange to get
// bt = (al+1)/(2*al-1);

A, gen, frob := M3A();
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

// Nilpotent elements are scalar multiples of
n1 := -Al^2*(2*Al^2-2*Al-1)/(2*Al-1)^2*A.1 + Al^2*(A.2+A.3) + 2*A.4;
// and the orbits of n1 under Miy

n2 := Al^2*(A.1+A.2+A.3) + 2*(2*Al-1)*A.4;
