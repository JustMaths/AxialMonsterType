/*
******************************

Code to verify properties of the 4Y(al, (1-al^2)/2) algebra

******************************
*/
AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";

QQ := Rationals();

// =========================================================
//
// 4Y(al, (1-al^2)/2 )
//
// =========================================================
A, gen, frob := M4Y_al();
F<al> := BaseRing(A);
bt := (1-al^2)/2;

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

// Deal with this case later

assert Determinant(frob) eq -1/16*al^4*(al-2)^3/(al+1);
// Since the characteristic is not 2 and al \neq 0 or -1, we just need to check al = 2

A, gen, frob := M4Y_al(2);

P<lm> := PolynomialRing(QQ);
assert CharacteristicPolynomial(frob) eq lm^3*(lm-2)^2;
// So Radical has dim at most 3 in any char.

R := NullSpace(frob);
assert Dimension(R) eq 3;
a := A.1-A.3;
b := A.2-A.4;
c := A.5;
assert a in R;
assert b in R;
assert c in R;

// Quotient is 2B = F^2
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
//------------------------------

// Idempotents

//------------------------------

// ---------------------------------------------------
//
// Check singular locus
//

A, gen, frob := M4Y_al();
II := IdealOfSingularPoints(A);
primII := RadicalDecomposition(II);
P := Generic(II);

assert #primII eq 35;

// We can't have al = 0.
// If al = 1/2, then 4Y_al = 4Y_bt which has infinitely many idempotents.  So we can deal with this case there
bad := [ J : J in primII | P.6 notin J and P.6-1/2 notin J];
assert forall{ J : J in bad | P.6-2 in J};

// So al = 2 is a case we need to look at seperately.

// --------------------------------

// Idempotents

// --------------------------------
A, gen, frob := M4Y_al();
F<al> := BaseRing(A);
bt := (1-al^2)/2;

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(F, [2,1,4,3,5]);
G := sub<GL(5,F) | t1,t2,f>;

assert Order(G) eq 8; // Needed to ensure Magma knows the order of the group over FCl and so to be able to take orbits

FCl := AlgebraicClosure(F);
// Need to add roots
r := Sqrt(FCl!(al^2+2*al-2)/(al^4-2*al^3+4*al-2));
s := Sqrt(FCl!(2*al - 1)/(al^4 - 2*al^3 + 4*al - 2));
// These are the same roots as for 4B with the transformation \al \mapsto 1-\al applied.

// Bad points are roots of al^4 - 2*al^3 + 4*al - 2, al^2 + 2*al - 2, and al = 1/2.  Also need to check al = 2 from above.

A := ChangeRing(A, FCl);
frob := ChangeRing(frob, FCl);
idems := FindAllIdempotents(A);
Simplify(FCl);
Prune(FCl);

G := ChangeRing(G, FCl);
orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #orbs eq 12;
assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^6 *};

// Same as for 4B

// Orbits of size 1
// There is the zero vector, and A.5, id and id-A.5
so, id := HasOne(A);
assert so;
assert id eq 1/al*A![1,1,1,1, -(2+al)];

assert InnerProduct(Vector(A.5)*frob,Vector(A.5)) eq (2-al)/(al+1);
assert HasJordanFusionLaw(A.5: fusion_value:=1-al);
assert Dimension(Eigenspace(A.5, 0)) eq 2;
assert Dimension(Eigenspace(A.5, 1-al)) eq 2;
assert MiyamotoInvolution(A.5) eq t1*t2;

assert HasJordanFusionLaw(id-A.5: fusion_value:=al);
assert Dimension(Eigenspace(id-A.5, 1)) eq 2;
assert Dimension(Eigenspace(id-A.5, al)) eq 2;
assert MiyamotoInvolution(id-A.5) eq t1*t2;

assert InnerProduct(id*frob, id) eq (al + 4)/(al + 1);
assert InnerProduct(A.5*frob, A.5) eq (-al + 2)/(al + 1);
assert InnerProduct((id-A.5)*frob, (id-A.5)) eq 2;


// Orbits of size 2
// Each 3C subalgebra has its own identity id_3C and then id_3C - A.5
id_3C := 1/al*(A.1+A.3-A.5);
assert IsIdempotent(id_3C);
assert HasJordanFusionLaw(id_3C: fusion_value:=1-al);
assert Dimension(Eigenspace(id_3C, 1)) eq 3;
assert MiyamotoInvolution(id_3C) eq t1;

assert IsIdempotent(id_3C-A.5);
assert HasJordanFusionLaw(id_3C-A.5: fusion_value:=al);
assert Dimension(Eigenspace(id_3C-A.5, 0)) eq 3;
assert MiyamotoInvolution(id_3C-A.5) eq f*t1*f;

assert InnerProduct(id_3C*frob, id_3C) eq 3/(al + 1);
assert InnerProduct((id_3C-A.5)*frob, (id_3C-A.5)) eq 1;


// orbits of size 4
// the axes, id - axes
// there is also the orbit of x := id_3C - A.1 and id - x

assert InnerProduct((id-A.1)*frob, (id-A.1)) eq 3/(1+al);

x := id_3C - A.1;
assert IsIdempotent(x);
assert HasMonsterFusionLaw(x: fusion_values:=[1-al, 1-al-bt]);
assert Dimension(Eigenspace(x, 0)) eq 2;
assert MiyamotoInvolution(x) eq t1;

assert InnerProduct(x*frob, x) eq (2-al)/(1+al);
assert InnerProduct((id-x)*frob, (id-x)) eq 2;


// Final two orbits: id/2 \pm y
y := r/2/al*A![1-al, 1-al, 1-al, 1-al, al^2-2] + s/2*A![1,1,-1,-1,0];
assert IsIdempotent(1/2*id + y);
evals, espace, FL := IdentifyFusionLaw(1/2*id + y);
assert #FL eq 5;
assert Order(Grading(FL)) eq 2;
assert MiyamotoInvolution(1/2*id + y) eq f;

assert InnerProduct((1/2*id + y)*frob, 1/2*id + y) eq (4+al)/2/(al+1)+(1-2*al+2*bt)*r/2/(1+al);
assert InnerProduct((1/2*id - y)*frob, 1/2*id - y) eq (4+al)/2/(al+1)-(1-2*al+2*bt)*r/2/(1+al);

// ----------------------
//
// Check for new axes

poss := FindMatchingIdempotents(A.1, orbs);

assert #poss eq 1;

P<t> := PolynomialRing(F);
assert CharacteristicPolynomial(AdjointMatrix(A.1)) - poss[1,2] eq (al^2-1)/2*t^2*(t^2 -(al+1)*t +al);

// But al neq \pm 1, so no extra axes

// ---------------------------------------
//
// Don't need to check the exceptional cases as they will follow from the isomorphism with 4B, all apart from al = 2


// ---------------------------------------
//
// Check al = 2

al := 2;
bt := (1-al^2)/2;

assert bt eq -3/2;
// so char ne 3

A, gens, frob := M4Y_al(al);

P<lm, mu, nu> := PolynomialRing(QQ, 3);

AP := ChangeRing(A, P);

// Can prove this theoretically.  These are some calculations to support this.

// Radical is spanned by x0, x1 and c
x0 := AP.1-AP.3;
x1 := AP.2-AP.4;
c := AP.5;

assert x0^2 eq -3*c;
assert x1^2 eq -3*c;
assert x0*x1 eq 0;
assert c^2 eq c;
assert c*x0 eq -x0;
assert c*x1 eq -x1;

assert (AP.1+AP.3)*x0 eq x0;
assert (AP.1+AP.3)*x1 eq -3*x1;
assert (AP.1+AP.3)*c eq 3*c;

// First check if an idempotent can be in R
x := lm*x0 + mu*x1 + nu*AP.5;

assert x^2 eq -2*lm*nu*x0 -2*mu*nu*x1 +(nu^2-3*(lm^2+mu^2))*c;
/*
Then we get

nu = -1/2

and, as char ne 3, 

lm^2 + mu^2 =1/4
*/

// Check for fusion law

F<Lm, Mu>, phi := quo<P | lm^2+mu^2-1/4, nu>;

AA := ChangeRing(AP, F);

x := Lm*AA!Eltseq(x0) + Mu*AA!Eltseq(x1) - 1/2*AA.5;

PP<t> := PolynomialRing(F);
assert CharacteristicPolynomial(AdjointMatrix(x)) eq t^2*(t-1)*(t+1)*(t-1/2);

so, id := HasOne(A);
assert so;
assert id eq 1/2*(A.1+A.2+A.3+A.4) -2*A.5;


idAA := AA!Eltseq(id);
assert CharacteristicPolynomial(AdjointMatrix(idAA-x)) eq t*(t-1)^2*(t-2)*(t-1/2);

// So neither can be Monster type (2, -3/2)

// Now suppose that the image is the sum of the axes in 2B


id := AP!Eltseq(id);

// The image of this is the id in 2B
x := id + lm*x0 + mu*x1 + nu*AP.5;

assert x^2 eq id + 2*lm*(1-nu)*x0 + 2*mu*(1-nu)*x1
                    + (nu^2 +2*nu - 3*(lm^2+mu^2))*c;

// Now suppose that the image of x is an axis in A/R \cong 2B

x := 1/2*(AP.1 + AP.3) + lm*x0 + mu*x1 + nu*c;

assert x^2 eq 1/2*(AP.1+AP.3) + (1-2*nu)*lm*x0 - (2*nu+3)*mu*x1
                    + (nu^2 + 3*nu - 3*(lm^2+mu^2)  + 3/4)*c;

// We get 6 solutions here and by symmetry 6 more

// Check computationally (over Q) 
I := IdempotentIdeal(A);

assert Dimension(I) eq 1;

prim := RadicalDecomposition(I);

assert #prim eq 18;

prim0 := [ J : J in prim | Dimension(J) eq 0];
prim1 := [ J : J in prim | Dimension(J) ne 0];

P := Generic(I);
assert #prim0 eq 16;
assert #prim1 eq 2;

// 1-dimensional ideal
J := ideal<P | P.1+P.3, P.2+P.4, P.5+1/2, P.1^2+P.2^2-1/4>;
assert J in prim1;

// other ideal is id - this
so, id := HasOne(A);
assert so;
assert id eq 1/2*A![1,1,1,1,-4];

// So need to replace P.1 with 1/2-P.1 and P.5 with -2 -P.5
Jpair := ideal<P | P.1+P.3-1, P.2+P.4-1, (-2-P.5)+1/2, (1/2-P.1)^2+(1/2-P.2)^2-1/4>;
assert Jpair in prim1;

// 0-dimensional ideal
J := &meet prim0;

assert VarietySizeOverAlgebraicClosure(J) eq 16;
var := Variety(J);
assert #var eq 16;
// So we don't need an extension field

idems := [ A![t[i] : i in [1..5]] : t in var];

t1 := MiyamotoInvolution(A.1);
t2 := MiyamotoInvolution(A.2);

f := PermutationMatrix(QQ, [2,1,4,3,5]);
G := sub<GL(5,QQ) | t1,t2,f>;

orbs := {@ {@ A!u : u in Orbit(G, Vector(v))@} : v in idems @};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first

assert #orbs eq 8;
assert {* #o : o in orbs *} eq {* 1^^4, 2^^2, 4^^2 *};


// Orbits of length 1
so, id := HasOne(A);
assert so;
assert IsIdempotent(A.5);

// Orbits of size 2
// Each 3C subalgebra has its own identity id_3C and then id_3C - A.5
id_3C := 1/(al)*(A.1+A.3-A.5);

assert exists(oid3C){o : o in orbs | id_3C in o};

assert id-id_3C notin oid3C;

// orbits of size 4
// the axes, id - axes
// there is also the orbit of x := id_3C - A.1 and id - x

assert exists(axes){o : o in orbs | A.1 in o};

assert id - A.1 notin axes;

assert exists(id_axes){o : o in orbs | id-A.1 in o};

assert IsIdempotent(id_3C-A.1);
assert IsIdempotent(id-(id_3C-A.1));

assert id_3C - A.1 eq 1/2*(-A.1+A.3-A.5);
// this is in the infinite family given by J
// lm = -1, mu = 0

// So id - (id_3C -A.1) is in Jpair

// What about 1/2id pm y ???
assert (al^2+2*al-2)/(al^4-2*al^3+4*al-2) eq 1;
assert (2*al - 1)/(al^4 - 2*al^3 + 4*al - 2) eq 1/2;
// So r = \pm 1 and s = \pm 1/\sqrt{2}

/*
Claim that these are also in J and Jpair.  From above

 y := r/2/al*ACl![1-al, 1-al, 1-al, 1-al, al^2-2] + s/2*ACl![1,1,-1,-1,0];

the first part plus id/2 cancels all the axes and leaves -1/2c
*/
assert 1/2*id + r/2/al*A![1-al, 1-al, 1-al, 1-al, al^2-2] eq -1/2*A.5; 
/*
this leaves lm = 1/2sqrt{2} = mu which is a solution to lm^2 + mu^2 = 1/4

so 1/2id + y is in J and so 1/2id - y is in Jpair

*/

poss := FindMatchingIdempotents(A.1, orbs);

assert #poss eq 1;

P<t> := PolynomialRing(F);
assert CharacteristicPolynomial(AdjointMatrix(A.1)) - poss[1,2] eq 3/2*t^2*(t^2 -3*t +2);

// So no problem as the characteristic is not 3
// If char = 3, then al = 2 = -1, a contradiction
// So no extra axes


// --------------------------------

// Isomorphism with 4B algebra

// --------------------------------
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


