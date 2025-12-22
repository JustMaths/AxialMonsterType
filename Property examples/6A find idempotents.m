AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";


///////////////////////////////////////////////////////////////////////////////////////////

////////////////                  6A(al, (-al^2)/(4(2al-1)))

//////////////////////////////////////////////////////////////////////////////////////////

A , gen, frob := M6A();
F<al> := BaseRing(A);

bt := -al^2/4/(2*al-1);

assert bt-1 eq (-al^2-8*al+4)/(4*(2*al-1));
assert al-bt eq al*(9*al-4)/(4*(2*al-1));


t1:= MiyamotoInvolution(A.1);
t2:= MiyamotoInvolution(A.2);
f := PermutationMatrix(F,[2,1,6,5,4,3,7,8]);
assert forall{<i,j> : i,j in [1..8] | ((A.i)*f)*((A.j)*f) eq (A.i*A.j)*f};

G := sub<GL(8,F) | t1,t2,f>;
Miy := sub<GL(8,F)|t1,t2>;
assert Order(Miy) eq 6;
assert Order(G) eq 12;

tt1 := Sym(8)!(2,6)(3,5);
tt2 := Sym(8)!(4,6)(3,1);
ff := Sym(8)![2,1,6,5,4,3,7,8];

GG := sub<Sym(8)| tt1,tt2,ff>;

// Finding the variety is quicker in a different basis
bas := [ A.1-A.3, A.3-A.5, A.4-A.6, A.6-A.2, A.1+A.2+A.3-(A.4+A.5+A.6), A.1+A.2+A.3+A.4+A.5+A.6, A.7,A.8];

CoB := Matrix(bas);

A_bas := ChangeBasis(A, bas);
frob_bas := CoB*frob*Transpose(CoB);

P := PolynomialRing(F, Dimension(A));

AP := ChangeRing(A_bas, P);
frobP := ChangeRing(frob_bas,P);

x := &+[ P.i*AP.i : i in [1..Dimension(A)]];  // this is a general element in the algebra

// Instead of finding an idempotent e directly by solving e^2 = e
// Write e = id/2 + x
// Then id - e = id/2 - x
// Find the x instead.  We must have e = e^2 = (id/2 - x)^2 = id/4 - x - x^2
// So x^2 = id/4
// Can also get (x,x) = (x^2, id) = (id/4,id) as another relation

so, id := HasOne(A_bas);
len_id := InnerProduct(id*frob_bas,id);
y := AP!Eltseq(id/4);


conj_class := [ g[3] : g in Classes(G) | g[1] ne 1];  // remove the identity

Js := [];

for g in conj_class do
  gbas := CoB*g*CoB^-1;
  
  Jg := ideal< P | Eltseq(x^2-y) cat [InnerProduct(x*frobP,x) -P!(len_id/4)] cat
                   Eltseq(x*ChangeRing(gbas, P)-x) >;

  Append(~Js, Jg);
end for;

I := ideal< P | Eltseq(x^2-y) cat [InnerProduct(x*frobP,x) -P!(len_id/4)]>;

// WARNING - takes 172 hours
assert IsZeroDimensional(I);

// takes 5 mins
prims := [ RadicalDecomposition(J) : J in Js];


FCl := AlgebraicClosure(F);
ACl := ChangeRing(A, FCl);
frobCl := ChangeRing(frob, FCl);

so, id := HasOne(ACl);
assert so;

// Takes a LONG time
// Now we want to get the varieties, change basis and recover the idempotents from the x's
// Xs := &cat[ [ Vector([ t[i] : i in [1..8]]) : t in Variety(K, FCl)] : K in p, p in prims];


// We want to look individually at these as it is computationally less expensive

assert [ Order(conj_class[i]) : i in [1..5]] eq [2,2,2,3,6];
assert [#t : t in prims] eq [32, 17, 53, 16, 8];

// pick which prims to look at
i := 1;

Xs := &cat [ [ Vector([ t[i] : i in [1..8]]) : t in Variety(K, FCl)] : K in prims[i]];
Xs := Rows(Matrix(Xs)*ChangeRing(CoB, FCl));

// even partial simplification is a few minutes
Simplify(FCl:Partial:=true);
Prune(FCl);

orbs := [ Orbit(GG, v) : v in Xs];
orbs := IndexedSet(orbs);
orbs := {@ {@ id/2 + ACl!v : v in o@} : o in orbs@};
Sort(~orbs, func<x,y|#x-#y>); // sort smallest first


