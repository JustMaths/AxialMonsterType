/*

Some functions to return the non-symmetric 2-generated Monster type (al, bt) algebras together with a few other connected algebras.

In general, our intrinsics will return an algebra, a set of two generators and the Frobenius form.

We will use the notation for the algebras coming from

C. Franchi, M. Mainardis, J McInroy, M. Turner, The Classification of the $2$-generated Primitive Axial Algebras of Monster Type, arXiv:2605.18737, May 2026, 107 pages.

*/
import "Utilities_for_algebra_creation.m": ZZ, QQ;
// --------------------------------------------
//
//          Algebras on X(1+2)' axet
//
// --------------------------------------------
intrinsic M3Cprime(:base_ring := ZZ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 3C^\prime(al, 1-al) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base ring.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_ring);
  
  G := sub<Sym(3) | (2,3)>;
  
  V := VectorSpace(F, 3);
  S := [<1,1,V.1>, <1,2, (1+al)/2*V.1 +(1-al)/2*(V.2-V.3)>, <2,2,V.2>,
        <2,3,(1+al)/2*V.1 -(1-al)/2*(V.2+V.3)>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F,3 | mult>;
  
  T := [ <1,1,2-al>, <1,2,1/2*(2-al)*(al+1)>, <2,2,al+1>, <2,3,al/2*(al+1)>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M3Cprime(al::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 3C^\prime(al, 1-al) algebra, with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(al));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  require F!al notin { F | 1, 0, 1/2}: "The value of beta cannot be 1, 0, or 1/2.";
  
  A, gens, frob := M3Cprime(:base_ring:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [al]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;

intrinsic M3Qprime(:base_ring := ZZ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 3Q'(1/3, 2/3) algebra, with generators and its Frobenius form.  Optional paramenter base_ring of the base ring.
  }
  require Characteristic(base_ring) notin {2, 3}: "The characteristic of the field cannot be 2, or 3.";
  F := FieldOfFractions(base_ring);
  
  G := sub<Sym(4) | (1,3)>;
  
  V := VectorSpace(F, 4);
  S := [<1,1,V.1>, <1,2, V![2/3,1/6,0,-1/6]>, <1,3, V!0>, <1,4, V![2/3,-1/6,0,1/6]>,
        <2,2,V.2>, <2,4,1/3*V![2,-1,2,-1]>, <4,4,V.4>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F,4 | mult>;
  
  T := [ <1,1,F!5/8>, <1,2,F!5/12>, <1,3,F!0>, <1,4,F!5/12>, <2,2,F!1>, <2,4,F!1/6>, <4,4,F!1>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;
// --------------------------------------------
//
//          Algebras on X_4 axet
//
// --------------------------------------------
intrinsic M4Q(:base_ring := ZZ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4Q(2bt, bt) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base ring.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  F<bt> := FunctionField(base_ring);
  
  G := sub<Sym(4) | (2,4), (1,3)>;
  
  V := VectorSpace(F, 4);
  S := [<1,1,V.1>, <1,2, bt/2*V![2,1,0,-1]>, <1,3, V!0>, <2,2,V.2>, <2,4,bt*V![-1,1,-1,1]>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F,4 | mult>;
  
  T := [ <1,1,F!1>, <1,2,bt>, <1,3,F!0>, <2,2,F!2>, <2,4,2*bt>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M4Q(bt::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4Q(2bt, bt) algebra, with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(bt));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  require F!bt notin { F | 1, 0, 1/2}: "The value of beta cannot be 1, 0, or 1/2.";
  
  A, gens, frob := M4Q(:base_ring:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [bt]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;

intrinsic M4Qx(:base_ring := ZZ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4Q(-1, -1/2)^\times algebra, with generators and its Frobenius form.  Optional paramenter base_ring of the base ring.
  }
  require Characteristic(base_ring) notin {2, 3}: "The characteristic of the field cannot be 2, or 3.";
  F := FieldOfFractions(base_ring);
  
  G := sub<Sym(3) | (1,3)>;
  
  V := VectorSpace(F, 3);
  S := [<1,1,V.1>, <1,2, -1/4*V![3,2,1]>, <1,3, V!0>, <2,2,V.2>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F,3 | mult>;
  
  T := [ <1,1,F!1>, <1,2,-1/2>, <1,3,F!0>, <2,2,F!2>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M4BNonSymmetric(:base_ring := ZZ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4B(-1, 1/2; nu) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base ring.
  }
  require Characteristic(base_ring) notin {2, 3}: "The characteristic of the field cannot be 2, or 3.";
  F<nu> := FunctionField(base_ring);
  
  G := sub<Sym(4) | (2,4), (1,3)>;
  
  V := VectorSpace(F, 4);
  S := [<1,1,V.1>, <1,2, 1/4*( (1-nu)*V.1 + nu*V.2 - (1+nu)*V.3 +(nu-2)*V.4 )>,
        <1,3, -(nu+1)/2*(V.1+V.3) + (nu-1)/2*(V.2+V.4)>, <2,2,V.2>, <2,4, -nu/2*(V.1+V.3) + (nu-2)/2*(V.2+V.4)>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F,4 | mult>;
  
  T := [ <1,1,F!1>, <1,2,1/4>, <1,3,-1/2>, <2,2,F!1>, <2,4,-1/2>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M4BNonSymmetric(nu::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4B(-1, 1/2; nu) algebra, with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(nu));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  require F!nu ne F!1/2: "If nu is 1/2, then the quotient is in fact symmetric.";
  
  A, gens, frob := M4BNonSymmetric(:base_ring:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [nu]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;
