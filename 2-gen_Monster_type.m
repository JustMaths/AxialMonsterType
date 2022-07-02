/*

Some functions to return the 2-generated Monster type (al, bt) algebras together with a few other connected algebras.

In general, our intrinsics will return an algebra, a set of two generators and the Frobenius form.

We will use the notation for the algebras coming from

J. McInroy, S. Shpectorov, From forbidden configurations to a classification of some axial algebras of Monster type, arXiv:2107.07415, 41 pages, Jul 2021

rather than Yabe's notation.  We will also use bases from the above poaper, rather than bases given by Yabe for several of the algebras.

*/
import "Utilities_for_algebra_creation.m": QQ, MakeSymmetric;
// --------------------------------------------
//
//          Algebras on X_3 axet
//
// --------------------------------------------
// NB this is in Yabe's basis
intrinsic M3A(:base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 3A(al, bt) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_field of the base field.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<al,bt> := FunctionField(base_field, 2);
  
  pi_fact := (3*al^2+3*al*bt-bt-1);
  pi := -al*pi_fact/(4*(2*al-1));
  proj1 := pi/al +1/4*(3*(al+bt) +1);
  
  G := sub<Sym(4) | (2,3), (1,2)>;
  
  V := VectorSpace(F, 4);
  S := [<1,1,V.1>, <1,2,V.4+(al-bt)/2*(V.1+V.2+V.3) +bt*(V.1+V.2)>,
        <1,4, pi*V.1>, <4,4,pi*V.4>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F,4 | mult>;
  
  T := [ <1,1,F!1>, <1,2,proj1>, <1,4,pi>, <4,4,pi*(pi/al -(3*al-bt-1)/4)>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M3A(al::RngElt, bt::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 3A(al, bt) algebra, with generators and its Frobenius form.
  }
  so, F := ExistsCoveringStructure(Parent(al), Parent(bt));
  require so: "The given values must lie in the same field.";
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  require F!al notin { F | 1,0,1/2}: "The value of alpha cannot be 1, 0, or 1/2.";
  require F!bt notin { F | 1,0,al}: "The value of beta cannot be 1, 0, or alpha.";
  
  A, gens, frob := M3A(:base_field:=F);
  
  FF<x,y> := BaseRing(A);
  phi := hom<FF->F | [al, bt]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;

// --------------------------------------------
//
//          Algebras on X_4 axet
//
// --------------------------------------------
// Yabe IV_1(1/4, bt)
// Yabe's basis
// <a_0, a_2> \cong <a_1, a_3> \cong 2B
intrinsic M4A(:base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4A(1/4, bt) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_field of the base field.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<bt> := FunctionField(base_field);
  
  G := sub<Sym(5) | (2,4), (1,3), (1,2)(3,4)>;
  
  V := VectorSpace(F, 5);
  S := [<1,1,V.1>, <1,2,(1+4*bt)/8*(V.1+V.2) + (1-4*bt)/8*(V.3+V.4) + V.5>,
        <1,3,V!0>, <1,5,(2*bt-1)/8*V.1>, <5,5,(2*bt-1)/8*V.5>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 5 | mult>;
  
  T := [ <1,1,F!1>, <1,2,bt>, <1,3,F!0>, <1,5,(2*bt-1)/8>, <5,5,(bt^2-bt+1/4)/4>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

// NB 4A does exist for bt = 1/4,1/8 unlike what Felix says.
intrinsic M4A(bt::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4A(1/4, bt) algebra, with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(bt));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  require F!bt notin { F | 1,0, 1/4}: "The value of beta cannot be 1, 0, or 1/4.";
  
  A, gens, frob := M4A(:base_field:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [bt]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;

// Yabe IV_2(al, al^2/2, 1/al)
// Used a better basis so that the 5th basis element is the third axis in the 3C(al) subalgebras <a_0,a_2> and <a_1, a_3>.
intrinsic M4B(:base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4B(al, al^2/2) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_field of the base field.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_field);
  bt := al^2/2;
  
  G := sub<Sym(5) | (2,4), (1,3), (1,2)(3,4)>;
  
  V := VectorSpace(F, 5);
  S := [<1,1,V.1>, <1,2,bt/2*V![1,1,-1,-1,1]>,
        <1,3,al/2*V![1,0,1,0,-1]>, <1,5,al/2*V![1,0,-1,0,1]>, <5,5,V.5>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 5 | mult>;
  
  T := [ <1,1,F!1>, <1,2,bt/2>, <1,3,al/2>, <1,5,al/2>, <5,5,1>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M4B(al::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4B(al, al^2/2) algebra, with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(al));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  P<t> := PolynomialRing(F);
  so2, root2 := HasRoot(t^2-2);
  if so2 then
    require F!al notin { F | 1,0, 2, -root2, root2}: "The value of alpha cannot be 1, 0, 2, -sqrt(2), or sqrt(2).";
  else
    require F!al notin { F | 1,0, 2}: "The value of alpha cannot be 1, 0, 2, -sqrt(2), or sqrt(2).";
  end if;
  
  A, gens, frob := M4B(:base_field:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [al]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;

// Yabe IV_1(al, al/2)
// Joshi's double Matsuo algebra Table 7 (p4226) in paper with Galt, Joshi, Mamontov, Shpectorov, Staroletov
// We use Joshi's basis, but reordered d1, d3, d2, d4, w
// <a_0, a_2> \cong <a_1, a_3> \cong 2B
intrinsic M4J(:base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4J(al, al/2) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_field of the base field.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_field);
  bt := al/2;
  
  G := sub<Sym(5) | (2,4), (1,3), (1,2)(3,4)>;
  
  V := VectorSpace(F, 5);
  S := [<1,1,V.1>, <1,2,bt/2*V![2,2,0,0,-1]>,
        <1,3,V!0>, <1,5,bt*V![2,-1,0,-1,1]>, <5,5,V.5>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 5 | mult>;
  
  T := [ <1,1,F!1>, <1,2,bt>, <1,3,0>, <1,5,al>, <5,5,2>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M4J(al::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4J(al, al/2) algebra, with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(al));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  require F!al notin { F | 1, 0, 2}: "The value of alpha cannot be 1, 0, or 2.";
    
  A, gens, frob := M4J(:base_field:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [al]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;

// Yabe IV_2(1/2, bt, (1-4bt)/2bt)
// <a_0, a_2> \cong <a_1, a_3> \cong S(delta), the spin factor algebra, where delta = 2^5*bt*(2*bt-1) - 2.
// We choose the 5th basis vector as generically the intersection of these two subalgebras, we normalise so that it is an idempotent.
// NB delta is never equal to 2
// But delta can equal -2 iff bt = 1/4.  Then these subalgebras become the 2-dimensional S(2)^\circ and don't intersect.  However, the algebra has no non-trivial proper ideals!
// NB projection graph is always connected, but can lose the edge between a_0 and a_2 iff bt=1/4
intrinsic M4Y_bt(:base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4Y(1/2, bt) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_field of the base field.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<bt> := FunctionField(base_field);
  
  G := sub<Sym(5) | (2,4), (1,3), (1,2)(3,4)>;
  
  V := VectorSpace(F, 5);
  S := [<1,1,V.1>, <1,2, bt/2*V![1,1,-1,-1,8*bt]>, <1,3, (1-4*bt)/2*(V.1+V.3)+4*bt(4*bt-1)*V.5>,
        <1,5, bt*V.1-bt*V.3+8*bt^2*V.5>, <5,5, V.5>];
  
  S := [<1,1,V.1>, <1,2, bt/2*V![1,1,-1,-1,2]>, <1,3, (1-4*bt)/2*(V.1+V.3)+(4*bt-1)*V.5>,
        <1,5, bt*V.1-bt*V.3+2*bt*V.5>, <5,5, 4*bt*V.5>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 5 | mult>;
  
  T := [ <1,1,F!1>, <1,2,4*bt^2>, <1,3,(4*bt-1)^2>, <1,5,2*bt>, <5,5, 1>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M4Y_bt(bt::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4Y(1/2, bt) algebra, with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(bt));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  require F!bt notin { F | 1,0,1/2}: "The value of beta cannot be 1, 0, or 1/2.";
  
  A, gens, frob := M4Y_bt(:base_field:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [bt]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;

// Yabe's VI_2(al, (1-al^2)/2, -1/(al+1))
// <a_0, a_2> \cong <a_1, a_3> \cong 3C(al), but they intersect not in the third axis, c, but in 1_U-c, where 1_U is the one for the 3C(al).  We choose this element which is also an idempotent (but an axis of Jordan type 1,0, 1-al in the 3C(al)) as the fifth basis element.
// NB that al \neq -1, so we always have a 1_U in the 3C(al).
intrinsic M4Y_al(:base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4Y(al, (1-al^2)/2) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_field of the base field.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_field);
  bt := (1-al^2)/2;
  
  G := sub<Sym(5) | (2,4), (1,3), (1,2)(3,4)>;
  
  V := VectorSpace(F, 5);
  S := [<1,1,V.1>, <1,2, V![bt/2,bt/2,-bt/2,-bt/2,(al+1)^2/4]>,
        <1,3, (al-1)/2*(V.1+V.3)+(al+1)/2*V.5>, <1,5, (al-1)/2*(-V.1+V.3)+(al+1)/2*V.5>, <5,5, V.5>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 5 | mult>;
  
  T := [ <1,1,F!1>, <1,2,-(al-2)*(al+1)/4>, <1,3,al/2>, <1,5,1-al/2>, <5,5, (2-al)/(al+1)>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M4Y_al(al::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 4Y(al, (1-al^2)/2) algebra, with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(al));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  P<t> := PolynomialRing(F);
  som1, rootm1 := HasRoot(t^2+1);
  so2, root2 := HasRoot(t^2-2);
  if som1 then
    require F!al notin { F | -rootm1, rootm1}: "The value of alpha cannot be 1, 0, -1, +/-sqrt(-1), or -1 +/-sqrt(2).";
  end if;
  if so2 then
    require F!al notin { F | -root2, root2}: "The value of alpha cannot be 1, 0, -1, +/-sqrt(-1), or -1 +/-sqrt(2).";
  end if;
  require F!al notin { F | 1, 0, -1}: "The value of alpha cannot be 1, 0, -1, +/-sqrt(-1), or -1 +/-sqrt(2).";
  
  A, gens, frob := M4Y_al(:base_field:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [al]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;
// --------------------------------------------
//
//          Algebras on X_5 axet
//
// --------------------------------------------
intrinsic M5A(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 5A(al, (5*al-1)/8) algebra over a function field with variable al, with generators and its Frobenius form.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_field);
  bt := (5*al-1)/8;
  
  G := Sym(6)!!DihedralGroup(5);
  
  V := VectorSpace(F,6);
  S := [<1,1,Eltseq(V.1)>, <1,2,Eltseq(bt*(V.1+V.2)+V.6)>, <1,3,Eltseq(-bt/2*(&+[V.i : i in [1..5]]) + bt*(V.1+V.3)-V.6)>, <1,6,Eltseq(-(al-bt)*bt*V.1 + (al-bt)*bt/2*(V.2+V.5) +(al-bt)*V.6)>, <6,6,Eltseq(-(7*al-3)*(al-bt)*bt/2^5*(&+[V.i : i in [1..5]]) -5*(al-bt)*bt/2*V.6)>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 6 | mult>;
  
  T := [ <1,1,F!1>, <1,2,3/4*bt>, <1,3,3/4*bt>, <1,6,-5/32*bt*(3*al+1)>, <6,6, 5/2^9*bt*(11*al+1)*(3*al+1)>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M5A(al::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 5A(al, (5*al-1)/8) algebra, with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(al));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  require F!al notin { F | 1,0,-1/3,1/5}: "The value of beta cannot be 1, 0, -1/3, or 1/5.";
  
  A, gens, frob := M5A(:base_field:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [al]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;
// --------------------------------------------
//
//          Algebras on X_6 axet
//
// --------------------------------------------
intrinsic M6A(:base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 6A algebra over a function field with variable al, with generators and its Frobenius form.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_field);
  bt := -al^2/(4*(2*al-1));
  
  G := sub<Sym(8) | (3,5)(2,6), (1,5)(2,4), (1,4)(2,5)(3,6)>;
  
  V := VectorSpace(F, 8);
  S := [<1,1,V.1>, <1,2,bt/2*(V.1+V.2-V.3-V.4-V.5-V.6+V.7+V.8)>,
        <1,3, al/4*(V.1+V.3) + al*(3*al-1)/(4*(2*al-1))*V.5 -al*(5*al-2)/(8*(2*al-1))*V.8>,
        <1,4, al/2*(V.1+V.4-V.7)>, <1,7, al/2*(V.1+V.7-V.4)>,
        <1,8, al*(3*al-2)/(4*(2*al-1))*(2*V.1-V.3-V.5 +V.8)>,
        <7,7,V.7>, <7,8,V!0>, <8,8, (al+2)*(3*al-2)/(4*(2*al-1))*V.8>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 8 | mult>;
  
  T := [ <1,1,F!1>, <1,2,-al^2*(3*al-2)/(4*(2*al-1))^2>,
         <1,3,al*(21*al^2-18*al+4)/(4*(2*al-1))^2>,
         <1,4,al/2>, <1,7,al/2>,
         <1,8, al*(7*al-4)*(3*al-2)/(8*(2*al-1)^2)>,
         <7,7,F!1>, <7,8,F!0>, <8,8, (al+2)*(7*al-4)*(3*al-2)/(8*(2*al-1)^2)>];
  frob := BuildSymmetricBilinearForm(T, G);
    
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M6A(al::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The 6A algebra for al, with generators and its Frobenius form.
  }
  F := Parent(al);
  if not IsField(F) then // If F is just a ring, we take the field of fractions.
    F := FieldOfFractions(BaseRing(F));
  end if;
  
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  P<t> := PolynomialRing(F);
  so5, root5 := HasRoot(t^2-5);
  if so5 then
    require F!al notin { F | 1,0,1/2, 4/9, -4+root5, -4-root5}: "The value of alpha cannot be 1, 0, 1/2, 4/9, -4+sqrt(5), -4-sqrt(5).";
  else
    require F!al notin { F | 1,0,1/2, 4/9}: "The value of alpha cannot be 1, 0, 1/2, 4/9, -4+sqrt(5), -4-sqrt(5).";
  end if;
  
  A, gens, frob := M6A(:base_field:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [al]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;

intrinsic M6J(:base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 6J algebra over a function field with variable al, with generators and its Frobenius form.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_field);
  bt := al/2;
  
  G := sub<Sym(8) | (3,5)(2,6), (1,5)(2,4), (1,4)(2,5)(3,6)>;
  
  V := VectorSpace(F, 8);
  S := [<1,1,V.1>, <1,2,bt/2*(2*(V.1+V.2)-V.8)>, <1,3, bt/2*(V.1+V.3-V.5)>,
        <1,4, al/2*(V.1+V.4-V.7)>, <1,7, al/2*(V.1+V.7-V.4)>,
        <1,8, al/2*(2*V.1-V.6-V.2+V.8)>,
        <7,7,V.7>, <7,8,bt*V.7>, <8,8, (bt+1)*V.8 -bt*V.7>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 8 | mult>;
  
  T := [ <1,1,F!1>, <1,2,bt>, <1,3,bt/2>, <1,4,al/2>, <1,7,al/2>,
         <1,8, al>, <7,7,F!1>, <7,8,bt>, <8,8, bt+2>];
  frob := BuildSymmetricBilinearForm(T, G);
    
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M6J(al::RatFldElt) -> AlgGen, AlgMatElt
  {
  The 6J algebra for al, with generators and its Frobenius form.
  }
  
end intrinsic;

// We use the basis given by a_0, a_2, a_4, d, z as in the Forbidden paper.
intrinsic M6Y(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 6Y(1/2, 2) algebra.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  // Only use part of the symmetry group
  G := sub<Sym(5) | (2,3), (1,3)>;
  F := base_field;
  V := VectorSpace(F, 5);
  
  S := [<1,1,V.1>, <1,2,V.1+V.2-V.3>, <1,4, 1/2*V.4+V.5>,
        <4,4, -2*V.5>, <1,5,V!0>, <4,5,V!0>, <5,5,V!0>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 5 | mult>;
  
  T := [ <1,1,F!1>, <1,2,F!1>, <1,4,F!0>, <4,4,F!0>, <4,5,F!0>, <1,5,F!0>, <5,5,F!0>];
  frob := BuildSymmetricBilinearForm(T, G);
    
  return A, {@ A.1, A.3 + A.4 @}, frob;
end intrinsic;
// --------------------------------------------
//
//          Algebras on X_\infty axet
//
// --------------------------------------------
intrinsic IY3(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  
  }
  
end intrinsic;

intrinsic IY3(al::RngElt, mu::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  }
  if mu eq 1 then    
    mult := [[[1,0,0,0], [1/2,1/2,(al-1/2),1], [0,0,al,0], [0,0,0,0]],
         [[1/2,1/2,(al-1/2),1], [0,1,0,0], [0,0,al,0], [0,0,0,0]],
         [[0,0,al,0], [0,0,al,0], [0,0,0,0], [0,0,0,0]],
         [[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]];
    
    A := Algebra<Rationals(),4 | mult>;
    return A;
  end if;
end intrinsic;

intrinsic IY5(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  
  }
  
end intrinsic;

intrinsic IY5(al::RngFldElt) -> AlgGen, SetIndx, AlgMatElt
  {
  }

end intrinsic;
