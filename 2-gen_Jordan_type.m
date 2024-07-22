/*

The 2-generated algebras of Jordan type.

*/
QQ := Rationals();
// ------------------------------------
//
//           Matsuo algebras
//
// ------------------------------------
intrinsic M3C(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The Matsuo algebra 3C(eta) over a function field, with generators and its Frobenius form.  Optional paramenter base_field of the base field; default is the rationals.
  }
  F<eta> := FunctionField(base_field);

  G := sub<Sym(3) | (1,2), (2,3)>;
  
  V := VectorSpace(F, 3);
  S := [<1,1,V.1>, <1,2,eta/2*(V.1+V.2-V.3)>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 3 | mult>;
  
  T := [ <1,1,F!1>, <1,2,eta/2>];
  frob := BuildSymmetricBilinearForm(T, G);

  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic M3C(eta::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The Matsuo algebra 3C(eta), with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(eta));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  require F!eta notin { F | 1,0 }: "The value of eta cannot be 1, or 0.";

  A, gens, frob := M3C(:base_field:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [eta]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
end intrinsic;

intrinsic M3Cx(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The Matsuo algebra 3Cx(-1), with generators and its Frobenius form.  Optional paramenter base_field of the base field; default is the rationals.
  }
  F := base_field;
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  // Only use part of the symmetry group
  G := sub<Sym(2) | (1,2)>;
  
  V := VectorSpace(F, 2);
  S := [<1,1,V.1>, <1,2,-V.1-V.2>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 2 | mult>;
  
  T := [ <1,1,F!1>, <1,2,F!(-1/2)>];
  frob := BuildSymmetricBilinearForm(T, G);

  return A, {@ A.1, A.2 @}, frob;
end intrinsic;
// ------------------------------------
//
//       Spin Factors and other
//
// ------------------------------------
// NB this is in the 1, u, v basis
// This was called Cl^J(F^2, b_\dl) in Hall, Rehren, Shpectorov
intrinsic SpinFactor(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The spin factor algebra S(delta) over a function field, with generators and its Frobenius form.  Optional paramenter base_field of the base field; default is the rationals.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<dl> := FunctionField(base_field);

  G := sub<Sym(3) | (2,3)>;
  
  V := VectorSpace(F, 3);
  S := [<1,1,V.1>, <1,2,V.2>, <2,2,V.1>, <2,3,dl/2*V.1>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 3 | mult>;
  
  T := [ <1,1,F!2>, <1,2,F!0>, <2,2,F!2>, <2,3,dl>];
  frob := BuildSymmetricBilinearForm(T, G);

  return A, {@ (A.1+A.2)/2, (A.1+A.3)/2 @}, frob;
end intrinsic;

intrinsic S(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  "
  }
  A, gens, frob := SpinFactor(:base_field := base_field);
  return A, gens, frob;
end intrinsic;

intrinsic SpinFactor(dl::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  The spin factor algebra S(delta), with generators and its Frobenius form.
  }
  F := FieldOfFractions(Parent(dl));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  if F!dl eq 2 then
    print "Warning, the spin factor is not 2-generated.";
  end if;

  A, gens, frob := SpinFactor(:base_field:=F);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [dl]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ (A.1+A.2)/2, (A.1+A.3)/2 @}, ChangeRing(frob, F, phi);
end intrinsic;

intrinsic S(dl::RngElt) -> AlgGen, SetIndx, AlgMatElt
  {
  "
  }
  A, gens, frob := SpinFactor(dl);
  return A, gens, frob;
end intrinsic;

// The subalgebra S(2)^\circ.  This is Cl^0(F^2, b_2) in Hall, Rahren, Shpectorov.
intrinsic SpinFactorException(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The spin factor subalgebra S(2)^\circ, with generators and its Frobenius form.  Optional paramenter base_field of the base field; default is the rationals.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F := base_field;

  G := sub<Sym(2) | (1,2)>;
  
  V := VectorSpace(F, 2);
  S := [<1,1,V.1>, <1,2,1/2*(V.1+V.2)>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 2 | mult>;
  
  T := [ <1,1,F!1>, <1,2,F!1>];
  frob := BuildSymmetricBilinearForm(T, G);

  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic S2circ(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  "
  }
  A, gens, frob := SpinFactorException(:base_field := base_field);
  return A, gens, frob;
end intrinsic;

// The cover \widehat{S}(2)^\circ.  This is Cl^00(F^2, b_2) in Hall, Rahren, Shpectorov.
intrinsic SpinFactorCover(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  The spin factor cover \widehat S (2)^\circ, with generators and its Frobenius form.  Optional paramenter base_field of the base field; default is the rationals.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F := base_field;

  G := sub<Sym(3) | (1,2)>;
  
  V := VectorSpace(F, 3);
  S := [<1,1,V.1>, <1,2,1/2*(V.1+V.2)>, <1,3,V!0>, <3,3,V!0>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 3 | mult>;
  
  T := [ <1,1,F!1>, <1,2,F!1>, <1,3,F!0>, <3,3,F!0>];
  frob := BuildSymmetricBilinearForm(T, G);

  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic hatS2circ(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  "
  }
  A, gens, frob := SpinFactorCover(:base_field := base_field);
  return A, gens, frob;
end intrinsic;

intrinsic JordanUniversal(: base_field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Returns the universal 2-generated axial algebra of Jordan type J_\eta(\phi).  Optional paramenter base_field of the base field; default is the rationals.
  }
  require Characteristic(base_field) ne 2: "The characteristic of the field cannot be 2.";
  F<eta, phi> := FunctionField(base_field, 2);
  pi := (1-eta)*phi - eta;

  G := sub<Sym(3) | (1,2)>;
  
  V := VectorSpace(F, 3);
  S := [<1,1,V.1>, <1,2,eta*(V.1+V.2)+V.3>, <1,3,pi*V.1>, <3,3,pi*V.3>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 3 | mult>;
  
  T := [ <1,1,F!1>, <1,2,phi>, <1,3,pi>, <3,3,pi*(phi-2*eta)>];
  frob := BuildSymmetricBilinearForm(T, G);

  return A, {@ A.1, A.2 @}, frob;
end intrinsic;
