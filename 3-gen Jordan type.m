/*

We give code for Gorshkov and Staroletov's 3-gen axial algebra of Jordan type 1/2

https://www.sciencedirect.com/science/article/pii/S002186932030380X

If it has generators a,b,c, then the algebra is 9-dim, spanned by

a, b, c, ab, ac, bc, a(bc), b(ac), c(ab)

There is a natural action of S_3

*/
import "Utilities_for_algebra_creation.m": ZZ, QQ, MakeSymmetric;

intrinsic GS(: base_ring := ZZ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 3-generated axial algebra of Jordan type 1/2 described by Gorshkov and Staroletov.  The parameters are:
  al = \phi_a(b), bt = \phi_b(c), gm = \phi_c(a), psi = \phi_a(bc)
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  F<al,bt, gm, psi> := FunctionField(base_ring, 4);
  
  // The group acts semi-linearly on the algebra
  G := sub<Sym(9) | (2,3)(4,5)(8,9), (1,3)(4,6)(7,9)>;
  
  // NB definitions of al,bt,gm means that the action is not the same!
  phi3 := hom<G -> Sym(4) | [Sym(4) | (1,3), (1,2)]>;

  sg := hom<G -> Aut(F) | g:-> hom<F->F | PermuteSequence([al,bt,gm,psi], (g@phi3))> >;

  V := VectorSpace(F, 9);
  S := [<1,1,V.1>, <1,2,V.4>, <1,4, al/2*V.1 + 1/2*V.4>, <1,6, V.7>, <1,7, psi/2*V.1 + 1/2*V.7>,
        <1,8, 1/4*( psi*V.1 + gm*V.4 + al*V.5 + V.7 + V.8 - V.9)>,
        <4,4, al/4*(V.1 + V.2 + 2*V.4)>, <4,5,1/4*(psi*V.1 + gm*V.4 + al*V.5 - V.7 + V.8 + V.9)>,
        <4,7, 1/8*( (al*bt+psi)*V.1 + psi*V.2 + 2*psi*V.4 + al*V.6 + 2*al*V.7)>,
        <4,9, 1/8*(al*bt*V.1 + al*gm*V.2 + 4*psi*V.4 + al*V.6 + al*V.5 - 2*al*(V.7+V.8) + 4*al*V.9)>,
        <7,7, 1/16*( bt*(al+ gm + 2*psi)*V.1 + bt*gm*V.2 + al*bt*V.3 + 4*psi*V.6 
                     + (2*bt + 8*psi)*V.7 - 2*bt*V.8 - 2*bt*V.9)>,
        <7,8, 1/16*( bt*(gm + psi)*V.1 + gm*(bt + psi)*V.2 + al*psi*V.3 + 2*psi*V.4 + 2*(al*gm + psi)*V.6 + 2*(al*bt + psi)*V.5 + (4*psi-al+bt-gm)*V.7 + (4*psi-al-bt+gm)*V.8 + (al-bt-gm-4*psi)*V.9)>];
  
  T := [<1,1,F!1>, <1,2,al>, <1,4,al>, <1, 6, psi>, <1, 7, psi>, <1,8, (al*gm + psi)/2>,
        <4,4,(al^2 + al)/2>, <4,5,(al*gm + psi)/2>, <4,7, (al*bt + 2*al*psi + psi)/4>,
        <4,9, (al*bt + al*gm + 2*al*psi)/4>, <7,7, (al*bt + bt*gm + 2*bt*psi + 4*psi^2)/8>,
        <7,8,(2*al*bt*gm + al*psi + bt*gm + bt*psi + gm*psi + 2*psi^2)/8>];
  
  mult := [[ ] : j in [1..9]];
  
  for s in S, g in G do
    i,j,v := Explode(s);
    v := Eltseq(v); // in case v is a ModTupFldElt
    vg := [ x@(sg(g)) : x in PermuteSequence(v,g^-1)];
    if IsDefined(mult[i^g],j^g) then
      require mult[i^g,j^g] eq vg: "The multiplication given is not symmetric";
    else
      mult[i^g,j^g] := vg;
      mult[j^g,i^g] := vg;
    end if;
  end for;
  
  bil := [[ ] : j in [1..9]];
  for t in T, g in G do
    i,j,r := Explode(t);
    rg := r@(sg(g));
    if IsDefined(bil[i^g],j^g) then
      require bil[i^g,j^g] eq rg: "The form given is not symmetric";
    else
      bil[i^g,j^g] := rg;
      bil[j^g,i^g] := rg;
    end if;
  end for;
    
  A := Algebra<F,9 | mult>;
  frob := Matrix(F, bil);
  
  return A, {@ A.1, A.2, A.3@}, frob;
end intrinsic;

intrinsic GS(al, bt, gm, psi: base_ring := ZZ) -> AlgGen, SetIndx, AlgMatElt
  {
  The 3-generated axial algebra of Jordan type 1/2 described by Gorshkov and Staroletov.  The parameters are:
  al = \phi_a(b), bt = \phi_b(c), gm = \phi_c(a), psi = \phi_a(bc)
  }
  so1, F1 := ExistsCoveringStructure(Parent(al), Parent(bt));
  so2, F2 := ExistsCoveringStructure(Parent(gm), Parent(psi));
  so, F := ExistsCoveringStructure(F1, F2);
  if F eq Integers() then
    F := Rationals();
  end if;
  require so: "The given values must lie in the same field.";
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  
  A, gens, frob := GS(:base_ring:=F);
  
  FF<AL, BT, GM, PSI> := BaseRing(A);
  phi := hom<FF->F | [al, bt, gm, psi]>;
  
  A := ChangeRing(A, F, phi);
  return A, {@ A.1, A.2, A.3 @}, ChangeRing(frob, F, phi);
end intrinsic;

