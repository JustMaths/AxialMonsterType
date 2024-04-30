/*

Some utilities for helping to build algebra structure constants and bilinear forms

*/
ZZ := Integers();
QQ := Rationals();
/*

Begin with some useful functions for building the multiplication table from some products and an action of a group.

*/
// --------------------------------------------
//
//              Useful functions
//
// --------------------------------------------
intrinsic BuildSymmetricMultiplication(S::SeqEnum, G::GrpPerm) -> SeqEnum
  {
  Given a permutation group G on n letters and a sequence of tuples <i,j,v>, built a symmetric multiplication table with entry i,j being a vector v of length n, using the action of G.
  }
  n := Degree(G);
  require forall{ t : t in S | #t eq 3 
                  and Type(t[1]) eq RngIntElt and t[1] in [1..n]
                  and Type(t[2]) eq RngIntElt and t[2] in [1..n]
                  and ((Type(t[3]) eq SeqEnum and #t[3] eq n) or (Type(t[3]) eq ModTupFldElt and Degree(t[3]) eq n))}: "Data is not given in the correct form";

  mult := [[ ] : j in [1..n]];

  for s in S, g in G do
    i,j,v := Explode(s);
    v := Eltseq(v); // in case v is a ModTupFldElt
    vg := PermuteSequence(v,g^-1);
    if IsDefined(mult[i^g],j^g) then
      require mult[i^g,j^g] eq vg: "The multiplication given is not symmetric";
    else
      mult[i^g,j^g] := vg;
      mult[j^g,i^g] := vg;
    end if;
  end for;
  
  return mult;
end intrinsic;

intrinsic BuildSymmetricBilinearForm(S::SeqEnum, G::GrpPerm) -> AlgMatElt
  {
  Given a permutation group G on n letters and a sequence of tuples <i,j,r>, built the Gram matrix of a bilinear form with entry i,j being a r, using the action of G.
  }
  n := Degree(G);
  require forall{ t : t in S | #t eq 3 
                  and Type(t[1]) eq RngIntElt and t[1] in [1..n]
                  and Type(t[2]) eq RngIntElt and t[2] in [1..n]
                  and ISA(Type(t[3]), FldElt)}: "Data is not given in the correct form";
  
  bil := [[ ] : j in [1..n]];

  for s in S, g in G do
    i,j,r := Explode(s);
    if IsDefined(bil[i^g],j^g) then
      require bil[i^g,j^g] eq r: "The form given is not symmetric";
    else
      bil[i^g,j^g] := r;
      bil[j^g,i^g] := r;
    end if;
  end for;
  
  return Matrix(bil);
end intrinsic;

function AllOnesMatrix(R, m, n)
  return Matrix(R, m, n, [ 1 : i in [1..n*m]]);
end function;

// L is lower triangular sequence of sequences.
function MakeSymmetric(L)
  M := L;
  for i in [1..#L], j in [i+1..#L] do
    M[i,j] := M[j,i];
  end for;
  
  return M;
end function;
