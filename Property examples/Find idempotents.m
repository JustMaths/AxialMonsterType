/*

Some code to find idempotents

*/
function IdempotentIdeal(A)
  F := BaseRing(A);
  P := PolynomialRing(F, Dimension(A));
  
  AP := ChangeRing(A, P);
  x := &+[ P.i*AP.i : i in [1..Dimension(A)]];
  I := ideal< P | Eltseq(x^2-x)>;
  
  return I, AP;
end function;

function NilpotentIdeal(A)
  F := BaseRing(A);
  P := PolynomialRing(F, Dimension(A));
  
  AP := ChangeRing(A, P);
  x := &+[ P.i*AP.i : i in [1..Dimension(A)]];
  J := ideal< P | Eltseq(x^2)>;
  
  return J;
end function;

function VarietyOverAlgbebraicClosure(A, I)
  var := Variety(I);
  n := Dimension(A);
  if #var ne VarietySizeOverAlgebraicClosure(I) then
    F := BaseRing(A);
    FCl := AlgebraicClosure(F);

    var := Variety(I, FCl);
    
    ACl := ChangeRing(A, FCl);
    idems := [ ACl![ t[i] : i in [1..n]] : t in var];
  else
    idems := [ A![ t[i] : i in [1..n]] : t in var];
  end if;
  
  return idems;
end function;

function FindAllIdempotents(A)
  I := IdempotentIdeal(A);
  
  if Dimension(I) ne 0 then
    print "ideal has dimension ", Dimension(I);
    return false;
  end if;
  
  var := Variety(I);
  n := Dimension(A);
  if #var ne VarietySizeOverAlgebraicClosure(I) then
    F := BaseRing(A);
    FCl := AlgebraicClosure(F);

    var := Variety(I, FCl);
    
    ACl := ChangeRing(A, FCl);
    idems := [ ACl![ t[i] : i in [1..n]] : t in var];
  else
    idems := [ A![ t[i] : i in [1..n]] : t in var];
  end if;
  
  return idems;
end function;

// return the squarefree part of a function field element
function SquareFreePart(x)
  F := Parent(x);
  
  sqrfree := function(r)
    fact, no := Factorisation(r);
    fact := &*([1] cat [ t[1]^(t[2] mod 2) : t in fact]);
    return SquareFree(Numerator(no))/SquareFree(Denominator(no))*F!fact;
  end function;
  
  return sqrfree(Numerator(x))/sqrfree(Denominator(x));
end function;


algebras := [ "M3A()", "M4A()", "M4B()","M4J()","M4Y_al()","M4Y_bt()","M5A()","M6A()","M6J()","M6Y()", "IY3()", "IY5()"];

// Test out which algebras have finitely many idempotents
/*
for alg in algebras do
  A := eval(alg);
  I := IdempotentIdeal(A);
  print alg, Dimension(I);
end for;
*/
