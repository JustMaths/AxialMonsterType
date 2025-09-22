/*

Some code to find idempotents

*/
function IdempotentIdeal(A)
  F := BaseRing(A);
  P := PolynomialRing(F, Dimension(A));
  
  AP := ChangeRing(A, P);
  x := &+[ P.i*AP.i : i in [1..Dimension(A)]];  // this is a general element in the algebra
  I := ideal< P | Eltseq(x^2-x)>;
  
  return I, AP;
end function;

function NilpotentIdeal(A)
  F := BaseRing(A);
  P := PolynomialRing(F, Dimension(A));
  
  AP := ChangeRing(A, P);
  x := &+[ P.i*AP.i : i in [1..Dimension(A)]];  // this is a general element in the algebra
  J := ideal< P | Eltseq(x^2)>;
  
  return J, AP;
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

// Only works for characteristic 0
function Pretty(x)
  F := Parent(x);
  assert Characteristic(F) eq 0;

  if Type(F) eq FldAC then
    Fbase := BaseField(F);
    so, xx := IsCoercible(Fbase, x);
    if so then
      return Pretty(xx);
    else
      Faff := AffineAlgebra(F);
      xx := Faff!x;
      coeffs := Coefficients(xx);
      mons := Monomials(xx);

      return [* < c_num, c_denom, F!mons[i]> where c_num, c_denom := Pretty(c) : i->c in coeffs*];
    end if;
  end if;
  
  // Factorise nicely
  function factor(y)
    fact, u := Factorisation(y);

    // Want to clear any fractions
    if ISA(Type(y), RngUPolElt) then
      denom_coeffs := [ LCM([Denominator(t) : t in Coefficients(p[1])]) : p in fact ];
    elif ISA(Type(y), RngMPolElt) then
      denom_coeffs := [ CoefficientDenominator(p[1]) : p in fact ];
    else
      // Element must be in the ground field
      assert Parent(y) eq Integers();
      denom_coeffs := [ 1 : p in fact];
    end if;
    
    d := IsEmpty(fact) select 1 else &*[ denom_coeffs[i]^t[2] : i -> t in fact];
    
    return [ < F!t[1]*denom_coeffs[i], t[2]> : i -> t in fact], u/d;
  end function;
  
  num_f, nu := factor(Numerator(x));
  denom_f, du := factor(Denominator(x));
  
  // Fix the sign
  if Characteristic(F) eq 0 then
    sgn := Sign(nu/du) eq -1 select [<-1,1>] else [];
  else
    sgn := [];
  end if;
  
  return sgn cat Factorisation(Numerator(nu/du)) cat num_f, Factorisation(Denominator(nu/du)) cat denom_f;
end function;

function PrettyMagma(x)
  F := Parent(x);
  assert Characteristic(F) eq 0;

  bracket := function(x);
    P := RingOfIntegers(Parent(x));
    if IsCoercible(Rationals(), x) then
      return Sprint(x);
    elif #[ e : e in Eltseq(P!x) | e ne 0] eq 1 then
      return Sprint(x);
    else
      return "(" cat Sprint(x) cat ")";
    end if;
  end function;

  if Type(F) eq FldAC then
    Fbase := BaseField(F);
    so, xx := IsCoercible(Fbase, x);
    if so then
      return PrettyMagma(xx);
    else
      Faff := AffineAlgebra(F);
      xx := Faff!x;
      coeffs := Coefficients(xx);
      mons := Monomials(xx);

      coeffs_str := [ PrettyMagma(c) : c in coeffs];
      return Join([ c cat "*" cat Sprint(mons[i]) : i-> c in coeffs_str], " + ");
    end if;
  end if;

  x_num, x_denom := Pretty(x);

  num_str := Join([ t[2] eq 1 select bracket(t[1]) else bracket(t[1]) cat "^" cat Sprint(t[2]) : t in x_num], "*");

  denom_str := Join([ t[2] eq 1 select bracket(t[1]) else bracket(t[1]) cat "^" cat Sprint(t[2]) : t in x_denom], "/");

  if #denom_str eq 0 then
    return num_str;
  else
    return num_str cat "/" cat denom_str;
  end if;
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
