/*

Some code to find idempotents

*/
QQ := Rationals();

function IdempotentIdeal(A)
  F := BaseRing(A);
  P := PolynomialRing(F, Dimension(A));
  
  AP := ChangeRing(A, P);
  x := &+[ P.i*AP.i : i in [1..Dimension(A)]];  // this is a general element in the algebra
  I := ideal< P | Eltseq(x^2-x)>;
  
  return I;
end function;

// base_ring must be ring of integers of the field
function IdealOfSingularPoints(A: base_ring := QQ)
  F := BaseRing(A);
  P := PolynomialRing(F, Dimension(A));
  PP := PolynomialRing(base_ring, Dimension(A)+ Rank(F));
  PF := PolynomialRing(base_ring, Rank(F));

  phiF := hom<F->PF | [PF.i : i in [1..Rank(F)]]>;
  phiP := hom<P->PP | [ PP.i : i in [1..Dimension(A)]]>;
  phiPF := hom<PF->PP | [ PP.(Dimension(A)+i) : i in [1..Rank(PF)]]>;

  AP := ChangeRing(A, P);
  x := &+[ P.i*AP.i : i in [1..Dimension(A)]];  // this is a general element in the algebra

  polys := [ ClearDenominators(f) : f in Eltseq(x^2-x)];

  polyPP := [ &+[ (Coefficients(f)[i]@phiF@phiPF)*(Monomials(f)[i]@phiP) : i in [1..#Monomials(f)]] : f in polys];
  I := ideal< PP | polyPP >;

  J := JacobianMatrix(polyPP);
  II := ideal< PP | polyPP cat Minors(J, Rank(J))>;
  
  return II, I;
end function;
  
function NilpotentIdeal(A)
  F := BaseRing(A);
  P := PolynomialRing(F, Dimension(A));
  
  AP := ChangeRing(A, P);
  x := &+[ P.i*AP.i : i in [1..Dimension(A)]];  // this is a general element in the algebra
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

function IdempotentIdealSubspace(A, U)
  F := BaseRing(A);
  P := PolynomialRing(F, Dimension(U));
  
  AP := ChangeRing(A, P);
  basU := [ A | v : v in Basis(U)];
  x := &+[ P.i*AP!Eltseq(basU[i]) : i in [1..Dimension(U)]];  // this is a general element in the algebra
  I := ideal< P | Eltseq(x^2-x)>;
  
  return I, basU;
end function;

function FindAllIdempotentsSubspace(A, U)
  I, basU := IdempotentIdealSubspace(A, U);
  
  if Dimension(I) ne 0 then
    print "ideal has dimension ", Dimension(I);
    return false;
  end if;
  
  var := Variety(I);
  n := Dimension(U);
  if #var ne VarietySizeOverAlgebraicClosure(I) then
    F := BaseRing(A);
    FCl := AlgebraicClosure(F);

    var := Variety(I, FCl);
    basU := [ ChangeRing(u, FCl) : u in basU];
    ACl := ChangeRing(A, FCl);
    idems := [ ACl!Eltseq( &+[t[i]*basU[i] : i in [1..n]]) : t in var];
  else
    idems := [ A!Eltseq([ t[i]*basU[i] : i in [1..n]]) : t in var];
  end if;
  
  return idems;
end function;


function FCl_Indicator(r)
  FCl := Parent(r);
  Aff := AffineAlgebra(FCl);
  F := BaseField(FCl);
  FF := FunctionField(F);
  
  mons := Monomials(Aff!r);
  
  rk := Rank(FCl);
  ind := [FCl | ];
  for i in [1..rk] do
    phi := hom<Aff -> FF | [ j eq i select FF.1 else FF!1 : j in [1..rk]]>;
    
    inds := [ FCl!(Aff.i) : m in mons | m@phi notin F]; // Numbering is different in Aff to FCl
    
    ind cat:= inds;
  end for;
  
  return Sort(IndexedSet(ind));
end function;



// Check characteristic polynomials
CheckForMatchingCharactisticPoly := function(x, LL);
  n := Degree(x);
  char_x := CharacteristicPolynomial(AdjointMatrix(x)); // Seems to be a bug in Char poly??
  assert Coefficient(char_x, n) eq 1;
  
  if not Universe(LL) cmpeq Parent(x) then
    // we have been passed a set of orbits
    assert Universe(LL[1]) cmpeq Parent(x);
    L := [ o[1] : o in LL | x notin o and 0 notin o];
  else
    L := [ y : y in LL | y ne x and y ne 0];
  end if;
  
  // First we quickly rule out some options
  // The 1-eigenspace must be 1-dimensional
  L := [ l : l in L | Dimension(Eigenspace(l, 1)) eq 1];
  
  // Finding eigenvalues seems expensive, otherwise I would test to see if there were three or less
  
  char_L := [ CharacteristicPolynomial(AdjointMatrix(y)) : y in L];
  assert forall{ p : p in char_L | Coefficient(p, n) eq 1};
  
  FCl := BaseRing(Parent(x));
  if Type(FCl) eq FldAC then
    F := BaseRing(FCl);
  else
    F := FCl;
  end if;
  P := RingOfIntegers(F);  // This should now be a polynomial ring over the integers, ie Z[al], or Z[al,bt] etc
  if Characteristic(P) eq 0 and not P cmpeq Integers() then
    assert BaseRing(P) eq Integers();
  end if;

  // to be able to define ideals, we need a RngMPol not a RngUPol
  if Type(P) notin { RngUPol, RngMPol} then
    PM := P;
    hom_P_PM := hom<P->P | >;  // identity map
  elif Type(P) eq RngUPol and Rank(P) eq 1 then
    PM<t> := PolynomialRing(BaseRing(P), 1);
    hom_P_PM := hom<P -> PM | PM.1>;
  else
    PM := P;
    hom_P_PM := hom<P -> PM | [ PM.i : i in [1..Rank(PM)]]>;
  end if;

  
  fail := [**];
  for i-> py in char_L do
    print i;
    p := py - char_x;
    
    if p eq 0 then
      // we have found another class of axis!
      Append(~fail, <L[i], py, 0>);
      print "  Found new orbit of Monster axis.";
      continue; // go to the next idempotent
    end if;
    
    coeffs := [ q : q in Coefficients(p) | q ne 0];
    so, cond := CanChangeUniverse(coeffs, F);
    if so then
      // We need to clear denominators
      ds := LCM([ Denominator(q) : q in cond]);
      
      cond := [ P!(ds*cond[i]) : i in [1..#cond]]@hom_P_PM;
      
      if Type(PM) cmpeq RngMPol then
        cond := GroebnerBasis(cond);
      end if;
      
      I := ideal<PM | cond>;
      
      if I eq PM then
        // there are no values of al, or bt, or characteristics where the idempotent has the same spectrum as x
        continue;
      elif Type(PM) eq RngMPol and exists{ r : r in Basis(I) | #Terms(r) eq 1 and Terms(r) eq Monomials(r)} then
        // one of the generators for the ideal is just a power of t, but al and bt cannot be 0
        continue;
      else
        print "  Fail.  Need to check.  Ideal is", I;
        Append(~fail, <L[i], py, I>);
      end if;
    else
      // check the number of eigenvalues
      eigs := Eigenvalues(L[i]);
      if &+[ e[2] : e in eigs] eq n and #eigs le 3 then // we have all the eigenvalues and there are less than 4
        assert #Eigenvalues(x) eq 4;
        continue;
      end if;
      
      // Find the elements of FCl involved
      supp := &join[ FCl_Indicator(c) : c in coeffs];
      
      // Clear denominators
      Aff := AffineAlgebra(FCl);
      coeffs_aff := ChangeUniverse(coeffs, Aff);
      denoms := [ Denominator(t) : t in Coefficients(c), c in coeffs_aff];
      ds := LCM(denoms);
      coeffs_aff := [ ds*c : c in coeffs_aff];
      
      
      rk := #supp + Rank(F);
      PP := PolynomialRing(BaseRing(P), rk);
      
      // This is a little dangerous as we are mapping a field to a polynomial ring over a ring
      map_F_PP := hom<F-> PP | [ PP.(rk-Rank(F)+i) : i in [1..Rank(F)]]>;
      map_Aff_PP := hom<Aff->PP | map_F_PP, 
      [ Aff.i in supp select PP.Position(supp, Aff.i) else PP!0 : i in [1..Rank(Aff)]]>; // Need more generators!!
      
      gens := coeffs_aff@map_Aff_PP;
      
      // now add the minimal polynomials
      for pos-> r in supp do
        min := MinimalPolynomial(r);
        ds := LCM([ Denominator(c) : c in Coefficients(min)]);
        min := ds*min;
        map_Ft_PP := hom<Parent(min)-> PP | map_F_PP, PP.pos>;
        Append(~gens, min@map_Ft_PP);
      end for;
      
      // We can divide by 2
      function Reduce2(r)
        cont := Content(r);
        fact := Factorisation(r);
        
        so := exists(e){ t[2] : t in fact | t[1] eq 2};
        
        if not so then
          return r;
        end if;
        rr, rem := Quotrem(r, 2^e);
        assert rem eq 0;
        return rr;
      end function;
      
      gens := [Reduce2(r) : r in gens];
      while not IsGroebner(gens) do
        gens := GroebnerBasis(gens);
        gens := [Reduce2(r) : r in gens];
      end while;

      I := ideal<PP | gens>;

      if I eq Generic(I) then
        // there are no values of al, or bt, or characteristics where the idempotent has the same spectrum as x
        continue;
      else
        print "  Fail.  Algebraic Extension.  Groebner basis is", Basis(I);
        Append(~fail, <L[i], py, [*<r, r@map_Aff_PP> : r in supp*] cat [* <F.i, F.i@map_Aff_PP> : i in [1..Rank(F)] *], I>);
      end if;    
    end if;
  end for;
  
  return fail;
end function;

// Given an ideal I and a polynomial poly which is not allowed,
// reduce the generators of I by dividing by poly if possible.
ReduceIdeal := function(I, poly)
  P := Generic(I);
  bas := Basis(I);
  for i->r in bas do
    r_new := r;
    repeat
      r_old := r_new;
      so, r_new := IsDivisibleBy(r_old, poly);
    until not so;
    bas[i] := r_old;
  end for;
  
  bas := GroebnerBasis(bas);
  return ideal<P|bas>;
end function;








// Given an idempotent x and a sequence of orbits of idempotents orbs,
// find those in L which have the same characteristic polynomial as x over Z
// returns any possibilities with the characteristic poly in variables which needs to be satisfied

FindMatchingIdempotents := function(x, orbs)
  n := Degree(x);
  char_x := CharacteristicPolynomial(AdjointMatrix(x)); // Seems to be a bug in Char poly??
  assert Coefficient(char_x, n) eq 1;
  
  L := [ o[1] : o in orbs | x notin o ];
  
  char_L := [ CharacteristicPolynomial(AdjointMatrix(y)) : y in L];
  assert forall{ p : p in char_L | Coefficient(p, n) eq 1};

  FCl := BaseRing(Parent(x));
  if Type(FCl) eq FldAC then
    F := BaseRing(FCl);
  else
    F := FCl;
  end if;
  P := RingOfIntegers(F);  // This should now be a polynomial ring over the integers Z[t]
  // assert BaseRing(P) eq Integers();

  fail := [**];
  for i-> py in char_L do
    print i;
    p := py - char_x;
    
    if p eq 0 then
      // we have found another class of axis!
      Append(~fail, <L[i], py, 0>);
      print "  Found new orbit of Monster axis.";
    end if;
    
    coeffs := [ q : q in Coefficients(p) | q ne 0];
    so, cond := CanChangeUniverse(coeffs, F);
    
    if so then
      ds := LCM([ Denominator(q) : q in cond]);
      
      cond := [ P!(ds*cond[i]) : i in [1..#cond]];
      gcd := GCD(cond);

      if gcd eq 1 or (Parent(gcd) cmpeq QQ and gcd mod 2 eq 0) then
        // either gcd is 1 or a power of two, which is invertible
        print "gcd is ", gcd;
      else
        print "  Fail.  gcd is ", gcd;
        Append(~fail, <L[i], py, gcd>);
      end if;
    else
      // the coefficients of p involve elements in the algebraically closed field
      Aff := AffineAlgebra(FCl);
      V, phi := VectorSpace(Aff);
      
      coeffs := ChangeUniverse(coeffs, Aff);
      if forall{ q : q in coeffs | IsUnivariate(q)} then
        // check they are the same variable
        assert exists(q){ q : q in coeffs | #Monomials(q) ne 1};
        var := Monomials(q)[1];
        deg := Degree(MinimalPolynomial(var));
        
        if forall{ q : q in coeffs | Set(Monomials(q)) subset {Aff!1} join { var^i : i in [1..deg-1]}} then      
          coeffs := [ UnivariatePolynomial(q) : q in coeffs];
          // clear each of the denominators
          denom := LCM(Flat([[Denominator(e) : e in Eltseq(q)] : q in coeffs]));
          coeffs := [ denom*q : q in coeffs];
          
          // change ring to be over the polynomial ring          
          Ft := Universe(coeffs);
          assert F eq BaseRing(Ft);
          assert P eq RingOfIntegers(F);
          
          Pt := PolynomialRing(P, 1);
          coeffs := ChangeUniverse(coeffs, Pt);
          
          gcd := GCD(coeffs);
          if gcd eq 1 or (Parent(gcd) cmpeq QQ and gcd mod 2 eq 0) then
            // either gcd is 1 or a power of two, which is invertible
            print "gcd is ", gcd;
          else
            print "  Fail.  gcd is ", gcd;
            Append(~fail, <L[i], py, gcd>);
          end if;
        else
          Append(~fail, <L[i], py, "multivariate">);
        end if;
      else
        // multivariate - need to be more careful
        // do by hand???
        Append(~fail, <L[i], py, "multivariate">);
      end if;    
    end if;
  end for;

  return fail;
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

// ==================================================================
//
//     Function to return a fraction in a field with the numerator and denominator factorised
//
// ==================================================================

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

// ======================================================================================
//
//     Function to print out field elements in Magma code in fully factorised fractions
//
// ======================================================================================

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

  if x_num eq [] then
    num_str := "1";
  else
    num_str := Join([ t[2] eq 1 select bracket(t[1]) else bracket(t[1]) cat "^" cat Sprint(t[2]) : t in x_num], "*");
  end if;

  denom_str := Join([ t[2] eq 1 select bracket(t[1]) else bracket(t[1]) cat "^" cat Sprint(t[2]) : t in x_denom], "/");

  if #denom_str eq 0 then
    return num_str;
  else
    return num_str cat "/" cat denom_str;
  end if;
end function;

// ==================================================================
//
//     Functions to print out field elements nicely in LaTeX form
//
// ==================================================================
// helper function
function LaTeX(y)
  FF := Parent(y);
  names := Names(FF);
  names_str := [ "\\" cat name : name in names];
  
  y_str := Sprint(y);
  for i->name in names do
    y_str := Join(Split(y_str, name), names_str[i]);
  end for;
  
  y_str := Join(Split(y_str, "*"), " ");

  return y_str;
end function;


// Function to print out a field element in LaTeX code
function LaTeXprint(x)
  F := Parent(x);
  assert Characteristic(F) eq 0;
  // First check if it involves a algebraically closed field
  
  if Type(F) eq FldAC then
    Fbase := BaseField(F);
    so, xx := IsCoercible(Fbase, x);
    if so then
      return LaTeXprint(xx);
    else
      Faff := AffineAlgebra(F);
      xx := Faff!x;
      coeffs := Coefficients(xx);
      mons := Monomials(xx);
      mons_var := [ m eq 1 select "" else "\\" cat Sprint(m) : m in mons];

      coeffs_str := [ LaTeXprint(c) : c in coeffs];
      return Join([ "(" cat c cat ") " cat mons_var[i] : i-> c in coeffs_str], " + ");
    end if;
  end if;
  
  // If it is in a function field, split into numerator and denominator
  x_num, x_denom := Pretty(x);
  
  bracket := function(y);
    P := RingOfIntegers(Parent(y));
    if IsCoercible(Rationals(), y) then
      return Sprint(y);
    elif #[ e : e in Eltseq(P!y) | e ne 0] eq 1 then
      return Sprint(y);
    else
      return "(" cat LaTeX(y) cat ")";
    end if;
  end function;
  
  if x_num eq [] then
    num_str := "1";
  else
    num_str := Join([ t[2] eq 1 select bracket(t[1]) else bracket(t[1]) cat "^" cat Sprint(t[2]) : t in x_num], " ");
  end if;

  denom_str := Join([ t[2] eq 1 select bracket(t[1]) else bracket(t[1]) cat "^" cat Sprint(t[2]) : t in x_denom], " ");
  
  if #denom_str eq 0 then
    return num_str;
  else
    return "\\frac{" cat num_str cat "}{" cat denom_str cat "}";
  end if;
end function;

