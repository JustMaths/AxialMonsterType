// --------------------------------------------
//
//          Split spin factor algebras
//
// --------------------------------------------
intrinsic SplitSpinFactor(b::Mtrx) -> AlgGen, AlgMatElt
  {
  Returns the split spin factor algebra S(b, al) defined over a function field with variable al and its Frobenius form.
  }
  require NumberOfRows(b) eq NumberOfColumns(b): "The matrix given must be square";

  F<al> := FunctionField(FieldOfFractions(BaseRing(b)));
  
  dim := NumberOfRows(b)+2;
  V := VectorSpace(F, dim);
  
  function multfn(x, y, Bil)
    xe := Vector(Eltseq(x)[[1..dim-2]]);
    xz1 := x[dim-1];
    xz2 := x[dim];
    
    ye := Vector(Eltseq(y)[[1..dim-2]]);
    yz1 := y[dim-1];
    yz2 := y[dim];

    z := al*(al-2)*V.(dim-1) + (al^2-1)*V.dim;
    prod := -InnerProduct(xe*Bil,ye)*z + (al*yz1+(1-al)*yz2)*Vector(Eltseq(xe) cat [0,0])
        + (al*xz1+(1-al)*xz2)*Vector(Eltseq(ye) cat [0,0])
        + xz1*yz1*V.(dim-1) + xz2*yz2*V.dim;
    
    return prod;
  end function;

  mult := [[ multfn(V.i, V.j, ChangeRing(b, F)) : i in [1..dim]]: j in [1..dim]];

  A := Algebra<F, dim | mult>;
  
  frob := DiagonalJoin((al+1)*(2-al)*ChangeRing(b, F), Matrix(F, [[al+1, 0],[0,2-al]]));

  return A, frob;
end intrinsic;

intrinsic SplitSpinFactor(b::Mtrx, al::RngElt) -> AlgGen, AlgMatElt
  {
  Returns the split spin factor algebra S(b, al) and its Frobenius form.
  }
  // Need to fix to take covering ring of al and b
  F := FieldOfFractions(Parent(al));
  require Characteristic(F) ne 2: "The characteristic of the field cannot be 2.";
  // Should check that the field for b and F are compatible.
  require F!al notin { F | 1,0, 1/2}: "The value of eta cannot be 1, 0, or 1/2.";

  A, frob := SplitSpinFactor(b);
  
  FF<x> := BaseRing(A);
  phi := hom<FF->F | [al]>;

  return ChangeRing(A, F, phi), ChangeRing(frob, F, phi);
end intrinsic;

intrinsic SplitSpinFactorCover(b::Mtrx) -> AlgGen, AlgMatElt
  {
  Returns the cover of the exceptional split spin factor \\widehat\{S\}(b, -1)^\\circ and its Frobenius form.
  }
  require NumberOfRows(b) eq NumberOfColumns(b): "The matrix given must be square";
  
  dim := NumberOfRows(b)+2;
  F := FieldOfFractions(BaseRing(b));
  V := VectorSpace(F, dim);
  
  function multfn(x, y, Bil)
    xe := Vector(Eltseq(x)[[1..dim-2]]);
    xz1 := x[dim-1];
    
    ye := Vector(Eltseq(y)[[1..dim-2]]);
    yz1 := y[dim-1];

    z := 3*V.(dim-1) -2*V.dim;
    prod := -InnerProduct(xe*Bil,ye)*z - yz1*Vector(Eltseq(xe) cat [0,0])
        -xz1*Vector(Eltseq(ye) cat [0,0])
        + xz1*yz1*V.(dim-1);
    
    return prod;
  end function;

  mult := [[ multfn(V.i, V.j, b) : i in [1..dim]]: j in [1..dim]];

  A := Algebra<F, dim | mult>;
  
  frob := DiagonalJoin(3*ChangeRing(b, F), Matrix(F, [[1, 0],[0,0]]));

  return A, frob;
end intrinsic;
