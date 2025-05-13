/*

Yabe's algebras in his own basis

*/
import "Utilities_for_algebra_creation.m": ZZ, QQ, MakeSymmetric;
Attach("Utilities_for_algebra_creation.m");
// NB We use al, bt for the eigenvalues

// --------------------------
//
// The III algebra
//
// --------------------------
// NB we use dl for his al
intrinsic III(:base_ring:=QQ, specialise:=false) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's III(al, bt, dl) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base field. Optional parameter specialise can be set to 3A or IY3 to set field and parameters for those algebras.  Defaults to false.
  
  NB this gives the 3A(al, bt) and IY_3(al, 1/2, dl) algebras in the notation of McInroy and Shpectorov.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  
  if Type(specialise) eq BoolElt then
    require specialise eq false: "The optional parameter must be either false, 3A, or IY3";
  else
    require Type(specialise) eq MonStgElt and specialise in {"3A", "IY3"}: "The optional parameter must be either false, 3A, or IY3";
  end if;
  
  if Type(specialise) eq BoolElt then
    F<al, bt, dl> := FunctionField(base_ring, 3);
    
    pi_fact := (al+1)*(al-bt)*dl +(3*al^2+3*al*bt-bt-1);
    pi := -al*pi_fact/(4*(2*al-1));

    mult := [[[1,0,0,0], [(al-bt)*(dl+1)/2+bt, (al-bt)/2+bt, (al-bt)/2, 1], [(al-bt)*(dl+1)/2+bt, (al-bt)/2, (al-bt)/2+bt, 1], [pi, 0,0,0]],
             [[(al-bt)*(dl+1)/2+bt, (al-bt)/2+bt, (al-bt)/2, 1], [0,1,0,0], [(1-dl)*(al-bt)*(dl+1)/2, (1-dl)*(al-bt)/2+bt, (1-dl)*(al-bt)/2+bt, (1-dl)], [0, pi, 0,0]],
             [[(al-bt)*(dl+1)/2+bt, (al-bt)/2, (al-bt)/2+bt, 1], [(1-dl)*(al-bt)*(dl+1)/2, (1-dl)*(al-bt)/2+bt, (1-dl)*(al-bt)/2+bt, (1-dl)], [0,0,1,0], [0,0,pi, 0]],
             [[pi, 0,0,0], [0, pi, 0,0], [0,0,pi, 0], [0,0,0,pi]]];
    
    proj1 := pi/al +1/4*((al-bt)*dl +3*(al+bt) +1);

    proj2 := (-1/8*al^3*bt*dl^2 - 1/4*al^3*bt*dl + 3/8*al^3*bt + 1/8*al^3*dl^2 + 
            1/4*al^3*dl - 3/8*al^3 + 1/8*al^2*bt^2*dl^2 - 1/2*al^2*bt^2*dl + 
            3/8*al^2*bt^2 - 3/4*al^2*bt*dl^2 + 5/8*al^2*bt*dl - 7/8*al^2*bt + 
            1/8*al^2*dl^2 - 5/8*al^2*dl + 1/2*al^2 + 5/8*al*bt^2*dl^2 - 5/8*al*bt^2 
            + 1/8*al*bt*dl^2 + 5/8*al*bt*dl + 3/4*al*bt + 1/8*al*dl - 1/8*al - 
            1/4*bt^2*dl^2 + 1/4*bt^2 - 1/4*bt*dl - 1/4*bt)/(al^2*bt - al^2 - 
            3/2*al*bt + 3/2*al + 1/2*bt - 1/2);
            
    frob := Matrix([[1, proj1, proj1, pi], [proj1, 1, proj2, pi], [proj1, proj2, 1, pi], [pi, pi, pi, pi*(pi/al -((al-bt)*(dl+3)+2*bt-1)/4)]]);
    
    A := Algebra<F,4 | mult>;
    
    return A, {@ A.1, A.2 @}, frob;
    
  elif specialise eq "3A" then
    A, gen, frob := III(:base_ring:=base_ring);
    
    FF<x,y,z> := BaseRing(A);
    
    F<al, bt> := FunctionField(base_ring, 2);
    phi := hom<FF->F | [al, bt, 0]>;
  
    A := ChangeRing(A, F, phi);
    
    return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
  elif specialise eq "IY3" then
    A, gen, frob := III(:base_ring:=base_ring);
    
    FF<x,y,z> := BaseRing(A);
    
    F<al, dl> := FunctionField(base_ring, 2);
    phi := hom<FF->F | [al, 1/2, dl]>;
  
    A := ChangeRing(A, F, phi);
    
    return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
  end if;
end intrinsic;
// --------------------------
//
// The IV_1 algebra
//
// --------------------------
intrinsic IV1(:base_ring:=QQ, specialise:=false) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's IV_1(al, bt) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base field.  Optional parameter specialise can be set to 4A or 4J to set field and parameters for those algebras.  Defaults to false.
  
  NB this gives the 4A(1/4, bt) and 4J(2bt, bt) algebras in the notation of McInroy and Shpectorov.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  
  if Type(specialise) eq BoolElt then
    require specialise eq false: "The optional parameter must be either false, 4A, or 4J";
  else
    require Type(specialise) eq MonStgElt and specialise in {"4A", "4J"}: "The optional parameter must be either false, 4A, or 4J";
  end if;
  
  if Type(specialise) eq BoolElt then
    F<al, bt> := FunctionField(base_ring, 2);
    
    G := sub<Sym(5) | (2,4), (1,3), (1,2)(3,4)>;
    
    V := VectorSpace(F, 5);
    S := [<1,1,V.1>, <1,2,(al-bt)/2*(V.1+V.2+V.3+V.4) + bt*(V.1+V.2) + V.5>,
          <1,3,V!0>, <1,5,(-2*al*bt-al+bt)/2*V.1>, <5,5,(-2*al*bt-al+bt)/2*V.5>];
    
    mult := BuildSymmetricMultiplication(S, G);
    A := Algebra<F, 5 | mult>;
    
    T := [ <1,1,F!1>, <1,2,bt>, <1,3,F!0>, <1,5,(-2*al*bt-al+bt)/2>, <5,5,(bt-2*al)*(-2*al*bt-al+bt)/2>];
    frob := BuildSymmetricBilinearForm(T, G);
    
    return A, {@ A.1, A.2 @}, frob;
  elif specialise eq "4A" then
    require Characteristic(base_ring) ne 3: "The IV1(1/4,bt) algebra (aka 4A) does not exist over a field of characteristic 3.";
    A, gen, frob := IV1(:base_ring:=base_ring);
    
    FF<x,y> := BaseRing(A);
    
    F<bt> := FunctionField(base_ring);
    phi := hom<FF->F | [1/4, bt]>;
  
    A := ChangeRing(A, F, phi);
    
    return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
  elif specialise eq "4J" then
    A, gen, frob := IV1(:base_ring:=base_ring);
    
    FF<x,y> := BaseRing(A);
    
    F<al> := FunctionField(base_ring);
    phi := hom<FF->F | [al, al/2]>;
  
    A := ChangeRing(A, F, phi);
    
    return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
  end if;
end intrinsic;
// --------------------------
//
// The IV_2 algebra
//
// --------------------------
intrinsic IV2(:base_ring:=QQ, specialise:=false) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's IV_2(al, bt, mu) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base field.  Optional parameter specialise can be set to 4B, 4Y_bt or 4Y_al to set field and parameters for those algebras.  Defaults to false.
  
  NB this gives the 4B(al, al^2/2), 4Y(1/2, bt) and 4Y(al, (1-al^2)/2) algebras in the notation of McInroy and Shpectorov.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  
  if Type(specialise) eq BoolElt then
    require specialise eq false: "The optional parameter must be either false, 4B, 4Y_al, or 4Y_bt";
  else
    require Type(specialise) eq MonStgElt and specialise in {"4B", "4Y_al", "4Y_bt"}: "The optional parameter must be either false, 4B, 4Y_al, or 4Y_bt";
  end if;
  
  if Type(specialise) eq BoolElt then
    F<al, bt, mu> := FunctionField(base_ring, 3);
    
    G := sub<Sym(5) | (2,4), (1,3), (1,2)(3,4)>;
    
    V := VectorSpace(F, 5);
    S := [<1,1,V.1>, <1,2,bt*(V.1+V.2) + V.5>,
          <1,3,bt*(V.1+V.3) -mu*(2*V.5 + bt*(V.2+V.4)) - bt*(V.1+V.3)>,
          <1,5, (al-bt)/2*(2*V.5 + bt*(V.2+V.4)) + (-mu*bt^2 + bt*(2*al-2*bt-1)/2)*V.1>,
          <5,5,(2*bt^2 - al*bt -bt/2 +(al-2*al^2)/2/mu)*V.5
               + (bt^3*mu/2 + bt^3 -al*bt^2/2 +(al*bt-2*al^2*bt)/4/mu)*V![1,1,1,1,0]>];
    
    mult := BuildSymmetricMultiplication(S, G);
    A := Algebra<F, 5 | mult>;
    
    lm := (-al*bt - bt^3*mu + bt^2*mu + 1/2*bt^2 + 1/2*bt)/(al - 1);
    lmzz := -bt*(al-bt*mu-1/2)*(al*bt*mu - 1/2*al - bt^2*mu^2 - bt^2*mu - 1/2*bt*mu + 1/2*bt)/(al*mu - mu);
    T := [ <1,1,F!1>, <1,2,(bt^2*mu -bt/2)/(al-1)>,
           <1,3,(2*al*bt*mu - 2*bt^2*mu^2 - bt*mu)/(al - 1)>,
           <1,5,lm>,
           <5,5,-bt*lm + lmzz>];
    frob := BuildSymmetricBilinearForm(T, G);
    
    return A, {@ A.1, A.2 @}, frob;
  elif specialise eq "4B" then
    A, gen, frob := IV2(:base_ring:=base_ring);
    
    FF<x,y,mu> := BaseRing(A);
    
    F<al> := FunctionField(base_ring);
    phi := hom<FF->F | [al, al^2/2, 1/al]>;
  
    A := ChangeRing(A, F, phi);
    
    return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
  elif specialise eq "4Y_bt" then
    A, gen, frob := IV2(:base_ring:=base_ring);
    
    FF<x,y> := BaseRing(A);
    
    F<bt> := FunctionField(base_ring);
    phi := hom<FF->F | [1/2, bt, (1-4*bt)/2/bt]>;
  
    A := ChangeRing(A, F, phi);
    
    return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
  elif specialise eq "4Y_al" then
    A, gen, frob := IV2(:base_ring:=base_ring);
    
    FF<x,y> := BaseRing(A);
    
    F<al> := FunctionField(base_ring);
    phi := hom<FF->F | [al, (1-al^2)/2, -1/(al+1)]>;
  
    A := ChangeRing(A, F, phi);
    
    return A, {@ A.1, A.2 @}, ChangeRing(frob, F, phi);
  end if;
  
end intrinsic;
// --------------------------
//
// The IV_3 algebra
//
// --------------------------
intrinsic IV3(:base_ring:=QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's IV_3(1/2,2) algebra, with generators and its Frobenius form.  Optional paramenter base_ring of the base field.
  
  NB this is the 6Y(1/2, 2) algebra in the notation of McInroy and Shpectorov.
  }
  mult := [[[1,0,0,0,0], [1,1,-1/2,-1/2,1], [1,-1,0,1,0], [1,-1,-1/2,3/2,1], [0,0,0,0,0]],
           [[1,1,-1/2,-1/2,1], [0,1,0,0,0], [-1,1,3/2,-1/2,1], [-1,1,1,0,0], [0,0,0,0,0]],
           [[1,-1,0,1,0], [-1,1,3/2,-1/2,1], [0,0,1,0,0], [0,0,1/2,1/2,1], [0,0,0,0,0]],
           [[1,-1,-1/2,3/2,1],[-1,1,1,0,0], [0,0,1/2,1/2,1], [0,0,0,1,0], [0,0,0,0,0]],
           [[0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0], [0,0,0,0,0]]];

  A := Algebra<QQ,5 | mult>;
  frob := Matrix(QQ, [[1,1,1,1,0] : i in [1..4]] cat [[0,0,0,0,0]]);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;
// --------------------------
//
// The V_1 algebra
//
// --------------------------
intrinsic V1(:base_ring:=QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's V_1(al, (5al-1)/8) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base field.
  
  NB this is the 5A(al, (5al-1)/8) algebra in the notation of McInroy and Shpectorov.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_ring);
  bt := (5*al-1)/8;
  
  G := Sym(6)!!DihedralGroup(5);
  
  V := VectorSpace(F,6);
  S := [<1,1,Eltseq(V.1)>, <1,2,Eltseq(bt*(V.1+V.2)+V.6)>, <1,3,Eltseq(-bt/2*(&+[V.i : i in [1..5]]) + bt*(V.1+V.3)-V.6)>, <1,6,Eltseq(-(al-bt)*bt*V.1 + (al-bt)*bt/2*(V.2+V.5) +(al-bt)*V.6)>, <6,6,Eltseq(-(7*al-3)*(al-bt)*bt/2^5*(&+[V.i : i in [1..5]]) -5*(al-bt)*bt/2*V.6)>];
  
  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 6 | mult>;
  
  T := [ <1,1,F!1>, <1,2,3/4*bt>, <1,3,3/4*bt>, <1,6,-5/4*bt*(al-bt)>, <6,6, 5/2^6*bt*(11*al+1)*(al-bt)>];
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;
// --------------------------
//
// The V_2 algebra
//
// --------------------------
intrinsic V2(:base_ring:=QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's V2(al, 1/2) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base field.
  
  NB this is the IY_5(al, 1/2) algebra in the notation of McInroy and Shpectorov.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_ring);
  bt := 1/2;
  
  pi := (2*al-1)*(2*al-3)/32;
  
  V := VectorSpace(F,6);
  mult := [[V![1,0,0,0,0,0]],
           [V![bt, bt, 0, 0, 0, 1], V![0,1,0,0,0,0]],
           [V![1/4, 1, -1, 1, -1/4 , 4], V![0, bt, bt, 0, 0, 1], V![0,0,1,0,0,0]],
           [V![-1, 6, -9, 13/2, -3/2, 9 ], V![-1/4, 1+bt, -6/4, 1+bt, -1/4 , 4], V![0, 0, bt, bt, 0, 1], V![0,0,0,1,0,0]],
           [V![3-15/2, -5+25, 5-35, -5/2+45/2, 1/2-5, 1+15], V![ -3/2, 13/2, -9, 6, -1, 9 ], V![-1/4, 1, -6/4+bt, 1, -1/4+bt , 4], V![0, 0, 0, bt, bt, 1], V![0,0,0,0,1,0]],
           [ V![3*(2*al-1)/8, -9*(2*al-1)/8, 10*(2*al-1)/8, -5*(2*al-1)/8, (2*al-1)/8, (2*al-1)/2],
             V![(2*al-1)/8, -2*(2*al-1)/8, (2*al-1)/8, 0, 0, (2*al-1)/2], 
             V![0, (2*al-1)/8, -2*(2*al-1)/8, (2*al-1)/8, 0, (2*al-1)/2], 
             V![0, 0, (2*al-1)/8, -2*(2*al-1)/8, (2*al-1)/8, (2*al-1)/2],
             V![(2*al-1)/8, -5*(2*al-1)/8, 10*(2*al-1)/8, -9*(2*al-1)/8, 3*(2*al-1)/8, (2*al-1)/2],
             V![ pi, -4*pi, 6*pi, -4*pi, pi, 0]]];

  for i in [1..#mult] do
    for j in [1..i-1] do
      mult[j,i] := mult[i,j];
    end for;
  end for;
  
  A := Algebra<F,6|mult>;
  
  frob := Matrix(F, [[1,1,1,1,1,0] : i in [1..5]] cat [[0,0,0,0,0,0]]);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;
// --------------------------
//
// The VI_1 algebra
//
// --------------------------
// NB basis order is a_0, a_1, a_2, a_3, a_-2, a_-1, p_1, q
intrinsic VI1(:base_ring:=QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's VI_1(al, al/2) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base field.
  
  NB basis order is a_0, a_1, a_2, a_3, a_-2, a_-1, p_1, q.  
  NB this is the 6J(2bt, bt) algebra in the notation of McInroy and Shpectorov.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_ring);
  bt := al/2;
  
  G := sub<Sym(8) | (3,5)(2,6), (1,5)(2,4), (1,4)(2,5)(3,6)>;
  
  V := VectorSpace(F,8);
  S := [<1,1,Eltseq(V.1)>, <1,2,Eltseq(bt*(V.1+V.2)+V.7)>, <1,3,Eltseq(bt/2*(V.1+V.3-V.5))>,
        <1,4,Eltseq(bt*&+[V.i : i in [1..6]] +bt*(V.1+V.4) -2*V.7+V.8)>,
        <1,7,Eltseq(bt^2/2*(-2*V.1+V.2+V.6) +bt*V.7)>, <1,8,Eltseq((-7*bt^2-bt)*V.1)>,  
        <7,7, Eltseq(bt^3/4*&+[V.i : i in [1..6]] -bt*(bt+1/2)*V.7 + bt^2/4*V.8)>,
        <7,8, Eltseq((-7*bt^2-bt)*V.7)>, <8,8, Eltseq((-7*bt^2-bt)*V.8)>];

  mult := BuildSymmetricMultiplication(S, G);
  A := Algebra<F, 8 | mult>;
  
  T := [ <1,1,F!1>, <1,2,bt>, <1,3,bt/2>, <1,4,bt>, <1,7,-bt^2>,
         <1,8,-7*bt^2-bt>, <7,7,1/4*(bt^3+2*bt^2)>, <7,8,7*bt^3+bt^2>, <8,8, 9*(7*bt^3+bt^2)>];
                
  frob := BuildSymmetricBilinearForm(T, G);
  
  return A, {@ A.1, A.2@};
end intrinsic;

// --------------------------
//
// The VI_2 algebra
//
// --------------------------
intrinsic VI2(:base_ring:=QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's VI_2(al, -al^2/(2(2al-1))) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base field.
  
  NB this is the 6A(al, -al^2/(2(2al-1))) algebra in the notation of McInroy and Shpectorov.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  F<al> := FunctionField(base_ring);
  bt := -al^2/(4*(2*al-1));
  
  Add := function(S,T);
    return Eltseq(Vector(F, S)+Vector(F, T));
  end function;

  r_2 := [(21*al^2-18*al+4)/(8*(2*al-1)), (3*al-2)*(5*al-2)/(8*(2*al-1)), (21*al^2-18*al+4)/(8*(2*al-1)), (3*al-2)*(5*al-2)/(8*(2*al-1)), (21*al^2-18*al+4)/(8*(2*al-1)), (3*al-2)*(5*al-2)/(8*(2*al-1)), -(3*al-2)*(5*al-2)^2/(al^2*(9*al-4)), 1];

  r_2i := function(i)
    if IsEven(i) then
      return r_2;
    else
      return r_2[[2,3,4,5,6,1,7,8]];
    end if;
  end function;

  ord := [5,6,1,2,3,4];
  trans := map< Integers() -> [1..6] | i:-> (i mod 6)+1, j:-> ord[j]>;

  r_3i := function(i)
    v := Vector(F, [0,0,0,0,0,0,4*(2*al-1)/al, 0]);
    V := Parent(v);
    v +:= -al/2*(V.trans(i+1) + V.trans(i-1))
          -4*(2*al-1)/(5*al-2)*Vector(r_2i(i))
          + al^2/(2*(5*al-2))*(V.trans(i+2)+V.trans(i-2))
          + al^2/(4*(2*al-1))*V.trans(i+3)
          + al*(29*al^2-22*al+4)/(4*(2*al-1)*(5*al-2))*V.trans(i);
    return Eltseq(v);
  end function;

  perm := (Sym(8)!(1,2,3,4,5,6))^-1;

  row1 := [[1,0,0,0,0,0,0,0], [bt,bt,0,0,0,0,1,0], Add(r_2i(0),[bt,0,bt,0,0,0,0,0]), Add(r_3i(0),[bt,0,0,bt,0,0,0,0]), Add(r_2i(0),[bt,0,0,0,bt,0,0,0]), [bt,0,0,0,0,bt,1,0], [-al^2*(3*al-2)*(1-al)/(16*(2*al-1)^2) +bt*(al-bt-1), bt*(al-bt)/2,0,0,0, bt*(al-bt)/2, al-bt, 0], [-(3*al-2)*(5*al-2)*(12*al^2-al-2)/(8*(2*al-1)*(9*al-4)),0,0,0,0,0,0,0]];

  row := function(i)
    return PermuteSequence([ PermuteSequence(r, perm^(i-1)) : r in row1], perm^(i-1));
  end function;


  mult := [ row(i) : i in [1..6]] cat
          [ [row(i)[7] : i in [1..6]] cat [Add(Eltseq(-al^4*(9*al-4)/(32*(2*al-1)^2*(5*al-2))*Vector(r_2i(0))), [-al^4*(3*al-1)*(9*al-4)/(64*(2*al-1)^2*(5*al-2)), -al^4*(3*al-1)*(9*al-4)/(128*(2*al-1)^3), -al^4*(3*al-1)*(9*al-4)/(64*(2*al-1)^2*(5*al-2)), -al^4*(3*al-1)*(9*al-4)/(128*(2*al-1)^3), -al^4*(3*al-1)*(9*al-4)/(64*(2*al-1)^2*(5*al-2)), -al^4*(3*al-1)*(9*al-4)/(128*(2*al-1)^3), al^2*(39*al^2-22*al+2)/(16*(2*al-1)^2), 0]), [0,0,0,0,0,0,-(3*al-2)*(5*al-2)*(12*al^2-al-2)/(8*(2*al-1)*(9*al-4)),0]], [ PermuteSequence(row1[8], (Sym(8)!(1,8,7,6,5,4,3,2))^(i-1)) : i in [1..8]]];

  A := Algebra<F, 8 | mult>;
  
  perm := Sym(8)!(2,3,4,5,6,1);

  p1proj := (-3/512*al^5 + 21/256*al^4 - 9/128*al^3 + 1/64*al^2)/(al^3 - 3/2*al^2 + 3/4*al - 1/8);
  qproj := (-5/4*al^4 + 23/16*al^3 - 17/72*al^2 - 7/36*al + 1/18)/(al^2 - 17/18*al + 2/9);
  p1_p1 := (-219/8192*al^7 + 69/1024*al^6 - 91/2048*al^5 + 9/1024*al^4)/(al^4 - 2*al^3 + 3/2*al^2 - 1/2*al + 1/16);
  p1_q := (-65/256*al^7 + 419/1024*al^6 - 421/2304*al^5 - 5/288*al^4 + 17/576*al^3 - 1/192*al^2)/(al^4 - 35/18*al^3 + 17/12*al^2 - 11/24*al + 1/18);
  q_q := (1075/192*al^7 - 3755/256*al^6 + 50041/3456*al^5 - 10127/1728*al^4 - 1/16*al^3 + 373/432*al^2 - 59/216*al + 1/36)/(al^4 - 17/9*al^3 + 433/324*al^2 - 34/81*al + 4/81);
  
  frob := Matrix([PermuteSequence([1,-al^2*(3*al-2)/(4*(2*al-1))^2, al*(21*al^2-18*al+4)/(4*(2*al-1))^2, al/2, al*(21*al^2-18*al+4)/(4*(2*al-1))^2, -al^2*(3*al-2)/(4*(2*al-1))^2, p1proj, qproj], perm^-i) : i in [0..5]] cat [[ p1proj : i in [1..6]] cat [p1_p1, p1_q]] cat [[ qproj : i in [1..6]] cat [p1_q, q_q]]);
  
  return A, {@A.1, A.2@}, frob;
end intrinsic;
