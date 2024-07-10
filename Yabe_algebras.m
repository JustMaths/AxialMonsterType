/*

Yabe's algebras in his own basis

*/
import "Utilities_for_algebra_creation.m": QQ, MakeSymmetric;
// NB We use al, bt for the eigenvalues





// --------------------------
//
// The III algebra
//
// --------------------------
// NB we use mu for his al
intrinsic III(:base_ring:=QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's III(al, bt, mu) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base field.
  }
  require Characteristic(base_ring) ne 2: "The characteristic of the field cannot be 2.";
  F<al, bt, mu> := FunctionField(base_ring, 2);
  
  pi_fact := (al+1)*(al-bt)*mu +(3*al^2+3*al*bt-bt-1);
  pi := -al*pi_fact/(4*(2*al-1));

  mult := [[[1,0,0,0], [(al-bt)*(mu+1)/2+bt, (al-bt)/2+bt, (al-bt)/2, 1], [(1-mu)*(al-bt)/2+bt, (1-mu)*(al-bt)*(mu+1)/2, (1-mu)*(al-bt)/2+bt, (1-mu)], [pi, 0,0,0]],  
           [[(al-bt)*(mu+1)/2+bt, (al-bt)/2+bt, (al-bt)/2, 1], [0,1,0,0], [(al-bt)*(mu+1)/2, (al-bt)/2+bt, (al-bt)/2+bt, 1], [0, pi, 0,0]],
           [[(1-mu)*(al-bt)/2+bt, (1-mu)*(al-bt)*(mu+1)/2, (1-mu)*(al-bt)/2+bt, (1-mu)], [(al-bt)*(mu+1)/2, (al-bt)/2+bt, (al-bt)/2+bt, 1], [0,0,1,0], [0,0,pi, 0]],
           [[pi, 0,0,0], [0, pi, 0,0], [0,0,pi, 0], [0,0,0,pi]]];

  mult := [[[1,0,0,0], [(al-bt)*(mu+1)/2+bt, (al-bt)/2+bt, (al-bt)/2, 1], [(al-bt)*(mu+1)/2+bt, (al-bt)/2, (al-bt)/2+bt, 1], [pi, 0,0,0]],
           [[(al-bt)*(mu+1)/2+bt, (al-bt)/2+bt, (al-bt)/2, 1], [0,1,0,0], [(1-mu)*(al-bt)*(mu+1)/2, (1-mu)*(al-bt)/2+bt, (1-mu)*(al-bt)/2+bt, (1-mu)], [0, pi, 0,0]],
           [[(al-bt)*(mu+1)/2+bt, (al-bt)/2, (al-bt)/2+bt, 1], [(1-mu)*(al-bt)*(mu+1)/2, (1-mu)*(al-bt)/2+bt, (1-mu)*(al-bt)/2+bt, (1-mu)], [0,0,1,0], [0,0,pi, 0]],
           [[pi, 0,0,0], [0, pi, 0,0], [0,0,pi, 0], [0,0,0,pi]]];
  
  proj1 := pi/al +1/4*((al-bt)*mu +3*(al+bt) +1);

  proj2 := (-1/8*al^3*bt*mu^2 - 1/4*al^3*bt*mu + 3/8*al^3*bt + 1/8*al^3*mu^2 + 
          1/4*al^3*mu - 3/8*al^3 + 1/8*al^2*bt^2*mu^2 - 1/2*al^2*bt^2*mu + 
          3/8*al^2*bt^2 - 3/4*al^2*bt*mu^2 + 5/8*al^2*bt*mu - 7/8*al^2*bt + 
          1/8*al^2*mu^2 - 5/8*al^2*mu + 1/2*al^2 + 5/8*al*bt^2*mu^2 - 5/8*al*bt^2 
          + 1/8*al*bt*mu^2 + 5/8*al*bt*mu + 3/4*al*bt + 1/8*al*mu - 1/8*al - 
          1/4*bt^2*mu^2 + 1/4*bt^2 - 1/4*bt*mu - 1/4*bt)/(al^2*bt - al^2 - 
          3/2*al*bt + 3/2*al + 1/2*bt - 1/2);
          
  frob := Matrix([[1, proj1, proj1, pi], [proj1, 1, proj2, pi], [proj1, proj2, 1, pi], [pi, pi, pi, pi*(pi/al -((al-bt)*(mu+3)+2*bt-1)/4)]]);
  
  A := Algebra<F,4 | mult>;
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;

intrinsic V2(:base_ring:=QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's V2(al, 1/2) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_ring of the base field.
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
  
  /*
  am2:= A.1;
  am1 := A.2;
  a0 := A.3;
  a1 := A.4;
  a2 := A.5;
  p := A.6;
  
  a3 := am2 + 5*(a2-am1)-10*(a1-a0);
  am3 := a2 -5*(a1-am2) +10*(a0-am1);
  
  am3*am1 eq 4*p-1/4*(a2+am2-4*(a1+am1)+6*a0) +bt*(am3+am1);
  am2*a0 eq 4*p-1/4*(a2+am2-4*(a1+am1)+6*a0) +bt*(am2+a0);
  am1*a1 eq 4*p-1/4*(a2+am2-4*(a1+am1)+6*a0) +bt*(am1+a1);
  a0*a2 eq 4*p-1/4*(a2+am2-4*(a1+am1)+6*a0) +bt*(a0+a2);
  a1*a3 eq 4*p-1/4*(a2+am2-4*(a1+am1)+6*a0) +bt*(a1+a3);
  
  am2 eq a3 -5*(a2-am1) + 10*(a1-a0);
  am2*a1 eq a1*a3 - 5*a1*(a2-am1) + 10*a1*(a1-a0);
  
  a2 eq am3 + 5*(a1-am2) -10*(a0-am1);
  a2*am1 eq am1*am3 + 5*am1*(a1-am2) -10*am1*(a0-am1);
  */

  frob := Matrix(F, [[1,1,1,1,1,0] : i in [1..5]] cat [[0,0,0,0,0,0]]);
  
  return A, {@ A.1, A.2 @}, frob;
end intrinsic;




