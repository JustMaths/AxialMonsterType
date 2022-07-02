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
intrinsic III(:base_field:=QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Yabe's III(al, bt, mu) algebra over a function field, with generators and its Frobenius form.  Optional paramenter base_field of the base field.
  }
  F<al, bt, mu> := FunctionField(base_field, 2);
  
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
  
  return Algebra<F,4 | mult>, frob;
end intrinsic;




