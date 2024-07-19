/*

Code to check which 3-generated Jordan type 1/2 shapes complete when using the quotients 2B and S(2)^\circ

*/
AttachSpec("2-gen Monster.spec");
AttachSpec("../AxialTools/AxialTools.spec");
Attach("3-gen Jordan type.m");

AA, _, frobAA := GS();
FF<AL, BT, GM, PSI> := BaseRing(AA);

// the values of the projections which give quotients are 0, or 1
test := [* [0], [1], [0,0], [0,1], [1,1], [0,0,0], [0,0,1], [0,1,1], [1,1,1] *];
names := [ "al", "bt", "gm"];

for S in test do
  print "Projection values are ", S;
  if 0 in S then
    if #S eq 3 then
      F := Rationals();
      phi := hom<FF->F | S cat [0]>;
    else
      F := FunctionField(Integers(), 3-#S);
      AssignNames(~F, names[[#S+1..3]]);
      phi := hom<FF->F | S cat [Name(F,i) : i in [1..Rank(F)]] cat [0]>;
    end if;
  else
    if #S eq 3 then
      F := Rationals();
      phi := hom<FF->F | [1,1,1,1] >;
    else
      F := FunctionField(Integers(), 3-#S);
      AssignNames(~F, names[[#S+1..3]]);
      // We always have al + bt + gm = 2psi +1 for this case
      psi_val := 1/2*( &+( S  cat [Name(F,i) : i in [1..Rank(F)]]) -1);
      phi := hom<FF->F | S cat [Name(F,i) : i in [1..Rank(F)]] cat [psi_val]>;
    end if;
  end if;
  
  AF := ChangeRing(AA, F, phi);
  frobF := ChangeRing(frobAA, F, phi);
  
  pairs := [<1,2>, <2,3>, <3,1>];
  
  I := ideal<AF| [ AF.p[1]*AF.p[2] - S[i]/2*(AF.p[1]+AF.p[2]) where p:= pairs[i] : i in [1..#S]] >;
  
  A, quo := quo<AF|I>;
  
  if Dimension(A) le 1 then
    print "  Dimension of the algebra is ", Dimension(A), "\n";
  else
    print "  Dimension of the algebra is ", Dimension(A);
    frob := Matrix([[ InnerProduct((A.i@@quo)*frobF, A.j@@quo) : i in [1..Dimension(A)]]: j in [1..Dimension(A)]]);
  
    flags := [ Dimension(sub<A| [A.i : i in pairs[j]]>) eq 2 : j in [1..#S]] cat
               [ Dimension(sub<A| [A.i : i in pairs[j]]>) eq 3 : j in [#S+1..3]];
    print "  We have the correct subalgebra dimensions", flags, "\n";
  end if;
end for;

// NB for [0,1], we must have psi = 0 and also 0+1+gm = 2psi+1 = 1 so gm = 0.
// This does then complete.
A := GS(0,1,0,0);
I := ideal<A|A.1*A.2, A.2*A.3-1/2*(A.2+A.3)>;
A := quo<A|I>;
assert Dimension(A) eq 4;

assert Dimension(sub<A| A.1, A.2>) eq 2
   and Dimension(sub<A| A.2, A.3>) eq 2
   and Dimension(sub<A| A.3, A.1>) eq 3;

// For [0,1,1] we would need psi = 0 and 2 = 0+1+1 = 2psi +1 and so psi eq 1/2, a contradiction.
