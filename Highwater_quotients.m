/*

Highwater algebra quotients

*/
import "Utilities_for_algebra_creation.m": QQ, MakeSymmetric;
// --------------------------------------------
//
//          Highwater quotients
//
// --------------------------------------------
/*

Maximal quotients of the highwater agebra come in two types, those with finitely many axes and those with infinitely many axes.

Also have characteristic 5 cover.

*/
// modulus except returns 1, .., d
function Mymod(x,d)
  xmodd := x mod d;
  return xmodd ne 0 select xmodd else d;
end function;
  
intrinsic HighwaterQuotient(n::RngIntElt: field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Returns the largest quotient of the highwater algebra (or its cover in charatceristic 5) on X(n) axet and its Frobenius form.
  }
  require n in Integers() and n gt 0: "n must be a positive integer";
  // Get the full automorphism group
  if n in [1,2] then
    G := Sym(n);
  else
    G := DihedralGroup(n); // G = D_2n, which in magma is n
  end if;
  
  if Characteristic(field) eq 5 and IsDivisibleBy(n,3) then
    sg_max := Floor(n/2);
    // need to count the number of numbers which are 0 mod 3 less than sg_max
    trips := sg_max div 3;
    sg_num := sg_max + 2*trips;
    
    dim := n + sg_num;
    
    // S is a sequence [r,j]
    function sg_name(S)
      assert Type(S) eq SeqEnum and #S eq 2;
      r,j := Explode(S);
      
      rbar := r mod 3;
      
      jmodn := j mod n;
      if jmodn mod 3 ne 0 then
        rbar := 0;
      end if;
      
      if jmodn gt sg_max then
        jmodn := n-jmodn;
      end if;
      
      return [rbar, jmodn];
    end function;
    
    // fix an ordering of the basis elements
    names := [* i : i in [1..n] *] cat [* x : x in {@ sg_name([r,j]) : r in [0..2], j in [1..sg_max]@} *];
    
    // Need the correct action of the group
    tau0 := Stabiliser(G,1).1;
    
    so, f := IsConjugate(G,1,2);
    assert so;
    if Order(f) ne 2 then
      f := tau0*f;
      assert Order(f) eq 2;
    end if;
    
    S3 := Sym(3);
    sgact := hom<G->S3| [<tau0, S3!(2,3)>, <f,S3!(1,2)>]>;
    
    X := IndexedSet([1..dim]);
    XxG := CartesianProduct(X, G);
    act := map<XxG->X | x:-> x[1] le n select x[1]^x[2] else
                Position(names, sg_name([(names[x[1],1]+1)^(x[2]@sgact)-1, names[x[1],2]]))>;
    X := GSet(G, X, act);
    G := ActionImage(G,X);
    
    V := VectorSpace(field, dim);
    
    // given a set S, return the sg element in V
    function Sg(S)
      SS := sg_name(S);
      if SS[2] eq 0 then
        return Zero(V);
      else
        pos := Position(names, SS);
        assert pos ne 0; // equivalent to membership
        return V.pos;
      end if;
    end function;
    
    function H2coeff(i,r)
      imod := i mod 3;
      rmod := r mod 3;
      if imod eq rmod then
        return 0;
      else
        c := (imod-rmod) mod 3;
        return c eq 1 select -1 else c eq 2 select 1 else 0;
      end if;
    end function;
    
    function sgprod(S,T)
      r,i := Explode(sg_name(S));
      t,j := Explode(sg_name(T));
      
      if not ((i mod 3) eq 0 and (j mod 3) eq 0) then
        return 2*(Sg([r,i]) + Sg([t,j])) -2*(&+[ Sg([k,i-j]) : k in [0..2]] + &+[ Sg([k,i+j]) : k in [0..2]]);
      elif r eq t then
        return 2*(Sg([r,i]) + Sg([t,j])) -(Sg([r,i-j]) + Sg([t,i+j]));
      else
        assert exists(q){ q : q in [0..2] | q notin {r,t}};
        return 2*(Sg([r,i]) + Sg([t,i]) - Sg([q,i]) + Sg([r,j]) + Sg([t,j]) - Sg([q,j]))
                -(Sg([r,i-j]) + Sg([t,i-j]) - Sg([q,i-j]) + Sg([r,i+j]) + Sg([t,i+j]) - Sg([q,i+j]));
      end if;
    end function;
    
    multbas := [<1,1,V.1>] cat [ <1,i,-2*(V.1+V.i) +Sg([i-1,i-1])> : i in [2..n]]
         cat [<1,Position(names, S),-2*V.1 +(V.Mymod(1-j,n) + V.Mymod(1+j,n)) -Sg(S) -H2coeff(0,r)*(Sg([r-1,j]) - Sg([r+1,j]))>
                    where r,j := Explode(S) : S in names[n+1..dim]]
         cat [<Position(names,S), Position(names,T),sgprod(S, T)> : S, T in names[n+1..dim]];

  else // In the Highwater algebra
    sg_num := Floor(n/2);
    
    dim := n + sg_num;
    G := Sym(dim)!!G;
    V := VectorSpace(field, dim);
    
    // given x in Z, return image of sg_|x| in the quotient
    function Sg(x)
      xmodn := x mod n;
      if xmodn eq 0 then
        return Zero(V);
      elif xmodn gt sg_num then
        return V.(n+n-xmodn);
      else
        return V.(n+xmodn);
      end if;
    end function;
    
    multbas := [<1,1,V.1>] cat [ <1,i,1/2*(V.1+V.i) +Sg(i-1)> : i in [2..n]]
         cat [<1,n+j,-3/4*V.1 +3/8*(V.Mymod(1-j,n) + V.Mymod(1+j,n)) + 3/2*Sg(n+j)> : j in [1..sg_num]]
         cat [<n+i,n+j,3/4*(Sg(n+i)+Sg(n+j)) -3/8*(Sg(i-j)+Sg(i+j))> : i,j in [1..sg_num]];
  end if;
  
  mult := BuildSymmetricMultiplication(multbas, G);
  
  frob := DiagonalJoin(AllOnesMatrix(field,n,n), ZeroMatrix(field,sg_num,sg_num));
  
  return Algebra<field, dim | mult>, frob;
end intrinsic;

intrinsic HighwaterQuotient(S::SeqEnum) -> AlgGen, AlgMatElt
  {
  Returns the quotient of the Highwater algebra by the ideal generated by s_1 a_1 + ... + s_n a_n, where S = [s_1, ..., s_n], and its Frobenius form.
  }
  n := #S;
  require &+S eq 0: "The coefficients of the sequence must sum to zero";
  F := FieldOfFractions(Universe(S));
  // Remove restriction for char 5
  require Characteristic(F) notin {2,3,5}: "The characteristic must not be 2,3,5";
  ChangeUniverse(~S, F);
  e := S[1]/S[n];
  require forall{i : i in [1..Floor(n/2)] | S[i] eq e*S[n+1-i]}: "The sequence must be either plus or minus type";
  
  // We have relations on the sg and we must be able to backsolve for the sg which arise in products.  These relations come from folding the S.
  
  // folds S at position 0 \leq p \leq Floor(n/2)
  function fold(S, p)
    S_op := Reverse(S[1..p-1]);
    S_op := S_op cat [0 : i in [1..n-#S_op]];
    S_end := S[p+1..n] cat [0 : i in [1..p]];
    
    assert #S_end eq n and #S_op eq n;
    
    return [F | S_op[i]+S_end[i] : i in [1..n]];
  end function;
  
  Sg_rels := Matrix([ fold(S, p) : p in [0..Floor((n+1)/2)]]);
  
  m := Rank(Sg_rels);
  // if the last row is zero, we prune it off
  if NumberOfRows(Sg_rels) eq m+1 then
    assert IsZero(Sg_rels[m+1]);
    Sg_rels := RowSubmatrix(Sg_rels, m);
  else
    assert NumberOfRows(Sg_rels) eq m;
  end if;
  assert forall{r : r in Rows(Sg_rels) | not IsZero(r)};
  
  // We will need to backsolve for a's and sg's

  // Assume M is a matrix of relations of the form (* | U), where U is upper left triangular.
  function BacksolveMatrix(M)
    // Can use magma's EchelonForm, but we need a horizontal flip
    
    function flip(N)
      return Matrix([Reverse(r) : r in RowSequence(N)]);
    end function;
    
    N := EchelonForm(flip(M));
    Soln := ColumnSubmatrix(-flip(N), NumberOfColumns(N)-Rank(N));
    
    return Matrix([r : r in Reverse(Rows(Soln))]);
  end function;
  
  Sg_elts := BacksolveMatrix(Sg_rels);
  
  // Get the matrix of rels for the a's and backsolve
  Sd := [0 : i in [1..n-1]] cat S;
  A_rels := CyclicShiftsMatrix(F, n, 2*n-1, Sd);
  
  A_elts := BacksolveMatrix(A_rels);
  
  // We now form the multiplication
  d := n-1;  // axial dimension
  sg_num := n-m;
  dim := d + sg_num;
  V := VectorSpace(F, dim);
  
  // given x in Z, return image of sg_|x| in the quotient
  function Sg(x)
    xmod := Abs(x);
    if xmod eq 0 then
      return Zero(V);
    elif xmod le sg_num then
      return V.(d+xmod);
    else
      assert xmod le sg_num+m;
      return V!([F|0 : i in [1..d]] cat Eltseq(Sg_elts[xmod-sg_num]));
    end if;
  end function;
  
  // given x in Z, return image of a_x in the quotient
  // NB the a-axes are numbered a_0...a_{d-1}
  function A(x)
    if x ge 0 and x lt d then
      return V.(x+1);
    elif x lt 0 then
      assert x ge -sg_num;
      // by symmetry, can just look up what the d-x axis is and reverse it.
      // This is the reverse of A_elts[-x]
      return V!(Reverse(Eltseq(A_elts[-x])) cat [F|0 : i in [1..sg_num]]);
    else
      assert x le d+sg_num;
      return V!(Eltseq(A_elts[x-d+1]) cat [F|0 : i in [1..sg_num]]);
    end if;
  end function;

  amult := [ [1/2*(V.i+V.j) + Sg(i-j) : i in [1..j]] : j in [1..d]];
  
  remaining := [ [ i le d select -3/4*A(i-1) +3/8*(A(i-1-j) + A(i-1+j)) + 3/2*Sg(j) 
                   else 3/4*(Sg(i-d)+Sg(j)) -3/8*(Sg(i-d-j)+Sg(i-d+j))
                     : i in [1..d+j] ] : j in [1..sg_num]];
  mult := MakeSymmetric(amult cat remaining);
  
  frob := DiagonalJoin(AllOnesMatrix(F,d,d), ZeroMatrix(F,sg_num,sg_num));
  
  return Algebra<F, dim | mult>, frob;
end intrinsic;

intrinsic HighwaterCoverQuotient(n::RngIntElt: field := QQ) -> AlgGen, SetIndx, AlgMatElt
  {
  Returns the largest quotient of the cover of the highwater algebra on the X(n) axet and its Frobenius form.
  }
  require n in Integers() and n gt 0: "n must be a positive integer";
  // Get the full automorphism group
  if n in [1,2] then
    G := Sym(n);
  else
    G := DihedralGroup(n); // G = D_2n, which in magma is n
  end if;
  
  sg_max := Floor(n/2);
  // need to count the number of numbers which are 0 mod 3 less than sg_max
  trips := sg_max div 3;
  sg_num := sg_max + 2*trips;
  
  dim := n + sg_num;
  
  // S is a sequence [r,j]
  function sg_name(S)
    assert Type(S) eq SeqEnum and #S eq 2;
    r,j := Explode(S);
    
    rbar := r mod 3;
    
    jmodn := j mod n;
    if jmodn mod 3 ne 0 then
      rbar := 0;
    end if;
    
    if jmodn gt sg_max then
      jmodn := n-jmodn;
    end if;
    
    return [rbar, jmodn];
  end function;
  
  // fix an ordering of the basis elements
  names := [* i : i in [1..n] *] cat [* x : x in {@ sg_name([r,j]) : r in [0..2], j in [1..sg_max]@} *];
  
  // Need the correct action of the group
  tau0 := Stabiliser(G,1).1;
  
  so, f := IsConjugate(G,1,2);
  assert so;
  if Order(f) ne 2 then
    f := tau0*f;
    assert Order(f) eq 2;
  end if;
  
  S3 := Sym(3);
  sgact := hom<G->S3| [<tau0, S3!(2,3)>, <f,S3!(1,2)>]>;
  
  X := IndexedSet([1..dim]);
  XxG := CartesianProduct(X, G);
  act := map<XxG->X | x:-> x[1] le n select x[1]^x[2] else
              Position(names, sg_name([(names[x[1],1]+1)^(x[2]@sgact)-1, names[x[1],2]]))>;
  X := GSet(G, X, act);
  G := ActionImage(G,X);
  
  V := VectorSpace(field, dim);
  
  // given a set S, return the sg element in V
  function Sg(S)
    SS := sg_name(S);
    if SS[2] eq 0 then
      return Zero(V);
    else
      pos := Position(names, SS);
      // ERROR here with the assert if n=4.
      assert pos ne 0; // equivalent to membership
      return V.pos;
    end if;
  end function;
  
  // We need the coefficient for \delta(i-r) in H2
  function H2coeff(i,r)
    imod := i mod 3;
    rmod := r mod 3;
    c := (imod-rmod) mod 3;
    
    return c eq 2 select -1 else c;
  end function;
  
  function sgprod(S,T)
    r,i := Explode(sg_name(S));
    t,j := Explode(sg_name(T));
    
    if not ((i mod 3) eq 0 and (j mod 3) eq 0) then
      return 3/4*(Sg([r,i]) + Sg([t,j])) -1/8*(&+[ Sg([k,i-j]) : k in [0..2]] + &+[ Sg([k,i+j]) : k in [0..2]]);
    elif r eq t then
      return 3/4*(Sg([r,i]) + Sg([t,j])) -3/8*(Sg([r,i-j]) + Sg([t,i+j]));
    else
      assert exists(q){ q : q in [0..2] | q notin {r,t}};
      return 3/4*(Sg([r,i]) + Sg([t,i]) - Sg([q,i]) + Sg([r,j]) + Sg([t,j]) - Sg([q,j]))
              -3/8*(Sg([r,i-j]) + Sg([t,i-j]) - Sg([q,i-j]) + Sg([r,i+j]) + Sg([t,i+j]) - Sg([q,i+j]));
    end if;
  end function;
  
  multbas := [<1,1,V.1>] cat [ <1,i,1/2*(V.1+V.i) +Sg([i-1,i-1])> : i in [2..n]]
       cat [<1,Position(names, S),-3/4*V.1 +3/8*(V.Mymod(1-j,n) + V.Mymod(1+j,n)) +3/2*Sg(S) +H2coeff(0,r)*(Sg([r-1,j]) - Sg([r+1,j]))>
                  where r,j := Explode(S) : S in names[n+1..dim]]
       cat [<Position(names,S), Position(names,T),sgprod(S, T)> : S, T in names[n+1..dim]];
  
  mult := BuildSymmetricMultiplication(multbas, G);
  
  frob := DiagonalJoin(AllOnesMatrix(field,n,n), ZeroMatrix(field,sg_num,sg_num));
  
  return Algebra<field, dim | mult>, frob;
end intrinsic;

intrinsic HighwaterCoverQuotient(L::SeqEnum) -> AlgGen, SetIndx, AlgMatElt
  {
  Returns the quotient of the cover of the Highwater algebra by the ideal generated by al_1 a_1 + ... + al_n a_n, where L = [al_1, ..., al_n], and its Frobenius form.
  }
  n := #L;
  require &+L eq 0: "The coefficients of the sequence must sum to zero";
  F := FieldOfFractions(Universe(L));
  // Remove restriction for char 5
  require Characteristic(F) notin {2,3}: "The characteristic must not be 2,3";
  ChangeUniverse(~L, F);
  e := L[1]/L[n];
  require forall{i : i in [1..Floor(n/2)] | L[i] eq e*L[n+1-i]}: "The sequence must be either plus or minus type";
  
  // First check if sum of the indices = i mod (3) equals zero for all i
  
  coeffmod3 := [ &+[F | L[i] : i in [1..n] | i mod 3 eq j ] : j in [0..2]];
  
  if coeffmod3 ne [F | 0,0,0] then
    // By Theorem 8.4, the ideal contains J and hence the quotient is a quotient of the highwater algebra
    return HighwaterQuotient(L);  // FIX char 5 issue/naming of functions
  end if;
  
  if IsOdd(n) and e eq -1 then
    s_max := Floor(n/2);
  else
    s_max := Floor(n/2) -1;
  end if;
  
  // need to count the number of numbers which are 0 mod 3 less than sg_max
  trips := s_max div 3;
  s_num := s_max + 2*trips;
  
  d := n-1;  // axial dimension
  
  // return the correct subscripts for s_{r,j}
  function s_name(r,j)
    rbar := r mod 3;
    
    if j mod 3 ne 0 then
      rbar := 0;
    end if;
    
    return [rbar, Abs(j)];
  end function;
    
  s_names := {@ s_name(r,j) : r in [0..2], j in [1..d]@};
  
  // We have relations on the s and we must be able to backsolve for the s which arise in products.  These relations come from folding the L.

  Vs := VectorSpace(F, #s_names);
  
  // we have a function to define y_k(r) cf Theorem 8.4
  function ykr(k,r)
    return &+[ L[i]*Vs.Position(s_names, s_name(r,i-k)) : i in [1..n] | i ne k];
  end function;
  
  s_rels := Matrix(Setseq({@ ykr(k,r) : r in [0..2], k in [1..d-s_max]@}));
    
  // We will need to backsolve for a's and s's
  
  // For the a's we know that any d consecutive elements are linearly independent, so this is easy.
  // This is more complicated for the s-relations as we could have eg s_{0,3} - s_{1,3} but still have s_{0,7} in the image
  
  // returns a matrix of the backsolved elements and sequence of those which have been removed
  function BacksolveMatrix(M)
    // Can use magma's EchelonForm, but we need a horizontal flip
    
    N := RemoveZeroRows(EchelonForm(ReverseColumns(M)));
    ncols := Ncols(M);
    
    leading := [ ncols+1 - Depth(r) : r in Rows(N)];
    // We must remove these columns from the negation of the Column Reversed Matrix.
    // Also ReverseRow (flip top->bottom) to get solutions in right order
    
    Soln := ReverseRows(ColumnSubmatrix(-ReverseColumns(N), [ i : i in [1..ncols] | i notin leading]));
    
    return Soln, Reverse(leading);
  end function;
  
  s_elts, removed := BacksolveMatrix(s_rels);
  
  // Now that we know which s-elements we can backsolve for, we can write which elements we have in the quotient
  
  // fix an ordering of the basis elements
  names := [* i : i in [1..d] *] cat [* s_names[i] : i in [1..#s_names] | i notin removed *];
  dim := #names;
  s_num := dim-d;

  // Get the matrix of rels for the a's and backsolve
  Ld := [0 : i in [1..n-1]] cat L;
  A_rels := CyclicShiftsMatrix(F, n, 2*n-1, Ld);
  
  A_elts := BacksolveMatrix(A_rels);
  
  // We now form the multiplication
  V := VectorSpace(F, dim);
  
  // given r, j in Z, return image of s_{r,j} in the quotient
  s_removed := [ s_names[i] : i in removed];
  function S(rr, jj)
    r,j := Explode(s_name(rr,jj));
    
    if j eq 0 then
      return Zero(V);
    end if;
    
    pos := Position(s_removed, [r,j]);
    if pos eq 0 then // it was not removed
      return V.Position(names,[r,j]);
    else
      return V!([F|0 : i in [1..d]] cat Eltseq(s_elts[pos]));
    end if;
  end function;
  
  // given x in Z, return image of a_x in the quotient
  // NB the a-axes are numbered a_0...a_{d-1}
  function A(x)
    if x ge 0 and x lt d then
      return V.(x+1);
    elif x lt 0 then
      assert x ge -s_num;
      // by symmetry, can just look up what the d-x axis is and reverse it.
      // This is the reverse of A_elts[-x]
      return V!(Reverse(Eltseq(A_elts[-x])) cat [F|0 : i in [1..s_num]]);
    else
      assert x le d+s_num;
      return V!(Eltseq(A_elts[x-d+1]) cat [F|0 : i in [1..s_num]]);
    end if;
  end function;

  // Now build the multiplication
  
  // We need the coefficient for \delta(i-r) in H2
  function H2coeff(i,r)
    imod := i mod 3;
    rmod := r mod 3;
    c := (imod-rmod) mod 3;
    
    return c eq 2 select -1 else c;
  end function;
  
  // The s_{r,i} s_{t,j} multiplication has several different cases, so we have a function to deal with it
  function sprod(R,T)
    r,i := Explode(R);
    t,j := Explode(T);
    
    if not ((i mod 3) eq 0 and (j mod 3) eq 0) then
      return 3/4*(S(r,i) + S(t,j)) -1/8*(&+[ S(k,i-j) + S(k,i+j): k in [0..2]]);
    elif r eq t then
      return 3/4*(S(r,i) + S(t,j)) -3/8*(S(r,i-j) + S(t,i+j));
    else
      assert exists(q){ q : q in [0..2] | q notin {r,t}};
      return 3/4*(S(r,i) + S(t,i) - S(q,i) + S(r,j) + S(t,j) - S(q,j))
              -3/8*(S(r,i-j) + S(t,i-j) - S(q,i-j) + S(r,i+j) + S(t,i+j) - S(q,i+j));
    end if;
  end function;
  
  amult := [ [1/2*(V.i+V.j) + S(i-1, i-j) : i in [1..j]] : j in [1..d]];
  
  remaining := [ [ -3/4*A(i-1) +3/8*(A(i-1-j) + A(i-1+j)) + 3/2*S(r,j)
                     + H2coeff(i-1,r)*(S(r-1,j) - S(r+1,j))  : i in [1..d]]
                 cat [ sprod([r,j], names[d+l]) : l in [1..k] ] 
                       where r,j := Explode(names[d+k]) : k in [1..s_num]];
  
  mult := MakeSymmetric(amult cat remaining);
  
  frob := DiagonalJoin(AllOnesMatrix(F,d,d), ZeroMatrix(F,s_num,s_num));
  
  return Algebra<F, dim | mult>, frob;
end intrinsic;
