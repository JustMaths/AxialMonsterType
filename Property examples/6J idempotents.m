AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";


///////////////////////////////////////////////////////////////////////////////////////////

////////////////                  6J(2bt, bt)

//////////////////////////////////////////////////////////////////////////////////////////

A , gen, frob := M6J();
F<bt> := BaseRing(A);

t1:= MiyamotoInvolution(A.1);
t2:= MiyamotoInvolution(A.2);
f := PermutationMatrix(F,[2,1,6,5,4,3,7,8]);
assert forall{<i,j> : i,j in [1..8] | ((A.i)*f)*((A.j)*f) eq (A.i*A.j)*f};

G := sub<GL(8,F) | t1,t2,f>;
Miy := sub<GL(8,F)|t1,t2>;
assert Order(Miy) eq 6;
assert Order(G) eq 12;

tt1 := Sym(8)!(2,6)(3,5);
tt2 := Sym(8)!(4,6)(3,1);
ff := Sym(8)![2,1,6,5,4,3,7,8];

GG := sub<Sym(8)| tt1,tt2,ff>;
/*

Finding the idempotents is computationally expensive.
Here we list the idempotents.
Since we know how many to expect, we can show we have them all.

*/
// We need to add roots to the field
PF := PolynomialRing(F);

p1 := 2^7*3*bt^5 -3*5*2^6*bt^4 + 373*bt^3 -3*7*bt^2 -3^2*bt +1;

PF := PolynomialRing(F);
FCl := AlgebraicClosure(F);
rt1 := Sqrt(FCl!-(11*bt-1)/p1);
rt2 := Sqrt(FCl!-(4*bt - 1)*(4*bt^2 - 7*bt + 1)/p1);

rt3 := Sqrt(FCl!1/(36*bt^4 + 140*bt^3 - 43*bt^2 - 2*bt + 1));

f6:= 2^4*(7*bt + 1)^4*p1^2*PF.1^4 + 2^3*(7*bt + 1)^2*p1*(960*bt^5 - 1536*bt^4 + 167*bt^3 + 69*bt^2 - 3*bt - 1)*PF.1^2 + (608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)^2;

rt6 := Roots(f6, FCl)[1,1];
/*
f2 := PF.1^2 + 2*(960*bt^5 - 1536*bt^4 + 167*bt^3 + 69*bt^2 - 3*bt - 1)*PF.1 + (608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)^2;
rootf2 := Roots(f2, FCl)[1,1];

rt2 := Sqrt(FCl!rootf2/2^2/(7*bt+1)^2/(384*bt^5 - 960*bt^4 + 373*bt^3 - 21*bt^2 - 9*bt + 1));
*/

// The poly for the ratios of the roots in the idempotent
q := PF.1^3 + (95150080*bt^13 - 30660608*bt^12 + 41302272*bt^11 - 7444096*bt^10 + 4008752*bt^9 - 629208*bt^8 - 61800*bt^7 - 29922*bt^6 - 5787*bt^5 - 833*bt^4 + 874*bt^3 + 12*bt^2 - 7*bt - 1)/(20676608*bt^13 - 6565888*bt^12 + 7718912*bt^11 - 1156480*bt^10 + 668544*bt^9 - 49480*bt^8 - 14756*bt^7 - 7906*bt^6 - 2063*bt^5 - 209*bt^4 + 6*bt^3 + 76*bt^2 - 3*bt - 1)*PF.1^2
        + (124190720*bt^13 - 50341888*bt^12 + 53701632*bt^11 - 13538432*bt^10 + 5279872*bt^9 - 956448*bt^8 - 112776*bt^7 + 34662*bt^6 - 20817*bt^5 + 4337*bt^4 + 206*bt^3 - 72*bt^2 - 5*bt + 1)/(20676608*bt^13 - 6565888*bt^12 + 7718912*bt^11 - 1156480*bt^10 + 668544*bt^9 - 49480*bt^8 - 14756*bt^7 - 7906*bt^6 - 2063*bt^5 - 209*bt^4 + 6*bt^3 + 76*bt^2 - 3*bt - 1)*PF.1 + (35348480*bt^13 - 20611072*bt^12 + 13622784*bt^11 - 3971328*bt^10 + 326784*bt^9 + 57856*bt^8 - 130924*bt^7 + 35614*bt^6 - 2341*bt^5 - 159*bt^4 + 322*bt^3 - 80*bt^2 - bt + 1)/(20676608*bt^13 - 6565888*bt^12 + 7718912*bt^11 - 1156480*bt^10 + 668544*bt^9 - 49480*bt^8 - 14756*bt^7 - 7906*bt^6 - 2063*bt^5 - 209*bt^4 + 6*bt^3 + 76*bt^2 - 3*bt - 1);

rhos := [ r[1] : r in Roots(q, FCl)];

// define three xi_i as the linear combinations below of 1, rho and rho^2

lin_comb := [-(184225240186880*bt^25 + 288702425202688*bt^24 - 74735996108800*bt^23 + 224221306814464*bt^22 - 92218797981696*bt^21 + 70634041679872*bt^20 - 31441472532480*bt^19 + 13262442963968*bt^18 - 5672465330688*bt^17 + 1758753594400*bt^16 - 578395573840*bt^15 + 145753586896*bt^14 - 25623893176*bt^13 + 2938203714*bt^12 + 869988875*bt^11 - 497299218*bt^10 + 135625966*bt^9 - 26408511*bt^8 + 2126690*bt^7 + 286000*bt^6 - 114976*bt^5 + 11104*bt^4 + 2283*bt^3 - 374*bt^2 - 30*bt + 5),
            -2*bt*(66539613061120*bt^24 + 133440162758656*bt^23 - 38252056674304*bt^22 + 99026917130240*bt^21 - 39275684069376*bt^20 + 28395688206336*bt^19 - 12556797956096*bt^18 + 4940435230720*bt^17 - 2169311800192*bt^16 + 673127462496*bt^15 - 224931380528*bt^14 + 64717274624*bt^13 - 13817295552*bt^12 + 3055018414*bt^11 - 473069311*bt^10 + 45655443*bt^9 - 14833136*bt^8 + 4425680*bt^7 - 1094770*bt^6 + 295650*bt^5 - 29748*bt^4 - 4934*bt^3 + 1033*bt^2 - 13*bt - 4),
            -(1220608*bt^12 + 3514368*bt^11 - 601344*bt^10 + 682688*bt^9 - 276912*bt^8 + 72972*bt^7 - 38112*bt^6 + 11871*bt^5 - 2826*bt^4 + 742*bt^3 - 96*bt^2 - 9*bt + 2)*(20676608*bt^13 - 6565888*bt^12 + 7718912*bt^11 - 1156480*bt^10 + 668544*bt^9- 49480*bt^8 - 14756*bt^7 - 7906*bt^6 - 2063*bt^5 - 209*bt^4 + 6*bt^3 + 76*bt^2 - 3*bt - 1)];

// Each of these has a min poly being a cubic
sqrs := [  &+[1/2^2/(7*bt + 1)^3/(20*bt^2 - 3*bt + 1)/(56*bt^3 - 9*bt^2 + 6*bt - 1)/(2048*bt^8 - 5632*bt^7 + 2096*bt^6 - 1796*bt^5 + 412*bt^4 - 101*bt^3 + 17*bt^2 + 5*bt - 1)/(151552*bt^11 + 261120*bt^10 - 26240*bt^9 + 89408*bt^8 - 10808*bt^7 + 8132*bt^6 - 4022*bt^5 + 389*bt^4 - 272*bt^3 + 18*bt^2 + 22*bt - 3)*lin_comb[i]*rho^(i-1) : i in [1..3]] : rho in rhos];

m := {@ MinimalPolynomial(sqrs[i]) :  i in [1..3] @};
assert #m eq 1;
m := m[1];
assert Degree(m) eq 3;

xis := [Sqrt(sqrs[i]) : i in [1..3]];

// Simplify takes about 104 secs
Simplify(FCl: Partial:=true);
Prune(FCl);

// We require that the square roots are chose with compatable signs:

signs := [ <i,j> : i,j in [+1,-1]];

value := 1/2/(7*bt + 1)/(56*bt^3 - 9*bt^2 + 6*bt - 1)/(151552*bt^11 + 261120*bt^10 - 26240*bt^9 + 89408*bt^8 - 10808*bt^7 + 8132*bt^6 - 4022*bt^5 + 389*bt^4 - 272*bt^3 + 18*bt^2 + 22*bt - 3)*
          ( (1096679424*bt^16 - 598540288*bt^15 + 482988032*bt^14 - 201112576*bt^13 + 39421696*bt^12 - 17985792*bt^11 + 105744*bt^10 + 357752*bt^9 + 189048*bt^8 + 83334*bt^7 - 13165*bt^6 + 2252*bt^5 - 3007*bt^4 + 214*bt^3 + 69*bt^2 - 1)/2/bt*xis[1] +
            (64*bt^3 - 2*bt^2 + 5*bt - 1)*(26603520*bt^12 - 6814720*bt^11 + 11714176*bt^10 - 1791808*bt^9 + 1137656*bt^8 - 197588*bt^7 - 6058*bt^6 - 17687*bt^5 + 1019*bt^4 - 938*bt^3 + 364*bt^2 + 5*bt - 5)*xis[1]*rhos[1] + 
            (64*bt^3 - 2*bt^2 + 5*bt - 1)*(20676608*bt^13 - 6565888*bt^12 + 7718912*bt^11 - 1156480*bt^10 + 668544*bt^9 - 49480*bt^8 - 14756*bt^7 - 7906*bt^6 - 2063*bt^5 - 209*bt^4 + 6*bt^3 + 76*bt^2 - 3*bt - 1)/2/bt*xis[1]*rhos[1]^2 );

so := exists(p){ p : p in signs | p[1]*xis[2] + p[2]*xis[3] eq value };

assert so;
xis[2] *:= p[1];
xis[3] *:= p[2];



ACl := ChangeRing(A, FCl);
frobCl := ChangeRing(frob, FCl);

G_FCl := ChangeRing(G, FCl);

// In addition to the 208 idempotents below, there are 4 orbits of size 12 giving 2^8 = 256 = 208 + 4*12 idempotents in total.

// ----------------------------------------

// Orbits of size 1

// ----------------------------------------

// We have eight in total.

// Three mutually orthogonal idempotents sum to the identity
u := ACl.7;
wp := 1/(bt+1)*( -bt*ACl.7 + ACl.8);
s := 1/(7*bt+1)*( ACl![1,1,1,1,1,1,0,0] -6*bt/(bt+1)*(ACl.7+ACl.8));

assert IsIdempotent(u) and IsIdempotent(s) and IsIdempotent(wp);

assert s*wp eq 0 and u*wp eq 0 and u*s eq 0;

so, id := HasOne(ACl);
assert so;

assert id eq s+u+wp;

assert InnerProduct(u*frobCl,u) eq 1;
assert InnerProduct(wp*frobCl,wp) eq (-bt + 2)/(bt + 1);
assert InnerProduct(s*frobCl,s) eq -6*(2*bt-1)/(bt+1)/(7*bt+1);

assert HasJordanFusionLaw(u:fusion_value:=2*bt);
assert Dimension(Eigenspace(u,1)) eq 1;
assert u*(ACl.1+ACl.4 -2*bt*ACl.7) eq 0;  // 2 more of these in the subalgebras <<a_1, a_4, a_8>>
// this also contains wp
assert u*s eq 0;

assert u*(ACl.1-ACl.4) eq 2*bt*(ACl.1-ACl.4); // 2 more of these

orbs := {@ {@ v @} : v in {@ ACl!0, u,wp,s, wp+s, u+s, u+wp, id @}@};
idems := {@ ACl!0, u,wp,s, wp+s, u+s, u+wp, id @};

// s is not graded.
// u is Jordan type 2bt
// wp is C_2-graded with 5 eigenvalues

assert InnerProduct((u+wp)*frobCl, (u+wp)) eq 3/(bt + 1);
assert InnerProduct((s+wp)*frobCl, (s+wp)) eq (8-7*bt)/(1+7*bt);
assert InnerProduct((u+s)*frobCl, (u+s)) eq (7*bt^2-4*bt+7)/(7*bt^2+8*bt+1);

assert InnerProduct((id)*frobCl, (id)) eq 9/(1+7*bt);

// ---------------------------------------

// Try a different basis

// ---------------------------------------
s0 := ACl.1+ACl.3+ACl.5;
bas := [ACl.1-ACl.3,ACl.3-ACl.5,ACl.2-ACl.4,ACl.4-ACl.6, s0, s, u, wp];

// ----------------------------------------

// Orbits of size 2

// ----------------------------------------

// We have four of these

// There is an identity inside the subalgebra <<a_1, a_3, a_5>> \cong 3C(bt)
id13 := 1/(bt+1)*(ACl.1+ACl.3+ACl.5);

assert InnerProduct(id13*frobCl, id13) eq 3/(bt+1);
// 4 eigenvalues, not graded

o_id13 := ChangeUniverse(Orbit(GG, Vector(id13)), ACl);
assert #o_id13 eq 2;
assert id-id13 notin o_id13;

o_id13_pair := ChangeUniverse(Orbit(GG, Vector(id-id13)), ACl);
assert InnerProduct((id-id13)*frobCl, id-id13) eq -2*3*(2*bt-1)/(bt+1)/(7*bt+1);


// u1 := 1/(608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)*(2^2*(7*bt + 1)^2*(384*bt^5 - 960*bt^4 + 373*bt^3 - 21*bt^2 - 9*bt + 1

// for -rt2, we get the other element in the orbit.  Changing the signs of both rt1 and rt2 gives the orbit of id-u1.

u1 := id/2 + bt*(2*bt-1)/(7*bt+1)*rt1*ACl![1,1,1,1,1,1,0,0] 
            + rt2/2*ACl![1,-1,1,-1,1,-1,0,0]
             + (46*bt^2 - 3*bt - 1)/2/(7*bt + 1)*rt1*ACl.7
               - (24*bt^2 - bt - 1)/2/(7*bt + 1)*rt1*ACl.8;

assert u1 eq (bt+1)*rt2*id13 + ((-7*bt - 1)/2*rt2 + (2*bt^2 - bt)*rt1 + 1/2)*s
                    +(-3*bt*rt2 + (5*bt - 1)/2*rt1 + 1/2)*u
                    +(-3*bt*rt2 + (-5*bt + 1)/2*rt1 + 1/2)*wp;

assert InnerProduct(u1*frobCl, u1) eq 1/2/(7*bt+1)*( 3^2 + (2*bt-1)*(11*bt-1)*rt1 );
// 6 eigenvalues, not graded

o1 := ChangeUniverse(Orbit(GG, Vector(u1)), ACl);
assert #o1 eq 2;
assert id-u1 notin o1;

o1_pair := ChangeUniverse(Orbit(GG, Vector(id - u1)), ACl);
assert InnerProduct((id-u1)*frobCl, id-u1) eq 1/2/(7*bt+1)*( 3^2 - (2*bt-1)*(11*bt-1)*rt1 );

orbs join:= {@ o_id13, o_id13_pair, o1, o1_pair @};
idems join:= &join {@ o_id13, o_id13_pair, o1, o1_pair @};
// ----------------------------------------

// Orbits of size 3

// ----------------------------------------

// We have 8 of these

id14 := 1/(2*bt+1)*(ACl.1+ACl.4+ACl.7);
assert IsIdempotent(id14);

o_id14 := ChangeUniverse(Orbit(GG, Vector(id14)), ACl);
assert #o_id14 eq 3;
assert InnerProduct(id14*frobCl, id14) eq 3/(2*bt+1);

assert id-id14 notin o_id14;
o_id14_pair := ChangeUniverse(Orbit(GG, Vector(id-id14)), ACl);
assert InnerProduct((id-id14)*frobCl, id-id14) eq -3*(bt-2)/(7*bt+1)/(2*bt+1);


// Add in id14 - u which is in the subalgebra <<a_1, a_4, a_7>>
u_id14 := id14 - u; 
assert IsIdempotent(u_id14);
o_u_id14 := ChangeUniverse(Orbit(GG, Vector(u_id14)), ACl);
assert #o_u_id14 eq 3;
assert InnerProduct(u_id14*frobCl, u_id14) eq 2*(1-bt)/(2*bt+1);
// 7 eigenvalues, C_2 x C_2 graded, tau_1 and flip

assert id-u_id14 notin o_u_id14;
o_u_id14_pair := ChangeUniverse(Orbit(GG, Vector(id-u_id14)), ACl);
assert InnerProduct((id-u_id14)*frobCl, id-u_id14) eq (14*bt^2+6*bt+7)/(7*bt+1)/(2*bt+1);

u2 := id/2 + (2*bt*(5*bt-1)*rt3 - 1/2)*u
           + (26*bt^2 - 9*bt + 1)/2*rt3*wp
           + (34*bt^2 - 3*bt - 1)/2*rt3*s
           - (5*bt-1)*rt3*(ACl.1 + ACl.4);

assert u2 eq id/2 + 1/2*( -u + 3*(2*bt^2 - 5*bt + 1)*rt3*wp + (14*bt^2 - 9*bt + 1)*rt3*s) + (10*bt^2 + 3*bt - 1)*rt3*(id-id14);


assert IsIdempotent(u2);
o2 := ChangeUniverse(Orbit(GG, Vector(u2)), ACl);
assert #o2 eq 3;
assert InnerProduct(u2*frobCl, u2) eq -(3*bt*(2*bt-1)*(7*bt-1)*rt3 +(7*bt-8))/2/(7*bt+1);

assert id-u2 notin o2;
o2_pair := ChangeUniverse(Orbit(GG, Vector(id-u2)), ACl);
assert InnerProduct((id-u2)*frobCl, id-u2) eq (3*bt*(2*bt-1)*(7*bt-1)*rt3 +(7*bt+10))/2/(7*bt+1);

assert u2*ACl.7 eq 0;
// Check for other idempotents in the 0-eigenspace of u = ACl.7

u3 := u2 + ACl.7;
assert IsIdempotent(u3);
o3 := ChangeUniverse(Orbit(GG, Vector(u3)), ACl);
assert #o3 eq 3;
assert InnerProduct(u3*frobCl, u3) eq -(3*bt*(2*bt-1)*(7*bt-1)*rt3 -(7*bt+10))/2/(7*bt+1);

assert id-u3 notin o3;
o3_pair := ChangeUniverse(Orbit(GG, Vector(id-u3)), ACl);
assert InnerProduct((id-u3)*frobCl, id-u3) eq (3*bt*(2*bt-1)*(7*bt-1)*rt3 -(7*bt-8))/2/(7*bt+1);



assert u3 eq id/2 + (34*bt^2 - 3*bt - 1)/2/(7*bt+1)*rt3*ACl![1,1,1,1,1,1,0,0]
            -(5*bt-1)*rt3*(ACl.1 + ACl.4)
            + (-bt*(42*bt^2 - 7*bt - 1)/2/(7*bt+1)*rt3 + 1/2)*ACl.7
            - (22*bt^2 - 3*bt - 1)/2/(7*bt+1)*rt3*ACl.8;
              
assert u3 eq id/2 + (2*bt*(5*bt-1)*rt3 + 1/2)*u
           + (26*bt^2 - 9*bt + 1)/2*rt3*wp
           + (34*bt^2 - 3*bt - 1)/2*rt3*s
           -(5*bt-1)*rt3*(ACl.1 + ACl.4);

orbs join:= {@ o_id14, o_id14_pair, o_u_id14, o_u_id14_pair, o2, o2_pair, o3, o3_pair @};
idems join:= &join {@ o_id14, o_id14_pair, o_u_id14, o_u_id14_pair, o2, o2_pair, o3, o3_pair @};

assert #idems eq 8+2*4+3*8;
// ----------------------------------------

// Orbits of size 6

// ----------------------------------------

// We have 28 of these

// axes
axes := ChangeUniverse(Orbit(GG, Vector(ACl.1)), ACl);
assert #axes eq 6;

axes_id := ChangeUniverse(Orbit(GG, Vector(id-ACl.1)), ACl);
assert #axes_id eq 6;

assert InnerProduct((id-ACl.1)*frobCl, id-ACl.1) eq (8-7*bt)/(7*bt+1);

// also can subtract the id in the subalgebra

axes_id13 := ChangeUniverse(Orbit(GG, Vector(id13-ACl.1)), ACl);
assert #axes_id13 eq 6;
assert InnerProduct((id13-ACl.1)*frobCl, id13-ACl.1) eq (2-bt)/(bt+1);

axes_id14 := ChangeUniverse(Orbit(GG, Vector(id14-ACl.1)), ACl);
assert #axes_id14 eq 6;
assert InnerProduct((id14-ACl.1)*frobCl, id14-ACl.1) eq 2*(1-bt)/(2*bt+1);

// For each of these we get id - these
axes_idid13 := ChangeUniverse(Orbit(GG, Vector(id-(id13-ACl.1))), ACl);
assert #axes_idid13 eq 6;
assert InnerProduct((id-(id13-ACl.1))*frobCl, id-(id13-ACl.1)) eq (7*bt^2 - 4*bt + 7)/(bt+1)/(7*bt+1);

axes_idid14 := ChangeUniverse(Orbit(GG, Vector(id-(id14-ACl.1))), ACl);
assert #axes_idid14 eq 6;
assert InnerProduct((id-(id14-ACl.1))*frobCl, id-(id14-ACl.1)) eq (14*bt^2 + 6*bt + 7)/(2*bt+1)/(7*bt+1);

orbs join:= {@ axes, axes_id, axes_id13, axes_id14, axes_idid13, axes_idid14 @};
idems join:= &join{@ axes, axes_id, axes_id13, axes_id14, axes_idid13, axes_idid14 @};

u4 := id/2 - 1/2*ACl.1
         +1/2/(7*bt+1)*rt3*( + bt*(42*bt^2 - 7*bt - 1)*ACl.1
                              - (34*bt^2 - 3*bt - 1)*(ACl.2 + ACl.6 + ACl.8)
                              + (22*bt^2-3*bt-1)*(ACl.3 + ACl.5)
                              + (36*bt^2-bt-1)*(ACl.4 + ACl.7) );

assert IsIdempotent(u4);
o4 := ChangeUniverse(Orbit(GG, Vector(u4)), ACl);
assert #o4 eq 6;

assert InnerProduct(u4*frobCl, u4) eq 1/2/(7*bt+1)*( 9 - (7*bt+1) +3*bt*(2*bt-1)*(7*bt-1)*rt3);

assert id-u4 notin o4;
o4_pair := ChangeUniverse(Orbit(GG, Vector(id-u4)), ACl);
assert InnerProduct((id-u4)*frobCl, id-u4) eq 1/2/(7*bt+1)*( 9 + (7*bt+1) -3*bt*(2*bt-1)*(7*bt-1)*rt3);

orbs join:= {@ o4, o4_pair@};
idems := &join orbs;

u5 := id/2 + 1/2*ACL.1
         + (bt*(42*bt^2 - 7*bt - 1)/2/(7*bt+1)*rt3)*ACl.1
         - (34*bt^2 - 3*bt - 1)/2/(7*bt+1)*rt3*(ACl.2 + ACl.6 + ACl.8)
         + (22*bt^2-3*bt-1)/2/(7*bt+1)*rt3*(ACl.3 + ACl.5)
         + (36*bt^2-bt-1)/2/(7*bt+1)*rt3*(ACl.4 + ACl.7);

assert u5 eq u4+ACl.1;

// This corresponds to -rt3
// ie taking the other root of the quadratic which is the minimal poly defining rt3
assert IsIdempotent(u5);
o5 := ChangeUniverse(Orbit(GG, Vector(u5)), ACl);
assert #o5 eq 6;

assert InnerProduct(u5*frobCl, u5) eq 1/2/(7*bt+1)*( 9 + (7*bt+1) +3*bt*(2*bt-1)*(7*bt-1)*rt3);
assert id-u5 notin o5;

o5_pair := ChangeUniverse(Orbit(GG, Vector(id-u5)), ACl);
assert InnerProduct((id-u5)*frobCl, id-u5) eq 1/2/(7*bt+1)*( 9 - (7*bt+1) -3*bt*(2*bt-1)*(7*bt-1)*rt3);;

orbs join:= {@ o5, o5_pair@};
idems := &join orbs;

rt6_conj := 2/(608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)*(
                  2*(7*bt + 1)^2*p1*rt6^3 + 
                  + (960*bt^5 - 1536*bt^4 + 167*bt^3 + 69*bt^2 - 3*bt - 1)*rt6);

assert rt6_conj in Conjugates(rt6) and -rt6_conj in Conjugates(rt6);

u6 := id/2 + 
             (24*bt^2 - bt - 1)/(2*bt - 1)/bt/(608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)
*((7*bt + 1)^2*(384*bt^5 - 960*bt^4 + 373*bt^3 - 21*bt^2 - 9*bt+ 1)*rt6^3 +
(1312*bt^5 - 1920*bt^4 + 287*bt^3 + 61*bt^2 - 3*bt -1)/2^2*rt6)
*( -(46*bt^2 - 3*bt - 1)/(24*bt^2 - bt - 1)*ACl.1 + ACl.3 + ACl.5)
             + rt6*(ACl.2+ACl.4+ACl.6)
             - rt6_conj*(ACl.7+ACl.8);

assert IsIdempotent(u6);
o6 := ChangeUniverse(Orbit(GG, Vector(u6)), ACl);
assert #o6 eq 6;
assert InnerProduct(u6*frobCl, u6) eq
   - (11*bt - 1)/bt/(608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)*(
         (7*bt + 1)^2*p1*rt6^3
         + (1312*bt^5 - 1920*bt^4 + 287*bt^3 + 61*bt^2 - 3*bt - 1)/2^2*rt6 )
     + 3^2/2/(7*bt + 1);

assert id-u6 notin o6;
o6_pair := ChangeUniverse(Orbit(GG, Vector(id-u6)), ACl);
assert InnerProduct((id-u6)*frobCl, id-u6) eq
   (11*bt - 1)/bt/(608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)*(
         (7*bt + 1)^2*p1*rt6^3
         + (1312*bt^5 - 1920*bt^4 + 287*bt^3 + 61*bt^2 - 3*bt - 1)/2^2*rt6 )
     + 3^2/2/(7*bt + 1);

u6c := id/2 + 
             (24*bt^2 - bt - 1)/(2*bt - 1)/bt/(608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)
*((7*bt + 1)^2*(384*bt^5 - 960*bt^4 + 373*bt^3 - 21*bt^2 - 9*bt+ 1)*rt6^3 +
(1312*bt^5 - 1920*bt^4 + 287*bt^3 + 61*bt^2 - 3*bt -1)/2^2*rt6)
*( -(46*bt^2 - 3*bt - 1)/(24*bt^2 - bt - 1)*ACl.1 + ACl.3 + ACl.5)
             - rt6_conj*(ACl.2+ACl.4+ACl.6)
             + rt6*(ACl.7+ACl.8);

assert IsIdempotent(u6c);
o6c := ChangeUniverse(Orbit(GG, Vector(u6c)), ACl);
assert #o6c eq 6;
assert InnerProduct(u6c*frobCl, u6c) eq
   -(11*bt - 1)/bt/(608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)*(
         (7*bt + 1)^2*p1*rt6^3
         + (1312*bt^5 - 1920*bt^4 + 287*bt^3 + 61*bt^2 - 3*bt - 1)/2^2*rt6 )
     + 3^2/2/(7*bt + 1);

assert id-u6c notin o6c;
o6c_pair := ChangeUniverse(Orbit(GG, Vector(id-u6c)), ACl);
assert InnerProduct((id-u6c)*frobCl, id-u6c) eq
   (11*bt - 1)/bt/(608*bt^5 - 1152*bt^4 + 47*bt^3 + 77*bt^2 - 3*bt - 1)*(
         (7*bt + 1)^2*p1*rt6^3
         + (1312*bt^5 - 1920*bt^4 + 287*bt^3 + 61*bt^2 - 3*bt - 1)/2^2*rt6 )
     + 3^2/2/(7*bt + 1);

orbs join:= {@ o6, o6_pair, o6c, o6c_pair @};
assert #orbs eq 8+4+8+14;
idems := &join orbs;
assert #idems eq 8 + 2*4 + 3*8 + 6*14;

// We get 3x2 orbits of idempotents

u71 := ACl![ xis[2]*rhos[2], xis[3], xis[2], xis[3]*rhos[3], xis[2], xis[3], xis[1]*rhos[1], xis[1]];
u72 := ACl![ xis[3]*rhos[3], xis[1], xis[3], xis[1]*rhos[1], xis[3], xis[1], xis[2]*rhos[2], xis[2]];
u73 := ACl![ xis[1]*rhos[1], xis[2], xis[1], xis[2]*rhos[2], xis[1], xis[2], xis[3]*rhos[3], xis[3]];


assert IsIdempotent(id/2 + u71);
o71 := ChangeUniverse(Orbit(GG, Vector(id/2 + u71)), ACl);

assert InnerProduct((id/2+u71)*frobCl, id/2+u71) eq  3*(36*bt^3 - 6*bt^2 + 5*bt - 1)*(20676608*bt^13 - 6565888*bt^12 + 7718912*bt^11 - 1156480*bt^10 + 668544*bt^9 - 49480*bt^8 - 14756*bt^7 - 7906*bt^6 - 2063*bt^5 - 209*bt^4 + 6*bt^3 + 76*bt^2 - 3*bt - 1)/2^2/bt/(7*bt + 1)/(56*bt^3 - 9*bt^2 + 6*bt - 1)/(151552*bt^11 + 261120*bt^10 - 26240*bt^9 + 89408*bt^8 - 10808*bt^7 + 8132*bt^6 - 4022*bt^5 + 389*bt^4 - 272*bt^3 + 18*bt^2 + 22*bt - 3)*xis[1]*rhos[1]^2 + 
        3*(36*bt^3 - 6*bt^2 + 5*bt - 1)*(26603520*bt^12 - 6814720*bt^11 + 11714176*bt^10 - 1791808*bt^9 + 1137656*bt^8 - 197588*bt^7 - 6058*bt^6 - 17687*bt^5 + 1019*bt^4 - 938*bt^3 + 364*bt^2 + 5*bt - 5)/2/(7*bt + 1)/(56*bt^3 - 9*bt^2 + 6*bt - 1)/(151552*bt^11 + 261120*bt^10 - 26240*bt^9 + 89408*bt^8 - 10808*bt^7 + 8132*bt^6 - 4022*bt^5 + 389*bt^4 - 272*bt^3 + 18*bt^2 + 22*bt - 3)*xis[1]*rhos[1] + 
        3*(36*bt^3 - 6*bt^2 + 5*bt - 1)*(20848640*bt^13 - 2369536*bt^12 + 5399296*bt^11 + 268288*bt^10 - 218320*bt^9 + 149240*bt^8 - 100772*bt^7 + 10520*bt^6 - 1475*bt^5 - 35*bt^4 + 270*bt^3 - 30*bt^2 - 7*bt + 1)/2^2/bt/(7*bt + 1)/(56*bt^3 - 9*bt^2 + 6*bt - 1)/(151552*bt^11 + 261120*bt^10 - 26240*bt^9 + 89408*bt^8 - 10808*bt^7 + 8132*bt^6 - 4022*bt^5 + 389*bt^4 - 272*bt^3 + 18*bt^2 + 22*bt - 3)*xis[1] + 
        3^2/2/(7*bt + 1);

assert id/2-u71 notin o71;
o71_pair := ChangeUniverse(Orbit(GG, Vector(id/2-u71)), ACl);
assert InnerProduct((id/2-u71)*frobCl, id/2-u71) eq  -3*(36*bt^3 - 6*bt^2 + 5*bt - 1)*(20676608*bt^13 - 6565888*bt^12 + 7718912*bt^11 - 1156480*bt^10 + 668544*bt^9 - 49480*bt^8 - 14756*bt^7 - 7906*bt^6 - 2063*bt^5 - 209*bt^4 + 6*bt^3 + 76*bt^2 - 3*bt - 1)/2^2/bt/(7*bt + 1)/(56*bt^3 - 9*bt^2 + 6*bt - 1)/(151552*bt^11 + 261120*bt^10 - 26240*bt^9 + 89408*bt^8 - 10808*bt^7 + 8132*bt^6 - 4022*bt^5 + 389*bt^4 - 272*bt^3 + 18*bt^2 + 22*bt - 3)*xis[1]*rhos[1]^2 + 
        -3*(36*bt^3 - 6*bt^2 + 5*bt - 1)*(26603520*bt^12 - 6814720*bt^11 + 11714176*bt^10 - 1791808*bt^9 + 1137656*bt^8 - 197588*bt^7 - 6058*bt^6 - 17687*bt^5 + 1019*bt^4 - 938*bt^3 + 364*bt^2 + 5*bt - 5)/2/(7*bt + 1)/(56*bt^3 - 9*bt^2 + 6*bt - 1)/(151552*bt^11 + 261120*bt^10 - 26240*bt^9 + 89408*bt^8 - 10808*bt^7 + 8132*bt^6 - 4022*bt^5 + 389*bt^4 - 272*bt^3 + 18*bt^2 + 22*bt - 3)*xis[1]*rhos[1] + 
        -3*(36*bt^3 - 6*bt^2 + 5*bt - 1)*(20848640*bt^13 - 2369536*bt^12 + 5399296*bt^11 + 268288*bt^10 - 218320*bt^9 + 149240*bt^8 - 100772*bt^7 + 10520*bt^6 - 1475*bt^5 - 35*bt^4 + 270*bt^3 - 30*bt^2 - 7*bt + 1)/2^2/bt/(7*bt + 1)/(56*bt^3 - 9*bt^2 + 6*bt - 1)/(151552*bt^11 + 261120*bt^10 - 26240*bt^9 + 89408*bt^8 - 10808*bt^7 + 8132*bt^6 - 4022*bt^5 + 389*bt^4 - 272*bt^3 + 18*bt^2 + 22*bt - 3)*xis[1] + 
        3^2/2/(7*bt + 1);


// u72
assert IsIdempotent(id/2 + u72);
o72 := ChangeUniverse(Orbit(GG, Vector(id/2 + u72)), ACl);

assert InnerProduct((id/2+u72)*frobCl, id/2+u72) eq InnerProduct((id/2+u71)*frobCl, id/2+u71);

assert id/2-u72 notin o72;
o72_pair := ChangeUniverse(Orbit(GG, Vector(id/2-u72)), ACl);
assert InnerProduct((id/2-u72)*frobCl, id/2-u72) eq InnerProduct((id/2-u71)*frobCl, id/2-u71);

// u73  
assert IsIdempotent(id/2 + u73);
o73 := ChangeUniverse(Orbit(GG, Vector(id/2 + u73)), ACl);

assert InnerProduct((id/2+u73)*frobCl, id/2+u73) eq InnerProduct((id/2+u71)*frobCl, id/2+u71);

assert id/2-u73 notin o73;
o73_pair := ChangeUniverse(Orbit(GG, Vector(id/2-u73)), ACl);
assert InnerProduct((id/2-u73)*frobCl, id/2-u73) eq InnerProduct((id/2-u71)*frobCl, id/2-u71);

orbs join:= {@ o71, o71_pair, o72, o72_pair, o73, o73_pair @};
assert #orbs eq 8+4+8+20;
idems := &join orbs;
assert #idems eq 8 + 2*4 + 3*8 + 6*20;




// 6 orbits here for id/2 \pm u7


