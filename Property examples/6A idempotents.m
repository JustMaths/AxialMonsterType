AttachSpec("../2-gen Monster.spec");
AttachSpec("../../AxialTools/AxialTools.spec");
load "Find idempotents.m";


///////////////////////////////////////////////////////////////////////////////////////////

////////////////                  6A(al, (-al^2)/(4(2al-1)))

//////////////////////////////////////////////////////////////////////////////////////////

A , gen, frob := M6A();
F<al> := BaseRing(A);

bt := -al^2/4/(2*al-1);

assert bt-1 eq (-al^2-8*al+4)/(4*(2*al-1));
assert al-bt eq al*(9*al-4)/(4*(2*al-1));


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
PF<t> := PolynomialRing(F);
FCl := AlgebraicClosure(F);

// define the cubic

q := t^3 - (4968*al^9 - 6048*al^8 + 3006*al^7 - 1738*al^6 + 750*al^5 + 397*al^4 -464*al^3 + 69*al^2 + 44*al - 12)*t^2
     + (1259712*al^18 - 1824768*al^17 + 4369248*al^16 - 10244448*al^15 + 12876960*al^14 - 9159976*al^13 + 2874060*al^12 + 1158740*al^11 - 1861251*al^10 + 1094920*al^9 - 264422*al^8 - 160512*al^7 + 154970*al^6 - 28168*al^5 - 15205*al^4 + 6696*al^3 - 56*al^2 - 352*al + 48)*t
     -(2*al - 1)^2*(182736*al^15 + 222480*al^14 - 660312*al^13 + 409428*al^12 -188942*al^11 + 116620*al^10 + 2982*al^9 - 35988*al^8 + 18577*al^7 - 14392*al^6 + 4621*al^5 + 2847*al^4 - 1744*al^3 + 40*al^2 + 112*al - 16)^2
/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4);

qroots := [r[1] : r in Roots(q, FCl)];

chis := [ Sqrt(FCl!2^2*r/(3*al - 2)^2/(12*al^2 - al - 2)^2/(14*al^5 + 62*al^4 + 2*al^3 + 11*al^2 - 4*al - 4)) : r in qroots];





i := 1;
basc1 := [ FCl!1, qroots[i], qroots[i]^2, chis[i], qroots[i]*chis[i], chis[i]*qroots[i]^2]@phi;
Uc1 := VectorSpaceWithBasis(basc1);


i := 2;
basc2 := [ v@phi : v in [ FCl!1, qroots[i], qroots[i]^2, chis[i], qroots[i]*chis[i], chis[i]*qroots[i]^2], i in [2,3]];


basc3 := [ v@phi : v in [ FCl!1, qroots[i], qroots[i]^2, chis[i], qroots[i]*chis[i], chis[i]*qroots[i]^2], i in [2,3]];




min := (182736*al^15 + 222480*al^14 - 660312*al^13 + 409428*al^12 - 188942*al^11 + 116620*al^10 + 2982*al^9 - 35988*al^8 + 18577*al^7 - 14392*al^6 + 4621*al^5 + 2847*al^4 - 1744*al^3 + 40*al^2 + 112*al - 16)*t^3 
      + (al - 1)*(3*al - 2)*(190512*al^14 - 783648*al^13 + 809352*al^12 - 734472*al^11 + 523574*al^10 + 83596*al^9 - 261866*al^8 + 61277*al^7 + 16375*al^6 - 3329*al^5 + 1950*al^4 - 2040*al^3 + 160*al^2 + 176*al - 32)
/2^2/(2*al - 1)*t^2
      + (al - 1)*(3*al -2)^2*(131544*al^13 - 271476*al^12 + 603072*al^11 - 1120372*al^10 + 549648*al^9 + 172252*al^8 - 113718*al^7 + 4969*al^6 - 25892*al^5 + 6396*al^4 + 6208*al^3 - 1424*al^2 - 320*al + 64)
      /2^4/(2*al - 1)*t
      + (3*al - 2)^3*(2077992*al^14 + 6833036*al^13 - 10858648*al^12 + 3544884*al^11 - 358164*al^10 + 150440*al^9 + 461434*al^8 - 263285*al^7 + 26374*al^6 - 27908*al^5 - 1288*al^4 + 11792*al^3 - 1760*al^2 - 704*al + 128)
      /2^6/(2*al - 1)^2;

rhos := [r[1] : r in Roots(min, FCl)];

zetas := [ Sqrt(FCl!r) : r in rhos];



lin_comb := [ -(35213807849472*al^37 - 712527310900224*al^36 + 3205412057922048*al^35 -6361262960378112*al^34 + 6071467406092416*al^33 - 530269098822144*al^32 -7058094185803392*al^31 + 11645113404676608*al^30 - 10524079803552912*al^29 +5471704563007152*al^28 - 554771904925256*al^27 - 1904791869461992*al^26 + 2096822327786904*al^25 - 1198702412243452*al^24 + 304328439618224*al^23 + 109094873335514*al^22 - 161822432178162*al^21 + 98006223713526*al^20 - 33433454621341*al^19 - 704098265692*al^18 + 7602515674511*al^17 - 4341770574557*al^16 + 1415926315436*al^15 - 167705094379*al^14 - 192392629463*al^13 + 147089786381*al^12 - 37273885776*al^11 - 4022207190*al^10 + 4923559784*al^9 - 1287857224*al^8 + 124598912*al^7 + 36241472*al^6 - 23993344*al^5 + 5707776*al^4 - 198656*al^3 - 179712*al^2 + 34816*al - 2048)/(2*al - 1),
(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)*(4585351680*al^23 - 7607447424*al^22 + 106323840*al^21 + 7283896272*al^20 - 6710400936*al^19 + 4000901376*al^18 - 1297099336*al^17 - 1507322140*al^16 + 2071473066*al^15 - 871477608*al^14 + 45612026*al^13 + 140688704*al^12 - 143829760*al^11 + 69012623*al^10 + 3203334*al^9 - 15386628*al^8 + 4286156*al^7 + 329516*al^6 - 355456*al^5 + 98384*al^4 - 19008*al^3 - 2496*al^2 + 2048*al - 256)/(2*al - 1),
-(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)*(517104*al^13 + 192564*al^12 - 544752*al^11 - 29502*al^10 + 88550*al^9 - 34202*al^8 + 69741*al^7 - 13285*al^6 - 13916*al^5 + 4342*al^4 - 608*al^3 + 64*al^2 + 128*al - 32)
];

sqrs := [  &+[ 1/2^2/al^2/(3*al - 2)/(2*al^2 + 1)/(12*al^2 - al - 2)/(3483648*al^14 -2256768*al^13 - 4046544*al^12 + 4170312*al^11 - 864116*al^10 - 66820*al^9 +169196*al^8 - 316812*al^7 + 156509*al^6 - 8336*al^5 - 8702*al^4 + 3344*al^3 -2304*al^2 + 832*al - 96)/(182736*al^15 + 222480*al^14 - 660312*al^13 +409428*al^12 - 188942*al^11 + 116620*al^10 + 2982*al^9 - 35988*al^8 + 18577*al^7- 14392*al^6 + 4621*al^5 + 2847*al^4 - 1744*al^3 + 40*al^2 + 112*al - 16)*lin_comb[i]*rho^(i-1) : i in [1..3]] : rho in qroots];


assert uu[7] eq sqrs[3]*uu[8];










p1 := (14*al^5 + 62*al^4 + 2*al^3 + 11*al^2 - 4*al - 4);

f1 := t^6 
      - (1128*al^7 - 848*al^6 + 138*al^5 - 226*al^4 - 70*al^3 + 129*al^2 + 4*al - 12)/(12*al^2 - al - 2)^2/p1*t^4
      - (2*al - 1)*(52128*al^13 + 257872*al^12 - 23560*al^11 + 109516*al^10 - 42128*al^9 - 65828*al^8 + 4684*al^7 - 6396*al^6 + 4530*al^5 + 6363*al^4 - 1064*al^3 - 984*al^2 + 64*al + 48)/(12*al^2 - al - 2)^4/p1^2*t^2
      - (2*al - 1)^2*(13104*al^12 + 54976*al^11 - 2572*al^10 + 12344*al^9 - 12220*al^8 - 7532*al^7 - 228*al^6 - 656*al^5 + 1769*al^4 + 408*al^3 - 328*al^2 -32*al + 16)^2/(12*al^2 - al - 2)^6/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)/p1^3;

f1p := t^3 - (1128*al^7 - 848*al^6 + 138*al^5 - 226*al^4 - 70*al^3 + 129*al^2 + 4*al - 12)*t^2
           - (2*al - 1)*(52128*al^13 + 257872*al^12 - 23560*al^11 + 109516*al^10 - 42128*al^9 - 65828*al^8 + 4684*al^7 - 6396*al^6 + 4530*al^5 + 6363*al^4 - 1064*al^3 - 984*al^2 + 64*al + 48)*t
           - (2*al - 1)^2*(13104*al^12 + 54976*al^11 - 2572*al^10 + 12344*al^9 - 12220*al^8 - 7532*al^7 - 228*al^6 - 656*al^5 + 1769*al^4 + 408*al^3 - 328*al^2 -32*al + 16)^2/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4);

// f1p is a cubic associated with f1
assert Evaluate(f1p, p1*(12*al^2 - al - 2)^2*t^2) eq f1*(12*al^2 - al - 2)^6*p1^3;

f2 := t^6
      -(19572*al^8 - 28390*al^7 + 11730*al^6 - 260*al^5 - 1217*al^4 + 1224*al^3 - 424*al^2 - 96*al + 48)/2^2/(2*al - 1)/(12*al^2 - al - 2)^2/p1*t^4
      -(5*al - 2)*(9264528*al^15 + 34415920*al^14 - 51671532*al^13 + 15770704*al^12 + 606220*al^11 - 4047212*al^10 + 4994596*al^9 - 736880*al^8 - 687407*al^7 + 48682*al^6 - 43116*al^5 + 53704*al^4 + 12336*al^3 - 8736*al^2 - 576*al + 384)/2^4/(2*al - 1)^2/(12*al^2 - al - 2)^4/p1^2*t^2
       -(2077992*al^14 + 6833036*al^13 - 10858648*al^12 + 3544884*al^11 - 358164*al^10 + 150440*al^9 + 461434*al^8 - 263285*al^7 + 26374*al^6 - 27908*al^5- 1288*al^4 + 11792*al^3 - 1760*al^2 - 704*al + 128)^2/2^6/(2*al - 1)^2/(12*al^2- al - 2)^6/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)/p1^3;

f2p := t^3
       - (19572*al^8 - 28390*al^7 + 11730*al^6 - 260*al^5 - 1217*al^4 + 1224*al^3 - 424*al^2 - 96*al + 48)*t^2
       -(5*al - 2)*(9264528*al^15 + 34415920*al^14 - 51671532*al^13 + 15770704*al^12 + 606220*al^11 - 4047212*al^10 + 4994596*al^9 - 736880*al^8 - 687407*al^7 + 48682*al^6 - 43116*al^5 + 53704*al^4 + 12336*al^3 - 8736*al^2 - 576*al + 384)*t
       -(2*al-1)*(2077992*al^14 + 6833036*al^13 - 10858648*al^12 + 3544884*al^11 - 358164*al^10 + 150440*al^9 + 461434*al^8 - 263285*al^7 + 26374*al^6 - 27908*al^5- 1288*al^4 + 11792*al^3 - 1760*al^2 - 704*al + 128)^2/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4);

assert Evaluate(f2p, 2^2*(2*al-1)*p1*(12*al^2 - al - 2)^2*t^2) eq f2*2^6*(2*al-1)^3*(12*al^2 - al - 2)^6*p1^3;

f3 := t^6
       -2^2*(4968*al^9 - 6048*al^8 + 3006*al^7 - 1738*al^6 + 750*al^5 + 397*al^4 - 464*al^3 + 69*al^2 + 44*al - 12)/(3*al - 2)^2/(12*al^2 - al - 2)^2/p1*t^4
       + 2^4*(1259712*al^18 - 1824768*al^17 + 4369248*al^16 - 10244448*al^15 + 12876960*al^14 - 9159976*al^13 + 2874060*al^12 + 1158740*al^11 - 1861251*al^10 +1094920*al^9 - 264422*al^8 - 160512*al^7 + 154970*al^6 - 28168*al^5 - 15205*al^4+ 6696*al^3 - 56*al^2 - 352*al + 48)/(3*al - 2)^4/(12*al^2 - al - 2)^4/p1^2*t^2
      -2^6*(2*al - 1)^2*(182736*al^15 + 222480*al^14 - 660312*al^13 + 409428*al^12 -188942*al^11 + 116620*al^10 + 2982*al^9 - 35988*al^8 + 18577*al^7 - 14392*al^6 +4621*al^5 + 2847*al^4 - 1744*al^3 + 40*al^2 + 112*al - 16)^2/(3*al - 2)^6/(12*al^2 - al - 2)^6/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)/p1^3;

f3p := t^3
       -(4968*al^9 - 6048*al^8 + 3006*al^7 - 1738*al^6 + 750*al^5 + 397*al^4 - 464*al^3 + 69*al^2 + 44*al - 12)*t^2
       + (1259712*al^18 - 1824768*al^17 + 4369248*al^16 - 10244448*al^15 + 12876960*al^14 - 9159976*al^13 + 2874060*al^12 + 1158740*al^11 - 1861251*al^10 +1094920*al^9 - 264422*al^8 - 160512*al^7 + 154970*al^6 - 28168*al^5 - 15205*al^4+ 6696*al^3 - 56*al^2 - 352*al + 48)*t
       - (2*al - 1)^2*(182736*al^15 + 222480*al^14 - 660312*al^13 + 409428*al^12 -188942*al^11 + 116620*al^10 + 2982*al^9 - 35988*al^8 + 18577*al^7 - 14392*al^6 +4621*al^5 + 2847*al^4 - 1744*al^3 + 40*al^2 + 112*al - 16)^2/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4);

assert Evaluate(f3p, (3*al-2)^2*(12*al^2 - al - 2)^2/2^2*p1*t^2) eq f3*(3*al-2)^6*(12*al^2 - al - 2)^6*p1^3/2^6;

// All these three cubics have the same discriminant up to squares
disc := SquareFreePart(Discriminant(f1p));
assert SquareFreePart(Discriminant(f2p)) eq disc;
assert SquareFreePart(Discriminant(f3p)) eq disc;

assert disc eq -(2*al - 1)*(2*al^2 + 1)*(2*al^2 + 9*al - 2)*(14*al^3 - 8*al^2 + 5*al - 2)/2^4;
disc := 2^4*disc;


f4 := t^12
      -2*(9984*al^9 - 19520*al^8 + 12626*al^7 - 2992*al^6 - 310*al^5 + 936*al^4 - 578*al^3 + 57*al^2 + 52*al - 12)/(2*al - 1)^2/(12*al^2 - al - 2)^2/p1*t^10
      + (84621312*al^18 - 467074048*al^17 + 895075328*al^16 - 842746304*al^15 + 423774628*al^14 - 74109624*al^13 - 71604732*al^12 + 77010492*al^11 - 32061130*al^10 + 2335536*al^9 + 3800002*al^8 - 2392048*al^7 + 793148*al^6 + 9620*al^5 - 124457*al^4 + 35112*al^3 + 1800*al^2 - 2080*al + 240)/(2*al - 1)^4/(12*al^2 - al - 2)^4/p1^2*t^8
      + 2*(9591177019392*al^31 + 25525659746304*al^30 - 271574062997504*al^29 + 720707783364608*al^28 - 1030658669409536*al^27 + 947924428542400*al^26 - 599915584829840*al^25 + 244779123546208*al^24 - 21738892254120*al^23 - 58991944476132*al^22 + 55462417280660*al^21 - 29287614580518*al^20 + 9214376705054*al^19 + 213321272628*al^18 - 2276380623374*al^17 + 1473548303499*al^16 - 529393894870*al^15 + 67732744850*al^14 + 58277060654*al^13- 45028863628*al^12 + 14437063408*al^11 - 1438668068*al^10 - 1051198764*al^9 + 791663850*al^8 - 244280288*al^7 - 2589856*al^6 + 25520640*al^5 - 6510144*al^4 - 6656*al^3 + 268800*al^2 - 46080*al + 2560)/(2*al - 1)^5/(12*al^2 - al - 2)^6/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)/p1^3*t^6
      + (12890478340472832*al^39 + 65118919076610048*al^38 - 153913109924020224*al^37 - 550254488937496576*al^36 + 2448343737448976384*al^35 - 4240901900524259328*al^34+ 4404489220748159488*al^33 - 3043269983742772992*al^32 + 1308206190593444864*al^31 - 81947227259195200*al^30 - 406504551831165288*al^29 +388709423937635256*al^28 - 207896967683620448*al^27 + 61864501993132164*al^26 + 7169670520336550*al^25 - 21730468855367190*al^24 + 14261487366353554*al^23 - 5248319307171173*al^22 + 543960821274134*al^21 + 759936744831060*al^20 - 594465460133134*al^19 + 220582898020677*al^18 - 31689515144764*al^17 - 18148080147116*al^16 + 16758767141236*al^15 - 6218432501948*al^14 + 580707973186*al^13 + 503137083190*al^12 - 302282420334*al^11 + 93885652757*al^10- 5054477532*al^9 - 11037767692*al^8 + 4468291200*al^7 - 227843936*al^6 - 272079488*al^5 + 67942016*al^4 - 578048*al^3 - 2031360*al^2 + 312320*al - 15360)/(2*al - 1)^6/(12*al^2 - al - 2)^8/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)/p1^4*t^4
      + 2*(413257034694131712*al^44 + 3297835663983378432*al^43 + 3525192263296548864*al^42 - 19899751969455996928*al^41 - 9852046865128742912*al^40 + 79799092854002530304*al^39 - 107907761976238500352*al^38 + 77070966923148423936*al^37 - 31207347937375802752*al^36 - 2910876336891220800*al^35 + 16596396116162710064*al^34 - 13233726684481240640*al^33 + 5767736086585130448*al^32 - 1091521126535366576*al^31 - 914740812399975552*al^30+ 1096645671610307928*al^29 - 535882023733674364*al^28+ 132424304620402176*al^27 + 22612844094930709*al^26 - 55618635787623710*al^25 + 31694354373058556*al^24 - 7384279726175420*al^23 -536265115003774*al^22 + 1779821309386046*al^21 - 1230503776091110*al^20 + 322916240896214*al^19 + 37130670840094*al^18 - 53952391358656*al^17 + 29762118594884*al^16 -8963519665704*al^15 - 1506211026030*al^14 + 1725063518120*al^13 - 423220570379*al^12 + 70647399688*al^11 + 18116574120*al^10 - 31535110752*al^9 + 8058097200*al^8 + 1975517440*al^7 - 1085049600*al^6 + 31558656*al^5 + 51235584*al^4 - 7313408*al^3 - 628736*al^2 + 204800*al - 12288)/(2*al - 1)^4/(12*al^2 - al - 2)^10/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)/p1^5*t^2
      + (77160480768*al^27 + 434246132736*al^26 + 61307435648*al^25 -1181405073664*al^24 + 870176093600*al^23 - 250312918888*al^22 + 111004934032*al^21 + 47294472388*al^20 - 98892523184*al^19 + 32165823134*al^18 -11951638852*al^17 + 4685803263*al^16 + 4629850766*al^15 - 2619157027*al^14 + 338282832*al^13 - 242260185*al^12 - 47246506*al^11 + 106984586*al^10 - 13471338*al^9 + 334127*al^8 - 1413136*al^7 - 1835760*al^6 + 828672*al^5 + 123296*al^4 - 82176*al^3 + 1792*al^2 + 2560*al - 256)^2/(2*al - 1)^2/(12*al^2 - al - 2)^12/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)^2/p1^6;

f4p := t^6
       -2*(9984*al^9 - 19520*al^8 + 12626*al^7 - 2992*al^6 - 310*al^5 + 936*al^4 - 578*al^3 + 57*al^2 + 52*al - 12)/(2*al - 1)^2*t^5
       + (84621312*al^18 - 467074048*al^17 + 895075328*al^16 - 842746304*al^15 + 423774628*al^14 - 74109624*al^13 - 71604732*al^12 + 77010492*al^11 - 32061130*al^10 + 2335536*al^9 + 3800002*al^8 - 2392048*al^7 + 793148*al^6 + 9620*al^5 - 124457*al^4 + 35112*al^3 + 1800*al^2 - 2080*al + 240)/(2*al - 1)^4*t^4
       + 2*(9591177019392*al^31 + 25525659746304*al^30 - 271574062997504*al^29 + 720707783364608*al^28 - 1030658669409536*al^27 + 947924428542400*al^26 - 599915584829840*al^25 + 244779123546208*al^24 - 21738892254120*al^23 - 58991944476132*al^22 + 55462417280660*al^21 - 29287614580518*al^20 + 9214376705054*al^19 + 213321272628*al^18 - 2276380623374*al^17 + 1473548303499*al^16 - 529393894870*al^15 + 67732744850*al^14 + 58277060654*al^13- 45028863628*al^12 + 14437063408*al^11 - 1438668068*al^10 - 1051198764*al^9 + 791663850*al^8 - 244280288*al^7 - 2589856*al^6 + 25520640*al^5 - 6510144*al^4 - 6656*al^3 + 268800*al^2 - 46080*al + 2560)/(2*al - 1)^5/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)*t^3
       + (12890478340472832*al^39 + 65118919076610048*al^38 - 153913109924020224*al^37 - 550254488937496576*al^36 + 2448343737448976384*al^35 - 4240901900524259328*al^34+ 4404489220748159488*al^33 - 3043269983742772992*al^32 + 1308206190593444864*al^31 - 81947227259195200*al^30 - 406504551831165288*al^29 +388709423937635256*al^28 - 207896967683620448*al^27 + 61864501993132164*al^26 + 7169670520336550*al^25 - 21730468855367190*al^24 + 14261487366353554*al^23 - 5248319307171173*al^22 + 543960821274134*al^21 + 759936744831060*al^20 - 594465460133134*al^19 + 220582898020677*al^18 - 31689515144764*al^17 - 18148080147116*al^16 + 16758767141236*al^15 - 6218432501948*al^14 + 580707973186*al^13 + 503137083190*al^12 - 302282420334*al^11 + 93885652757*al^10- 5054477532*al^9 - 11037767692*al^8 + 4468291200*al^7 - 227843936*al^6 - 272079488*al^5 + 67942016*al^4 - 578048*al^3 - 2031360*al^2 + 312320*al - 15360)/(2*al - 1)^6/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)*t^2
       + 2*(413257034694131712*al^44 + 3297835663983378432*al^43 + 3525192263296548864*al^42 - 19899751969455996928*al^41 - 9852046865128742912*al^40 + 79799092854002530304*al^39 - 107907761976238500352*al^38 + 77070966923148423936*al^37 - 31207347937375802752*al^36 - 2910876336891220800*al^35 + 16596396116162710064*al^34 - 13233726684481240640*al^33 + 5767736086585130448*al^32 - 1091521126535366576*al^31 - 914740812399975552*al^30+ 1096645671610307928*al^29 - 535882023733674364*al^28+ 132424304620402176*al^27 + 22612844094930709*al^26 - 55618635787623710*al^25 + 31694354373058556*al^24 - 7384279726175420*al^23 -536265115003774*al^22 + 1779821309386046*al^21 - 1230503776091110*al^20 + 322916240896214*al^19 + 37130670840094*al^18 - 53952391358656*al^17 + 29762118594884*al^16 -8963519665704*al^15 - 1506211026030*al^14 + 1725063518120*al^13 - 423220570379*al^12 + 70647399688*al^11 + 18116574120*al^10 - 31535110752*al^9 + 8058097200*al^8 + 1975517440*al^7 - 1085049600*al^6 + 31558656*al^5 + 51235584*al^4 - 7313408*al^3 - 628736*al^2 + 204800*al - 12288)/(2*al - 1)^4/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)*t
       + (77160480768*al^27 + 434246132736*al^26 + 61307435648*al^25 -1181405073664*al^24 + 870176093600*al^23 - 250312918888*al^22 + 111004934032*al^21 + 47294472388*al^20 - 98892523184*al^19 + 32165823134*al^18 -11951638852*al^17 + 4685803263*al^16 + 4629850766*al^15 - 2619157027*al^14 + 338282832*al^13 - 242260185*al^12 - 47246506*al^11 + 106984586*al^10 - 13471338*al^9 + 334127*al^8 - 1413136*al^7 - 1835760*al^6 + 828672*al^5 + 123296*al^4 - 82176*al^3 + 1792*al^2 + 2560*al - 256)^2/(2*al - 1)^2/(270*al^5 - 234*al^4 + 74*al^3 - 53*al^2 + 28*al - 4)^2;

assert Evaluate(f4p, (12*al^2 - al - 2)^2*p1*t^2) eq f4*(12*al^2 - al - 2)^12*p1^6;






ACl := ChangeRing(A, FCl);
frobCl := ChangeRing(frob, FCl);

// G_FCl := ChangeRing(G, FCl);

// In addition to the 208 idempotents below, there are 4 orbits of size 12 giving 2^8 = 256 = 208 + 4*12 idempotents in total.

// ----------------------------------------

// Orbits of size 1

// ----------------------------------------

// We have eight in total.

// Three mutually orthogonal idempotents sum to the identity
c := ACl.7;
zp := 2^2*(2*al-1)/(3*al-2)/(al+2)*ACl.8;
assert zp eq -al^2/bt/(3*al-2)/(al+2)*ACl.8;
s := 2*(2*al-1)/(12*al^2-al-2)*( ACl![1,1,1,1,1,1,0,0] -3*al*ACl.7 -6*al/(al+2)*ACl.8);
assert s eq -1/2*al^2/bt/(12*al^2-al-2)*( ACl![1,1,1,1,1,1,0,0] -3*al*ACl.7 -6*al/(al+2)*ACl.8);

assert IsIdempotent(c) and IsIdempotent(s) and IsIdempotent(zp);

assert s*zp eq 0 and c*zp eq 0 and c*zp eq 0;

so, id := HasOne(ACl);
assert so;

assert id eq s+c+zp;

assert InnerProduct(c*frobCl,c) eq 1;
assert InnerProduct(zp*frobCl,zp) eq 2*(7*al-4)/(3*al-2)/(al+2);
assert InnerProduct(s*frobCl,s) eq -12*(al-1)*(al^2+4*al-2)/(al+2)/(12*al^2-al-2);

orbs := {@ {@ v @} : v in {@ ACl!0, c,zp,s, zp+s, c+s, c+zp, id @}@};
idems := {@ ACl!0, c,zp,s, zp+s, c+s, c+zp, id @};



// ----------------------------------------

// Orbits of size 2

// ----------------------------------------

// We have 4 orbits in total

id13 := 2*(2*al - 1)/(7*al^2 + al - 2)*( (ACl.1+ACl.3+ACl.5) + (5*al - 2)/(3*al - 2)*ACl.8);
assert IsIdempotent(id13);

o_id13 := ChangeUniverse(Orbit(GG, Vector(id13)), ACl);
assert #o_id13 eq 2;
assert InnerProduct(id13*frobCl, id13) eq (71*al^2 - 76*al + 20)/(3*al - 2)/(7*al^2 + al - 2);

assert id-id13 notin o_id13;
o_id13_pair := ChangeUniverse(Orbit(GG, Vector(id-id13)), ACl);
assert InnerProduct((id-id13)*frobCl, id-id13) eq (17*al - 8)*(al^2 + 4*al - 2)/(12*al^2 - al - 2)/(7*al^2 + al - 2);

assert IsIdempotent(id13 - zp);
o_zp_id13 := ChangeUniverse(Orbit(GG, Vector(id13-zp)), ACl);
assert #o_zp_id13 eq 2;
assert InnerProduct((id13-zp)*frobCl, id13-zp) eq -3*(3*al^2 - 10*al + 4)/(al + 2)/(7*al^2 + al - 2);

assert id-(id13-zp) notin o_zp_id13;
o_zp_id13_pair := ChangeUniverse(Orbit(GG, Vector(id-(id13-zp))), ACl);
assert InnerProduct((id-(id13-zp))*frobCl, id-(id13-zp)) eq 3*(409*al^5 - 118*al^4 - 204*al^3 - 48*al^2 + 128*al - 32)/(3*al - 2)/(al+2)/(12*al^2 - al - 2)/(7*al^2 + al - 2);

orbs join:= {@ o_id13, o_id13_pair, o_zp_id13, o_zp_id13_pair @};
idems join:= &join {@ o_id13, o_id13_pair, o_zp_id13, o_zp_id13_pair @};
// ----------------------------------------

// Orbits of size 3

// ----------------------------------------

// We have 8 orbits in total

id14 := 1/(al+1)*(ACl.1+ACl.4+ACl.7);
assert IsIdempotent(id14);

o_id14 := ChangeUniverse(Orbit(GG, Vector(id14)), ACl);
assert #o_id14 eq 3;
assert InnerProduct(id14*frobCl, id14) eq 3/(al+1);

assert id-id14 notin o_id14;
o_id14_pair := ChangeUniverse(Orbit(GG, Vector(id-id14)), ACl);
assert InnerProduct((id-id14)*frobCl, id-id14) eq 3*(7*al-4)*(al^2+4*al-2)/(3*al-2)/(al+1)/(12*al^2-al-2);

// Add in id14 - c which is in the subalgebra <<a_1, a_4, a_7>>
c_id14 := id14 - c; 
assert IsIdempotent(c_id14);
o_c_id14 := ChangeUniverse(Orbit(GG, Vector(c_id14)), ACl);
assert #o_c_id14 eq 3;
assert InnerProduct(c_id14*frobCl, c_id14) eq (2-al)/(al+1);

assert id-c_id14 notin o_c_id14;
o_c_id14_pair := ChangeUniverse(Orbit(GG, Vector(id-c_id14)), ACl);
assert InnerProduct((id-c_id14)*frobCl, id-c_id14) eq (36*al^4 + 30*al^3 + 41*al^2 - 90*al + 28)/(3*al - 2)/(al + 1)/(12*al^2 - al -2);

u1 := 1/(7*al^2 + al - 2)*( -1*al*(ACl.1+ACl.4)
                           + 2*(2*al - 1)*(ACl.2+ACl.3+ACl.5+ACl.6)
                           + -al*(7*al-4)*ACl.7
                           + 2^2*al*(2*al-1)/(3*al-2)*ACl.8);

assert u1 eq 1/(7*al^2 + al - 2)*( (2-5*al)*(ACl.1+ACl.4 - al*c -2*al*zp) + (12*al^2-al-2)*s);

assert u1-id/2 eq 1/(7*al^2 + al - 2)*( (2-5*al)*(ACl.1+ACl.4) + (al-1)*(3*al-2)/2*c +(13*al^2 - 9*al + 2)/2*zp + (17*al^2 - 3*al - 2)/2*s);

assert IsIdempotent(u1);

o1 := ChangeUniverse(Orbit(GG, Vector(u1)), ACl);
assert #o1 eq 3;
assert InnerProduct(u1*frobCl, u1) eq -(7*al - 4)*(3*al^2 - 10*al + 4)/(3*al - 2)/(7*al^2 + al - 2);

assert id-u1 notin o1;
o1_pair := ChangeUniverse(Orbit(GG, Vector(id-u1)), ACl);
assert InnerProduct((id-u1)*frobCl, id-u1) eq (84*al^4 + 22*al^3 + 21*al^2 - 66*al + 20)/(12*al^2 - al - 2)/(7*al^2 + al - 2);


assert u1*c eq 0;

u1c := u1+c;
assert IsIdempotent(u1c);

o1c := ChangeUniverse(Orbit(GG, Vector(u1c)), ACl);
assert #o1c eq 3;
assert InnerProduct(u1c*frobCl, u1c) eq (71*al^2 - 76*al + 20)/(3*al - 2)/(7*al^2 + al - 2);

assert id-u1c notin o1;
o1c_pair := ChangeUniverse(Orbit(GG, Vector(id-u1c)), ACl);
assert InnerProduct((id-u1c)*frobCl, id-u1c) eq (17*al - 8)*(al^2 + 4*al - 2)/(12*al^2 - al - 2)/(7*al^2 + al - 2);

orbs join:= {@ o_id14, o_id14_pair, o_c_id14, o_c_id14_pair, o1, o1_pair, o1c, o1c_pair @};
idems join:= &join {@ o_id14, o_id14_pair, o_c_id14, o_c_id14_pair, o1, o1_pair, o1c, o1c_pair @};

assert #idems eq 8+2*4+3*8;
// ----------------------------------------

// Orbits of size 6

// ----------------------------------------

// We have 28 orbits in total

// axes
axes := ChangeUniverse(Orbit(GG, Vector(ACl.1)), ACl);
assert #axes eq 6;

axes_id := ChangeUniverse(Orbit(GG, Vector(id-ACl.1)), ACl);
assert #axes_id eq 6;

assert InnerProduct((id-ACl.1)*frobCl, id-ACl.1) eq -2*(18*al^3 - 78*al^2 + 67*al - 16)/(3*al - 2)/(12*al^2 - al - 2);

// also can subtract the id in the subalgebra

axes_id13 := ChangeUniverse(Orbit(GG, Vector(id13-ACl.1)), ACl);
assert #axes_id13 eq 6;
assert InnerProduct((id13-ACl.1)*frobCl, id13-ACl.1) eq -(7*al - 4)*(3*al^2 - 10*al + 4)/(3*al - 2)/(7*al^2 + al - 2);

axes_id14 := ChangeUniverse(Orbit(GG, Vector(id14-ACl.1)), ACl);
assert #axes_id14 eq 6;
assert InnerProduct((id14-ACl.1)*frobCl, id14-ACl.1) eq (2-al)/(al+1);

// For each of these we get id - these
axes_idid13 := ChangeUniverse(Orbit(GG, Vector(id-(id13-ACl.1))), ACl);
assert #axes_idid13 eq 6;
assert InnerProduct((id-(id13-ACl.1))*frobCl, id-(id13-ACl.1)) eq (84*al^4 + 22*al^3 + 21*al^2 - 66*al + 20)/(12*al^2 - al - 2)/(7*al^2 + al - 2);

axes_idid14 := ChangeUniverse(Orbit(GG, Vector(id-(id14-ACl.1))), ACl);
assert #axes_idid14 eq 6;
assert InnerProduct((id-(id14-ACl.1))*frobCl, id-(id14-ACl.1)) eq (36*al^4 + 30*al^3 + 41*al^2 - 90*al + 28)/(3*al - 2)/(al + 1)/(12*al^2 - al -2);

// u2 is in 3A subalgebra
u2 := -1*al/(2*al - 1)/(al + 2)*ACl.1 + 2/(al+2)*(ACl.3+ACl.5) + 2*al/(3*al - 2)/(al + 2)*ACl.8;

assert u2 eq -1*al/(2*al - 1)/(al + 2)*ACl.1 + 2/(al+2)*(ACl.3+ACl.5) -2*bt/al*zp;

assert IsIdempotent(u2);
o2 := ChangeUniverse(Orbit(GG, Vector(u2)), ACl);
assert #o2 eq 6;
assert InnerProduct(u2*frobCl, u2) eq 2*(7*al - 4)/(3*al - 2)/(al + 2);

assert id-u2 notin o2;
o2_pair := ChangeUniverse(Orbit(GG, Vector(id-u2)), ACl);
assert #o2_pair eq 6;
assert InnerProduct((id-u2)*frobCl, id-u2) eq -(13*al^2 - 68*al + 28)/(al + 2)/(12*al^2 - al - 2);

// So also get id13-u2 as an idempotent
assert IsIdempotent(id13-u2);
o2_id13 := ChangeUniverse(Orbit(GG, Vector(id13-u2)), ACl);
assert #o2_id13 eq 6;
assert InnerProduct((id13-u2)*frobCl, id13-u2) eq -3*(3*al^2 - 10*al + 4)/(al + 2)/(7*al^2 + al - 2);

assert id-(id13-u2) notin o2;
o2_id13_pair := ChangeUniverse(Orbit(GG, Vector(id-(id13-u2))), ACl);
assert #o2_id13_pair eq 6;
assert InnerProduct((id-(id13-u2))*frobCl, id-(id13-u2)) eq 3*(409*al^5 - 118*al^4 - 204*al^3 - 48*al^2 + 128*al - 32)/(3*al - 2)/(al +2)/(12*al^2 - al - 2)/(7*al^2 + al - 2);

assert ACl.4*u2 eq 0;

u2a := ACl.4 + u2;
assert IsIdempotent(u2a);
o2a := ChangeUniverse(Orbit(GG, Vector(u2a)), ACl);
assert #o2a eq 6;
assert InnerProduct(u2a*frobCl, u2a) eq 3*(al^2 + 6*al - 4)/(3*al - 2)/(al + 2);

assert id-u2a notin o2a;
o2a_pair := ChangeUniverse(Orbit(GG, Vector(id-u2a)), ACl);
assert #o2a_pair eq 6;
assert InnerProduct((id-u2a)*frobCl, id-u2a) eq -2^2*3*(al - 1)*(al^2 + 4*al - 2)/(al + 2)/(12*al^2 - al - 2);


// Somehow related to id13???
// Looks worse when written as id/2 \pm
u3 := 1/(7*al^2 + al - 2)*( -al*ACl.1 -2*(5*al - 2)*al/(al + 2)*(ACl.2+ACl.6) + 2*(2*al - 1)*(ACl.3+ACl.5) + (5*al - 2)*al^2/(2*al - 1)/(al + 2)*ACl.4 + (5*al - 2)*ACl.7 -2*(al - 1)*al/(al + 2)*ACl.8);

// same orbit
// u1c = u1+c
// u3 + id-u1c eq id -u2;

// so u3 = u1c-u2 = u1+c-u2

assert IsIdempotent(u3);
o3 := ChangeUniverse(Orbit(GG, Vector(u3)), ACl);

assert c+u1-u2 in o3;
assert #o3 eq 6;
assert InnerProduct(u3*frobCl, u3) eq -3*(3*al^2 - 10*al + 4)/(al + 2)/(7*al^2 + al - 2);

assert id-u3 notin o3;
o3_pair := ChangeUniverse(Orbit(GG, Vector(id-u3)), ACl);
assert #o3_pair eq 6;
assert InnerProduct((id-u3)*frobCl, id-u3) eq 3*(409*al^5 - 118*al^4 - 204*al^3 - 48*al^2 + 128*al - 32)/(3*al - 2)/(al + 2)/(12*al^2 - al - 2)/(7*al^2 + al - 2);

// a = u-id/2
// last 6 are all related
// 4 different min polys of degrees 6,12,6,6
// a_1=a_{-1}, a_2 = a_{-2}
// a_7, a_8 have unique min polys
/*
a_1=a_3
a_4=a_6
both have the same min poly degree 6
a_2 and a_5 have same min poly, degree 12
// al min poly only have even powers




*/


