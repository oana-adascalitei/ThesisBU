// A challenge of Flynn and Whetherell
//finding the second generator

a := 2; b := 3;
p := 97;
_<x> := PolynomialRing(Rationals());
G1 := (a+b)^2*x^2-4*(a^2+a*b+b^2)*x+2*(a+b)^2;
G2 := (a-b)^2*x^2+4*(a^2-a*b+b^2)*x+2*(a-b)^2;
G3 := x^2-2;
F := G1*G2*G3;
C := HyperellipticCurve(F);
JC := Jacobian(C);

Qsqrt97<sqrt97> := QuadraticField(97);
ClassNumber(Qsqrt97); //1
_<x> := PolynomialRing(Qsqrt97);
CQsqrt97 := ChangeRing(C,Qsqrt97);
auts := Automorphisms(CQsqrt97);
assert Exponent(AutomorphismGroup(CQsqrt97)) eq 2;


ptsCQsqrt97 := Points(CQsqrt97 : Bound:=100);

g := 194^2*(1/194*(-1495*sqrt97 + 14647)*x^6 + 1/97*(819*sqrt97-6111)*x^4 + 1/97*(-819*sqrt97 - 6111)*x^2 + 1/194*(1495*sqrt97 + 14647));
H := HyperellipticCurve(g); //we use this model because the maps are easier
_,m:=IsIsomorphic(H,CQsqrt97);

f := 194^2*(1/194*(-1495*sqrt97 + 14647)*x^3 + 1/97*(819*sqrt97-6111)*x^2 + 1/97*(-819*sqrt97 - 6111)*x + 1/194*(1495*sqrt97 + 14647));
Ef := HyperellipticCurve(f);
E,map := EllipticCurve(Ef);

Emin, mapmin := MinimalModel(E);

G := Generators(Emin);

assert Order(G[1]) eq 2;

P2:= Ef!(Inverse(map))((Inverse(mapmin))(G[2])); //(1 : -970 : 1)
P3:=Ef!(Inverse(map))((Inverse(mapmin))(G[3])); //(1/136806*(-18971*sqrt97 - 181535) : 1/3442951*(-882284549*sqrt97 - 8967908117) : 1)
P2,P3;
(1/136806*(-18971*sqrt97 - 181535) : 1/3442951*(-882284549*sqrt97 - 8967908117) : 1) (1 : -970 : 1)

//Magma might swap the order of these two generators, so we will fix them:

P2 := Ef![1,970];
P3 := Ef![1/136806*(-18971*sqrt97 - 181535),1/3442951*(-882284549*sqrt97 - 8967908117)];

PP2 := E!((Inverse(mapmin))(G[2]));
PP3 := E!((Inverse(mapmin))(G[3]));

Regulator([PP2,PP3]);





M<r> := SplittingField(x^2-P3[1]);
HM := ChangeRing(H,M);
CM := ChangeRing(C,M);
_, HtoC := IsIsomorphic(HM,CM);  

// YK!HtoY(HL![1,-970]);   

pt1 := HM![r,P3[2]];
P := CM!HtoC(pt1); //defined over L

// P := CM![1/13818021096*(21775479423*r^3 - 5167778247*r^2 + 46350110506*r + 5626558062),
// 1/67878674117001354112*(-1395978446186944295897*r^3 - 2806681075832463155523*r^2
//     - 3371472394527336224430*r + 1367397897266240141926)];

Pbar := CM![1/13818021096*(-21775479423*r^3 - 5167778247*r^2 - 46350110506*r + 5626558062),
1/67878674117001354112*(1395978446186944295897*r^3 - 2806681075832463155523*r^2
    + 3371472394527336224430*r + 1367397897266240141926)];

JCM := Jacobian(CM);
Inf := PointsAtInfinity(CM);
JCM![P,Inf[1]]+JCM![Pbar,Inf[2]];
JCQsqrt97 := Jacobian(CQsqrt97);
Q := JCQsqrt97!(JCM![P,Inf[1]]+JCM![Pbar,Inf[2]]); //defined over Q(sqrt(97))


// Q := JCK![x^2 + 1/242792*(-25183*e - 438703)*x + 1/1456752*(327379*e + 2789635), 
//     1/13351711867296*(5663362594927*e - 141507678901313)*x + 
//     1/26703423734592*(157557240366857*e + 2201794607897657)];


Qbar := JCQsqrt97![x^2 + 1/242792*(25183*sqrt97 - 438703)*x + 1/1456752*(-327379*sqrt97 + 2789635), 
    1/13351711867296*(-5663362594927*sqrt97 - 141507678901313)*x + 
    1/26703423734592*(-157557240366857*sqrt97 + 2201794607897657)];



A2 := JC!(Q+Qbar); //defined over Q  
Order(A2);

A1 := JC![C!Inf[1],C!Inf[2]];
Regulator([A1,A2]); //245.95468477248400605432178288147


//OR
T := JC![x^2 + 28*x + 2, 0];
for P in [T,A1,A2,T+A1,T+A2,A1+A2,T+A1+A2] do
    IsDivisibleBy(P,2);
end for;