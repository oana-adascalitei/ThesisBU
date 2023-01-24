_<x> := PolynomialRing(Rationals());
Y := HyperellipticCurve((25*x^2-4*19*x+50)*(x^2+4*7*x+2)*(x^2-2));
JY := Jacobian(Y);

K<e> := QuadraticField(97);
ClassNumber(K); //1
_<x> := PolynomialRing(K);
YK := ChangeRing(Y,K);
#Automorphisms(YK);
Exponent(AutomorphismGroup(YK)); 

// ``bielliptic model" of Y over K
g := 194^2*(1/194*(-1495*e + 14647)*x^6 + 1/97*(819*e-6111)*x^4 + 1/97*(-819*e - 6111)*x^2 + 1/194*(1495*e + 14647));
H := HyperellipticCurve(g);
_,m:=IsIsomorphic(H,YK);

f := 194^2*(1/194*(-1495*e + 14647)*x^3 + 1/97*(819*e-6111)*x^2 + 1/97*(-819*e - 6111)*x + 1/194*(1495*e + 14647));
Ef := HyperellipticCurve(f);
E,map := EllipticCurve(Ef);

Emin, mapmin := MinimalModel(E);

G := Generators(Emin);

assert Order(G[1]) eq 2;

P2:= Ef!(Inverse(map))((Inverse(mapmin))(G[2])); //(1 : -970 : 1)
P3:=Ef!(Inverse(map))((Inverse(mapmin))(G[3])); //(1/136806*(-18971*e - 181535) : 1/3442951*(-882284549*e - 8967908117) : 1)
P2,P3;
//(1/136806*(-18971*e - 181535) : 1/3442951*(-882284549*e - 8967908117) : 1) (1 : -970 : 1)

//Magma might swap the order of these two generators, so we will fix them:

P2 := Ef![1,-970];
P3 := [1/136806*(-18971*e - 181535),1/3442951*(-882284549*e - 8967908117)];


L<r> := SplittingField(x^2-P3[1]);
HL := ChangeRing(H,L);
YL := ChangeRing(Y,L);
_, HtoY := IsIsomorphic(HL,YL);  

pt1 := HL![r,P3[2]];
P := YL!HtoY(pt1); //defined over L

// P := YL![1/13818021096*(21775479423*r^3 - 5167778247*r^2 + 46350110506*r + 5626558062),
// 1/67878674117001354112*(-1395978446186944295897*r^3 - 2806681075832463155523*r^2
//     - 3371472394527336224430*r + 1367397897266240141926)];

Pbar := YL![1/13818021096*(-21775479423*r^3 - 5167778247*r^2 - 46350110506*r + 5626558062),
1/67878674117001354112*(1395978446186944295897*r^3 - 2806681075832463155523*r^2
    + 3371472394527336224430*r + 1367397897266240141926)];

JYL := Jacobian(YL);
Inf := PointsAtInfinity(YL);
JYL![P,Inf[1]]+JYL![Pbar,Inf[2]];
YK := ChangeRing(Y,K);
JYK := Jacobian(YK);
PP := JYK!(JYL![P,Inf[1]]+JYL![Pbar,Inf[2]]); //defined over K


// PP := JYK![x^2 + 1/242792*(-25183*e - 438703)*x + 1/1456752*(327379*e + 2789635), 
//     1/13351711867296*(5663362594927*e - 141507678901313)*x + 
//     1/26703423734592*(157557240366857*e + 2201794607897657)];


PPbar := JYK![x^2 + 1/242792*(25183*e - 438703)*x + 1/1456752*(-327379*e + 2789635), 
    1/13351711867296*(-5663362594927*e - 141507678901313)*x + 
    1/26703423734592*(-157557240366857*e + 2201794607897657)];



D2 := JY!(PP+PPbar); //defined over Q  
Order(D2);

D1 := JY![Y!Inf[1],Y!Inf[2]];
Regulator([D1,D2]); //245.95468477248400605432178288147


//OR
T := JY![x^2 + 28*x + 2, 0];

for P in [T,D1,D2,T+D1,T+D2,D1+D2,T+D1+D2] do
IsDivisibleBy(P,2);
end for;
