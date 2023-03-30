//we use the Kummer surface like in Michael Stoll's code
//https://www.mathe2.uni-bayreuth.de/stoll/magma/scripts/ellchab.magma


_<x> := PolynomialRing(Rationals());
C := X0NQuotient(147,[3,49]);
C := SimplifiedModel(C);
J := Jacobian(C);
TorsionSubgroup(J);
P := Points(J : Bound:=100);
RankBounds(Jacobian(C): ReturnGenerators := true);
RankBounds(Jacobian(QuadraticTwist(C,-5)));
T := J![x^2-x+1,0];
ptsC := Points(C : Bound:=1000);
ptsJ := [ptsC[i]-ptsC[1] : i in [2,3,4,5,6]];
ptsJ;
bas := ReducedBasis(ptsJ);
Height(bas[1]);
Height(bas[2]);
K := NumberField(x^2+5);
CK := ChangeRing(C,K);
JK := Jacobian(CK);
TorsionBound(JK,10); //2

Kum := KummerSurface(JK);
Pr3<[z]> := ProjectiveSpace(K,3);
KumS := Scheme(Pr3,DefiningPolynomial(Kum));
dup := map<KumS -> KumS | ChangeUniverse(Kum`Delta, CoordinateRing(Pr3))>;

P1 := JK!bas[1];
pt1 := KumS!Eltseq(Kum!P1);
Points(pt1 @@ dup);

P2 := JK!bas[2];
pt2 := KumS!Eltseq(Kum!P2);
Points(pt2 @@ dup);


P3 := JK!(bas[1]+bas[2]);
pt3 := KumS!Eltseq(Kum!P3);
Points(pt3 @@ dup);


PT := JK!T;
ptT := KumS!Eltseq(Kum!PT);
Points(ptT@@ dup);



P1T := JK!(bas[1]+T);
pt1T := KumS!Eltseq(Kum!P1T);
Points(pt1T @@ dup);
P2T := JK!(bas[2]+T);
pt2T := KumS!Eltseq(Kum!P2T);
Points(pt2T @@ dup);
P3T := JK!(bas[1]+bas[2]+T);
pt3T := KumS!Eltseq(Kum!P3T);
Points(pt3T @@ dup);
//all are empty

//sanity check
P4 := JK!(bas[1]+bas[1]);
pt4 := KumS!Eltseq(Kum!P4);
Points(pt4@@dup); 
//{@(0:-1/6:0:1),(-1/2:1:0:0)@}


