# Checks the degree-2 Nakaoka decomposition of H_2(R wr_X P; F_p) at primes p dividing |P|,
# including p = 2, on finite examples.  Predicted:
#   dim H_2(R wr P) = h2(R)*#orb(X) + [2-set part] + h1(R)*sum_orb dim H_1(P_x;F_p) + dim H_2(P;F_p)
# where the 2-set part sums over P-orbits of 2-subsets {x,y} the coinvariants of V1 (x) V1
# under the setwise stabilizer: elements fixing x,y act trivially, a swap acts by -tau.
hdims:=function(G,p) local ab,m,h1,h2;
  if IsTrivial(G) then return [0,0]; fi; G:=Group(GeneratorsOfGroup(G)); ab:=AbelianInvariants(G);
  m:=AbelianInvariantsMultiplier(Image(IsomorphismFpGroupByGenerators(G,GeneratorsOfGroup(G))));
  h1:=Number(ab,a->a mod p=0);
  h2:=Number(m,a->a mod p=0)+h1;   # UCT: H_2(G;F_p)=H_2(G)/p + Tor(H_1,F_p)
  return [h1,h2];
end;
twoset:=function(P,X,h1,p) local tot,o,S,H,swap,d;
  tot:=0;
  for o in Orbits(P,Combinations(X,2),OnSets) do
    S:=o[1]; H:=Stabilizer(P,S,OnSets);
    swap:=ForAny(H,g->S[1]^g=S[2]);
    if not swap then d:=h1^2;
    elif p=2 then d:=h1*(h1+1)/2;   # symmetric coinvariants
    else d:=h1*(h1-1)/2; fi;        # exterior coinvariants (Koszul sign)
    tot:=tot+d;
  od; return tot;
end;
test:=function(R,P,p) local X,W,hR,hP,pred,orbs,o,Px,real;
  X:=MovedPoints(P); W:=WreathProduct(R,P);
  hR:=hdims(R,p); hP:=hdims(P,p); orbs:=Orbits(P,X);
  pred:=hR[2]*Length(orbs)+twoset(P,X,hR[1],p)+hP[2];
  for o in orbs do Px:=Stabilizer(P,o[1]); pred:=pred+hR[1]*hdims(Px,p)[1]; od;
  real:=hdims(W,p)[2];
  Print("R of order ",Size(R)," wr P of order ",Size(P)," on ",Length(X)," pts, p=",p,
        ": H_2 dim ",real," predicted ",pred, "  ", real=pred, "\n");
  return real=pred;
end;
ok:=true;
for p in [2,3,5] do
 for R in [CyclicGroup(IsPermGroup,2),CyclicGroup(IsPermGroup,3),CyclicGroup(IsPermGroup,4),
           CyclicGroup(IsPermGroup,5),SymmetricGroup(3),DirectProduct(CyclicGroup(IsPermGroup,2),CyclicGroup(IsPermGroup,2))] do
  for P in [Group((1,2)),Group((1,2,3)),SymmetricGroup(3),AlternatingGroup(4),Group((1,2,3,4,5)),AlternatingGroup(5)] do
    if Size(R)^NrMovedPoints(P)*Size(P) <= 2000 then ok:=test(R,P,p) and ok; fi;
  od; od; od;
Print("all agree: ",ok,"\n");
QUIT;
