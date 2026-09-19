# Admissible Hecke-splitting block for (MUI-O) at q = 2 (lane w13-121, 2026-09-18).
# Gamma-bar = SL_3(F_2[e]/e^2) = image of Gamma = EL_3(F_2[x_1..x_d]) under x_2 -> e, x_i -> 0 (i != 2).
# Lambda-bar = SL_3(F_2) = image of Lambda_t, t: x_2 -> x_1 x_2 (compressor I + E_12).
# Enumerates H <= Gamma-bar with Lambda-bar transitive on Gamma-bar/H of size 28, via
# M = pi(H) of order 24, V = H cap K an M-invariant subgroup of K = ker(Gamma-bar -> SL_3(F_2)),
# and complements to K/V in (K M)/V. Prints orbit data on pairs and automorphism groups.
# Run: nice -n 10 timeout 1200 gap -q -o 2g dual-number-antiflag-block-2026-09-18.g < /dev/null
F:=GF(2);; o:=One(F);; z:=Zero(F);;
emb:=function(M) local R,i,j; R:=NullMat(6,6,F);
  for i in [1..3] do for j in [1..3] do
    R[2*i-1][2*j-1]:=M[i][j][1]; R[2*i-1][2*j]:=M[i][j][2]; R[2*i][2*j]:=M[i][j][1];
  od; od; return R; end;;
Elm:=function(i,j,c) local M,k; M:=List([1..3],k->List([1..3],l->[z,z]));
  for k in [1..3] do M[k][k]:=[o,z]; od; M[i][j]:=c; return emb(M); end;;
gensL:=[];; gensG:=[];;
for i in [1..3] do for j in [1..3] do if i<>j then
  Add(gensL,Elm(i,j,[o,z])); Add(gensG,Elm(i,j,[o,z])); Add(gensG,Elm(i,j,[z,o])); fi; od; od;
G:=Group(gensG);; L:=Group(gensL);;
red:=A->List([1..3],i->List([1..3],j->A[2*i-1][2*j-1]));;
iso:=IsomorphismPermGroup(G);; Gp:=Image(iso);; Lp:=Image(iso,L);;
Kp:=Group(List(Filtered(Elements(G),x->red(x)=IdentityMat(3,F)),x->Image(iso,x)));;
Print("|Gamma-bar|=",Size(Gp)," |K|=",Size(Kp)," |Lambda-bar|=",Size(Lp),"\n");
els:=Elements(Lp);; subs:=[];;
for a in els do for b in els do S:=Group(a,b);
  if Size(S)=24 and ForAll(subs,T->not IsConjugate(Lp,S,T)) then Add(subs,S); fi; od; od;
pc:=Pcgs(Kp);; vec:=k->ExponentsOfPcElement(pc,k)*One(F);;
for M in subs do
  mats:=List(GeneratorsOfGroup(M),m->List(pc,p->vec(p^m)));;
  P:=ClosureGroup(Kp,M);;
  for W in Combinations(Filtered(Elements(F^8),f->not IsZero(f)),2) do
    if RankMat(W)<2 or ForAny(mats,A->ForAny(W,f->RankMat(Concatenation(W,[A*f]))>2)) then continue; fi;
    V:=Group(Concatenation([()],Filtered(Elements(Kp),k->ForAll(W,f->IsZero(vec(k)*f)))));;
    hom:=NaturalHomomorphismByNormalSubgroup(P,V);;
    for Cc in ComplementClassesRepresentatives(Image(hom),Image(hom,Kp)) do
      H:=PreImage(hom,Cc);; if Size(Gp)/Size(H)<>28 then continue; fi;
      if Size(Intersection(H,Lp))<>6 then continue; fi;   # Lambda-bar transitive on 28 points
      act:=FactorCosetAction(Gp,H);; img:=Image(act);; Limg:=Image(act,Lp);;
      prs:=Cartesian([1..28],[1..28]);;
      Print("BLOCK: |H|=",Size(H)," |H cap K|=",Size(V)," |H cap Lambda|=6  faithful=",Size(img)=Size(Gp),"\n");
      Print("  Gamma-bar pair orbits:  ",SortedList(List(OrbitsDomain(img,prs,OnPairs),Length)),"\n");
      Print("  Lambda-bar pair orbits: ",SortedList(List(OrbitsDomain(Limg,prs,OnPairs),Length)),"\n");
      Print("  |Aut_Gamma|=",Size(Centralizer(SymmetricGroup(28),img)),
            "  |Aut_Lambda|=",Size(Centralizer(SymmetricGroup(28),Limg)),"\n");
    od;
  od;
od;
Print("done\n");
QUIT;
