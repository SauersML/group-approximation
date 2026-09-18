# Lower exponent-2 central quotients G_k of H4(n), n = 3,5,7, classes 1..6.
# Records log2|G_k|, log2|A_k| (A=<a,c>), log2|B_k| (B=<b,d>), |A_k cap B_k|, generator orders,
# and log2|F_2/P_k(F_2)| for comparison (free pro-2 group on 2 generators).
F:=FreeGroup("a","b","c","d");; a:=F.1;;b:=F.2;;c:=F.3;;d:=F.4;;
F2:=FreeGroup(2);; K:=6;;
Pf:=EpimorphismPGroup(F2,2,K);; If:=Image(Pf);; Lf:=PCentralSeries(If,2);;
Print("free rank-2 log2|F/P_k| = ",List([1..K],k->Log(Size(If)/Size(Lf[k+1]),2)),"\n");
for n in [3,5,7] do
  rels:=[b^a*b^-n, c^b*c^-n, d^c*d^-n, a^d*a^-n];;
  G:=F/rels;; P:=EpimorphismPGroup(G,2,K);; I:=Image(P);;
  g:=List(GeneratorsOfGroup(G),x->Image(P,x));; L:=PCentralSeries(I,2);;
  for k in [1..Length(L)-1] do
    h:=NaturalHomomorphismByNormalSubgroup(I,L[k+1]);
    gg:=List(g,x->Image(h,x)); A:=Group(gg[1],gg[3]); B:=Group(gg[2],gg[4]);
    Print("n=",n," k=",k," log2|G|=",Log(Size(Image(h)),2)," log2|A|=",Log(Size(A),2),
      " log2|B|=",Log(Size(B),2)," |AcapB|=",Size(Intersection(A,B))," ord=",List(gg,Order),"\n");
  od;
od;
