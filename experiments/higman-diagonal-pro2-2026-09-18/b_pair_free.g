# H4(3)/<<[a,c]^2>>: lower exponent-2 central quotients G_k.
# Is B=<b,d> free pro-2 (|B_k| = |F_2/P_k(F_2)|)?  Records |A_k|, |B_k|, |A_k cap B_k|,
# and log2 of the free rank-2 quotients for comparison.
K:=8;;
F2:=FreeGroup(2);; Pf:=EpimorphismPGroup(F2,2,K);; If:=Image(Pf);; Lf:=PCentralSeries(If,2);;
Print("free rank-2 log2|F/P_k| = ",List([1..K],k->Log(Size(If)/Size(Lf[k+1]),2)),"\n");
F:=FreeGroup("a","b","c","d");; a:=F.1;;b:=F.2;;c:=F.3;;d:=F.4;;
n:=3;; rels:=[b^a*b^-n, c^b*c^-n, d^c*d^-n, a^d*a^-n];;
G:=F/Concatenation(rels,[Comm(a,c)^2]);;
P:=EpimorphismPGroup(G,2,K);; I:=Image(P);;
g:=List(GeneratorsOfGroup(G),x->Image(P,x));; L:=PCentralSeries(I,2);;
for k in [1..Length(L)-1] do
  h:=NaturalHomomorphismByNormalSubgroup(I,L[k+1]);
  gg:=List(g,x->Image(h,x)); A:=Group(gg[1],gg[3]); B:=Group(gg[2],gg[4]);
  Print("k=",k," log2|G|=",Log(Size(Image(h)),2)," log2|A|=",Log(Size(A),2),
    " log2|B|=",Log(Size(B),2)," log2|AcapB|=",Log(Size(Intersection(A,B)),2),
    " B^ab=",AbelianInvariants(B),"\n");
od;
QUIT;
