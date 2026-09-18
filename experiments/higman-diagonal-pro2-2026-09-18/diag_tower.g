# H4(3)/<<[a,c]^2>>, lower exponent-2 central quotients G_k up to class K.
# Per class: generator orders, log2|A_k|, log2|B_k|, A_k^ab, B_k^ab, and the least j
# with x^(2^j) in the opposite pair for x = a,c (in B_k) and x = b,d (in A_k).
# A value j < log2 ord(x) means a NONTRIVIAL power of x lies in the opposite edge group.
K:=11;;
F:=FreeGroup("a","b","c","d");; a:=F.1;;b:=F.2;;c:=F.3;;d:=F.4;;
n:=3;; rels:=[b^a*b^-n, c^b*c^-n, d^c*d^-n, a^d*a^-n];;
G:=F/Concatenation(rels,[Comm(a,c)^2]);;
P:=EpimorphismPGroup(G,2,K);; I:=Image(P);;
g:=List(GeneratorsOfGroup(G),x->Image(P,x));; L:=PCentralSeries(I,2);;
firstpow:=function(x,H) local j; j:=0; while not x^(2^j) in H do j:=j+1; od; return j; end;;
for k in [1..Length(L)-1] do
  h:=NaturalHomomorphismByNormalSubgroup(I,L[k+1]);
  gg:=List(g,x->Image(h,x)); A:=Group(gg[1],gg[3]); B:=Group(gg[2],gg[4]);
  Print("k=",k," log2|G|=",Log(Size(Image(h)),2)," log2ord=",List(gg,x->Log(Order(x),2)),
    " log2|A|=",Log(Size(A),2)," log2|B|=",Log(Size(B),2),
    " A^ab=",AbelianInvariants(A)," B^ab=",AbelianInvariants(B),
    " j(b,d in A)=",[firstpow(gg[2],A),firstpow(gg[4],A)],
    " j(a,c in B)=",[firstpow(gg[1],B),firstpow(gg[3],B)],"\n");
od;
QUIT;
