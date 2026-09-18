# Theorem O calibration: H4(3)/<<[a,c]^2>>, lower exponent-2 central quotients.
# Prediction: A=<a,c> is not free, so (item 1) a^Y in A' for a fixed Y, hence
# ord(a in A_k^ab) bounded and b^(2^s), d^(2^s) in A_k for a fixed s = v_2(3^Y-1).
F:=FreeGroup("a","b","c","d");; a:=F.1;;b:=F.2;;c:=F.3;;d:=F.4;;
n:=3;; rels:=[b^a*b^-n, c^b*c^-n, d^c*d^-n, a^d*a^-n];;
extra:=[Comm(a,c)^2];;
G:=F/Concatenation(rels,extra);;
P:=EpimorphismPGroup(G,2,10);; I:=Image(P);;
g:=List(GeneratorsOfGroup(G),x->Image(P,x));;
L:=PCentralSeries(I,2);; Print(List(L,x->Log(Size(x),2)),"\n");
firstpow:=function(x,H) local j; j:=0; while not x^(2^j) in H do j:=j+1; od; return j; end;;
for k in [1..Length(L)-1] do
  h:=NaturalHomomorphismByNormalSubgroup(I,L[k+1]);
  gg:=List(g,x->Image(h,x)); A:=Group(gg[1],gg[3]);
  ab:=AbelianInvariants(A);
  Print(k," log2|A|=",Log(Size(A),2)," A^ab=",ab," ord=",List(gg,Order),
        " b^2^s in A: s=",firstpow(gg[2],A)," d: s=",firstpow(gg[4],A),"\n");
od;
