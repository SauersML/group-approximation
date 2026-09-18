# Calibration: H4(3)/<<[a,c]>> and H4(3)/<<[a,c],[b,d]>>: orders of generators in 2-quotients.
F:=FreeGroup("a","b","c","d");; a:=F.1;;b:=F.2;;c:=F.3;;d:=F.4;;
n:=3;; rels:=[b^a*b^-n, c^b*c^-n, d^c*d^-n, a^d*a^-n];;
for extra in [[Comm(a,c)],[Comm(a,c),Comm(b,d)]] do
  G:=F/Concatenation(rels,extra);;
  for K in [2..9] do
    P:=EpimorphismPGroup(G,2,K);; g:=List(GeneratorsOfGroup(G),x->Image(P,x));;
    Print(extra," class ",K," log2|P|=",Log(Size(Image(P)),2)," log2ord=",
      List(g,x->Log(Order(x),2)),"\n");
  od;
od;
QUIT;
