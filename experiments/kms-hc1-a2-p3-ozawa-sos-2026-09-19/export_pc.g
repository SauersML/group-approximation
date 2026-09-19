# Fast export of Q_K = Gamma_3/P_K (P_K = lower exponent-3 central series) for qball.py.
# Uses a pcgs through the 3-central series: T[i] = product of the top pcgs elements with exponent
# vector e (i = sum e_k 3^(k-1), so T[0] = 1), A = P_J/P_K = span of the tail (elementary abelian).
# Output lines: R x i j exps  with T[i]*x = al*T[j], al in A (the same format as the transversal export).
SizeScreen([4000,1000]);;
F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
cm:=function(x,y) return x^-1*y^-1*x*y; end;;
rels:=[a^3,b^3,c^3,cm(cm(a,b),a),cm(cm(a,b),b),cm(cm(b,c),b),cm(cm(b,c),c),cm(cm(a,c),a),cm(cm(a,c),c)];;
G:=F/rels;;
epi:=EpimorphismPGroup(G,3,K-1);; Q:=Image(epi);;
gens:=List(GeneratorsOfGroup(G),g->Image(epi,g));;
ser:=PCentralSeries(Q,3);;
pcgs:=PcgsPCentralSeriesPGroup(Q);; n:=Length(pcgs);;
A:=ser[J];; d:=LogInt(Index(Q,A),3);;
if not IsElementaryAbelian(A) then Error("A not elementary abelian"); fi;
if Group(pcgs{[d+1..n]})<>A then Error("tail is not A"); fi;
if ForAny(RelativeOrders(pcgs),r->r<>3) then Error("rel orders"); fi;
Print("# |Q_",K,"| = 3^",n," increments ",List([1..Length(ser)-1],i->LogInt(Index(ser[i],ser[i+1]),3)),"\n");
Print("ORDS ",List([d+1..n],x->3),"\n");
m:=3^d;; Print("M ",m,"\n");
top:=pcgs{[1..d]};;
for x in [1..3] do
  e:=List([1..d],k->0);;
  for i in [0..m-1] do
    t:=i;; for k in [1..d] do e[k]:=t mod 3;; t:=(t-e[k])/3;; od;
    Ti:=Product([1..d],k->top[k]^e[k]);;
    g:=Ti*gens[x];; ex:=ExponentsOfPcElement(pcgs,g);;
    j:=Sum([1..d],k->ex[k]*3^(k-1));;
    Tj:=Product([1..d],k->top[k]^ex[k]);;
    al:=g*Tj^-1;; ea:=ExponentsOfPcElement(pcgs,al);;
    if ForAny([1..d],k->ea[k]<>0) then Error("al not in A"); fi;
    Print("R ",x," ",i," ",j," ",ea{[d+1..n]},"\n");
  od;
od;
QUIT;
