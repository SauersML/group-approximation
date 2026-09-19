# Exact rank-2 check for A = <u,v>, u = bcba, v = babc (u v = v u is proved in Gamma_3 by tube.py).
# If A were virtually cyclic it would be Z x F with F <= (Z/3)^2 (finite abelian subgroups lie in
# vertex-group conjugates, Heisenberg of order 27), and every quotient of Z x F has at most one
# cyclic factor of order >= 9.  So two abelian invariants >= 9 of the image of A in Gamma_3/P_K
# prove A ~= Z^2 (virtually).
SizeScreen([4000,1000]);;
F:=FreeGroup("a","b","c");; a:=F.1;; b:=F.2;; c:=F.3;;
cm:=function(x,y) return x^-1*y^-1*x*y; end;;
rels:=[a^3,b^3,c^3,cm(cm(a,b),a),cm(cm(a,b),b),cm(cm(b,c),b),cm(cm(b,c),c),cm(cm(a,c),a),cm(cm(a,c),c)];;
G:=F/rels;;
for K in [5..8] do
  epi:=EpimorphismPGroup(G,3,K-1);; Q:=Image(epi);;
  g:=List(GeneratorsOfGroup(G),x->Image(epi,x));;
  u:=g[2]*g[3]*g[2]*g[1];; v:=g[2]*g[1]*g[2]*g[3];;
  Print("K=",K," |Q|=3^",LogInt(Size(Q),3)," [u,v]=1: ",Comm(u,v)=One(Q),
        " ord u,v,vu^-1: ",Order(u)," ",Order(v)," ",Order(v*u^-1)," invariants of <u,v>: ",AbelianInvariants(Subgroup(Q,[u,v])),"\n");
od;
QUIT;
