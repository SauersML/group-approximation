# Example: G = <x,y | w>, w = x y^4 x^-1 y^-1 x y^2 x^-1 y^-5, H = <x, y^2, y x y x^-1 y^-1>.
# Find finite-index subgroups K >= H of G in which the vertices 0,1,2 of Gamma (tree paths 1, y, y x) are distinct cosets.
F:=FreeGroup("x","y");; x:=F.1;; y:=F.2;;
w:=x*y^4*x^-1*y^-1*x*y^2*x^-1*y^-5;;
G:=F/[w];; gx:=G.1;; gy:=G.2;;
H:=Subgroup(G,[gx,gy^2,gy*gx*gy*gx^-1*gy^-1]);;
L:=LowIndexSubgroupsFpGroup(G,H,8);;
Print("subgroups of index <=8 containing H: ",Length(L),"\n");
for K in L do
  if not gy in K and not gy*gx in K and not (gy*gx)*gy^-1 in K then
    Print("index ",Index(G,K)," separates the three vertices\n");
  fi;
od;
Print("done\n");
QUIT;
