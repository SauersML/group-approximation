# pi_1(S_JW) = K = type-preserving kernel of Gamma_JW -> Z/2 x Z/2.
# K^ab = Z x Z/3, so K has a unique normal subgroup N_j with K/N_j a 2-group of order 2^j (it is cyclic).
# Output: permutation action of Gamma_JW on the cosets of N_j (j = 1,2,3), for jw_sub_sat.py.
F:=FreeGroup("a","b","x","y");; a:=F.1;; b:=F.2;; x:=F.3;; y:=F.4;;
G:=F/[a*x*a*y, a*x^-1*b*y^-1, a*y^-1*b^-1*x^-1, b*x*b^-1*y^-1];;
Q:=Group((1,2)(3,4),(1,3)(2,4));;
hom:=GroupHomomorphismByImages(G,Q,GeneratorsOfGroup(G),[(1,2)(3,4),(1,2)(3,4),(1,3)(2,4),(1,3)(2,4)]);;
K:=Kernel(hom);;
Print("# [G:K] = ",Index(G,K),"  K^ab = ",AbelianInvariants(K),"\n");
out:=OutputTextFile("jw_2power.json",false);; SetPrintFormattingStatus(out,false);
AppendTo(out,"{");
for j in [1..3] do
  cands:=Filtered(LowIndexSubgroupsFpGroup(K,2^j), H->Index(K,H)=2^j and IsNormal(K,H) and IsPGroup(K/H));
  Print("# index 2^",j,": normal subgroups of K with 2-group quotient: ",Length(cands),"\n");
  N:=cands[1];;
  Print("#   K/N cyclic: ",IsCyclic(FactorGroup(K,N)),"  [G:N] = ",Index(G,N),"\n");
  act:=FactorCosetAction(G,N);;
  imgs:=List(GeneratorsOfGroup(G),g->ListPerm(Image(act,g),Index(G,N)));;
  # point 1 is the coset N itself: its stabiliser must be N
  st:=PreImage(act,Stabilizer(Image(act),1));;
  Print("#   stabiliser of point 1 equals N: ",st=N,"\n");
  if j>1 then AppendTo(out,","); fi;
  AppendTo(out,"\"",j,"\":",imgs);
od;
AppendTo(out,"}\n"); CloseStream(out);
QUIT;
