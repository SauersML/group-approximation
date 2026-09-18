# GAP: index-4 subgroups of Radu's BMW lattice and a presentation of pi_1(S_R) = ker(Gamma_R -> C2 x C2).
# Recorded output (2026-09-17): exactly two index-4 subgroups pass the torsion-free test, both with H1 = [0] (= Z);
#   F1 = b*a^-1, F2 = y*x^-1; relators
#   F2*F1^-1*F2^-2*F1^2*F2^2*F1^-1*F2^-1*F1 and F1*F2^-2*F1^-1*F2*F1*F2^-1*F1^-1*F2^2*F1;
#   relators hold: [ true, true ]; index of <F1,F2>: 4.
# Independent checks: radu_relators_normal_form.py, radu_kernel_not_locally_indicable.py.
F := FreeGroup("a","b","c","x","y","z");;
a:=F.1;;b:=F.2;;c:=F.3;;x:=F.4;;y:=F.5;;z:=F.6;;
G := F/[a^2,b^2,c^2,x^2,y^2,z^2,a*x*a*x,a*y*a*y,a*z*b*z,b*x*b*x,b*y*c*y,c*x*c*z];;
gg := GeneratorsOfGroup(G);;
tors := [gg[1],gg[2],gg[3],gg[4],gg[5],gg[6],gg[1]*gg[4],gg[1]*gg[5],gg[2]*gg[4]];;
L := LowIndexSubgroupsFpGroup(G, 4);;
for H in L do
  if Index(G,H) = 4 then
    act := FactorCosetAction(G,H);;
    tf := ForAll(tors, t -> Length(MovedPoints(Image(act,t))) = 4);
    Print("index 4 subgroup, torsion-free test: ", tf, " H1 ", AbelianInvariants(H), "\n");
  fi;
od;
hom := GroupHomomorphismByImages(G, Group((1,2),(3,4)), gg, [(1,2),(1,2),(1,2),(3,4),(3,4),(3,4)]);;
K := Kernel(hom);;
iso := IsomorphismFpGroup(K);; P := Image(iso);;
p := List(GeneratorsOfGroup(P), q -> PreImagesRepresentative(iso, q));;
Print("F1 = ", UnderlyingElement(p[1]), "\nF2 = ", UnderlyingElement(p[2]), "\n");
Print("rels ", RelatorsOfFpGroup(P), "\n");
# verify the relators hold on the preimages
r := RelatorsOfFpGroup(P);;
Print("relators hold: ", List(r, w -> MappedWord(w, FreeGeneratorsOfFpGroup(P), p) = One(G)), "\n");
# check F1, F2 generate K (index 4 check)
Print("index of <F1,F2>: ", Index(G, Subgroup(G, p)), "\n");
QUIT;
