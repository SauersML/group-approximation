# The explicit L_2 of w3-107 (l2rep.log, 8 generators; words act right-to-left as in selfrep.act)
# versus phi_0(Stab_{L_2}(0)), both on level 5, computed from level 6.
Read("chain.g"); Read("g281_6.g");
W := [[0],[1],[2],[3,0,3,0,3],[3,2,3,1,3,2,3],[3,2,0,3,2,3,2,3,2,3],[3,2,3,2,3,2,3,0,2,3],[3,2,3,2,3,0,3,2,3,2,3]];
el := w -> Product(Reversed(w), a -> gens[a+1]);
L := Group(List(W, el));
Print("|L_2| on level 6 = ", Size(L), "\n");
hom := ActionHomomorphism(L, List([0..3^5-1], v -> [3*v+1..3*v+3]), OnSets);
L5 := Image(hom);
Print("|L_2| on level 5 = ", Size(L5), "\n");
S := Sec0(L, 3^6);   # phi_0(Stab_L(0)) acting on the subtree below vertex 0, i.e. level 5
Print("|phi_0(Stab_{L_2}(0))| on level 5 = ", Size(S), "\n");
# compare as subgroups of Sym(3^5): is S contained in L5?  (identical labelling of the subtree)
Print("phi_0(Stab_{L_2}(0)) <= L_2 on level 5: ", IsSubgroup(L5, S), "   index ", Size(L5)/Size(S), "\n");
Print("each of the 8 generators lies in phi_0(Stab_{L_2}(0)) mod level 5: ", List(W, w -> Image(hom, el(w)) in S), "\n");
quit;
