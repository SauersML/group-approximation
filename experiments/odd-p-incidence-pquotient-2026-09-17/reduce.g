# Reduce a p-group quotient of Gamma_p(G,b) in which J survives to a quotient
# with cyclic centre (so every faithful irreducible representation sends J to a
# primitive p-th root of unity times I), and re-verify all relators on images.
Read("pq.g");
Reduce := function(hom, jimg, p)
  local H, Z1, N, nat, pc, ex, k;
  H := Image(hom);
  repeat
    Z1 := Omega(Centre(H), p, 1);
    Print("  |H|=", p, "^", Length(Factors(Size(H))), " |Omega1 Z|=", p, "^", Length(Factors(Size(Z1))), "\n");
    if Size(Z1) > p then
      pc := Pcgs(Z1); ex := ExponentsOfPcElement(pc, jimg);
      k := PositionProperty(ex, a -> a <> 0);
      N := SubgroupNC(H, pc{Difference([1..Length(pc)], [k])});
      nat := NaturalHomomorphismByNormalSubgroupNC(H, N);
      hom := hom*nat; jimg := Image(nat, jimg); H := Image(nat);
    fi;
  until Size(Z1) = p;
  return [hom, jimg];
end;

ReduceAndVerify := function(name, nv, edges, p, c)
  local G, ne, hom, jimg, r, H, imgs, ok;
  G := SolGroup(nv, edges, p, [1]); ne := G[2]; G := G[1];
  hom := EpimorphismPGroup(G, p, c);
  jimg := Image(hom, GeneratorsOfGroup(G)[ne+1]);
  r := Reduce(hom, jimg, p);
  hom := r[1]; jimg := r[2]; H := Image(hom);
  Print(name, " p=", p, ": reduced order ", p, "^", Length(Factors(Size(H))),
        ", |Z|=", Size(Centre(H)), ", J nontrivial ", not IsOne(jimg),
        ", class ", NilpotencyClassOfGroup(H), ", exponent ", Exponent(H), "\n");
  imgs := List(GeneratorsOfGroup(G), g -> Image(hom, g));
  ok := ForAll(RelatorsOfFpGroup(G), rr -> IsOne(MappedWord(rr, FreeGeneratorsOfFpGroup(G), imgs)));
  Print("  all relators hold on images: ", ok, "\n");
  return [H, imgs, jimg];
end;
