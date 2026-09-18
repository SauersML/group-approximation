# Output: sylow_k44.out
# K44, p=3.  Explicit epimorphisms Gamma -> T killing J, factoring through the deletion of the
# 8 edges between the 4-cycles {1,2,5,6} and {3,4,7,8}: x_(1,5)=x_(2,6)=g, x_(1,6)=x_(2,5)=g^-1,
# x_(3,7)=x_(4,8)=h, x_(3,8)=x_(4,7)=h^-1, all other edges and J -> 1.
# For T = <g,h> non-3-group, U = preimage of a Sylow 3-subgroup; test J in 3-quotients of U.
OnBreak := function() FORCE_QUIT_GAP(3); end;
Read("pq.g"); Read("graphs.g");
p := 3;
G := SolGroup(8, k44, p, [1]); ne := G[2]; G := G[1];
gens := GeneratorsOfGroup(G); J := gens[ne+1];
TestPair := function(name, g, h, maxc)
  local T, imgs, hom, S, U, iso, Ufp, jU, c, q, t0;
  T := Group(g, h);
  imgs := List([1..ne+1], i -> One(T));
  imgs[1] := g; imgs[6] := g; imgs[2] := g^-1; imgs[5] := g^-1;
  imgs[11] := h; imgs[16] := h; imgs[12] := h^-1; imgs[15] := h^-1;
  if not ForAll(RelatorsOfFpGroup(G), r -> IsOne(MappedWord(r, FreeGeneratorsOfFpGroup(G), imgs))) then
    Print(name, ": not a homomorphism\n"); return;
  fi;
  hom := GroupHomomorphismByImagesNC(G, T, gens, imgs);
  S := SylowSubgroup(T, p);
  U := PreImage(hom, S);
  iso := IsomorphismFpGroup(U);
  Ufp := Range(iso); jU := Image(iso, J);
  Print(name, " |T|=", Size(T), " U index ", Index(G, U), ", ", Length(GeneratorsOfGroup(Ufp)),
        " gens\n");
  for c in [1..maxc] do
    t0 := Runtime();
    q := EpimorphismPGroup(Ufp, p, c);
    Print("   class<=", c, " |P|=3^", Length(Factors(Size(Image(q)))),
          " J nontrivial: ", not IsOne(Image(q, jU)), " (", Runtime()-t0, "ms)\n");
    if not IsOne(Image(q, jU)) then return; fi;
  od;
end;
TestPair("A4", (1,2,3), (1,2,4), 4);
TestPair("A5", (1,2,3), (1,4,5), 3);
QUIT;
