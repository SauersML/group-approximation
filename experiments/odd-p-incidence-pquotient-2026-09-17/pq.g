# Solution group Gamma_p(G,b) of the oriented incidence system of a graph G.
# edges: list of [tail,head]; b: one vertex gets 1, rest 0.
SolGroup := function(nv, edges, p, bv)
  local F, gens, x, J, rels, v, inc, i, j, w, ne;
  ne := Length(edges);
  F := FreeGroup(ne+1);
  gens := GeneratorsOfGroup(F);
  x := gens{[1..ne]}; J := gens[ne+1];
  rels := [J^p];
  for i in [1..ne] do Add(rels, x[i]^p); Add(rels, Comm(x[i],J)); od;
  for v in [1..nv] do
    inc := Filtered([1..ne], i -> v in edges[i]);
    for i in inc do for j in inc do if i<j then Add(rels, Comm(x[i],x[j])); fi; od; od;
    w := One(F);
    for i in inc do
      if edges[i][2]=v then w := w*x[i]; else w := w*x[i]^-1; fi;
    od;
    if v in bv then w := w*J^-1; fi;
    Add(rels, w);
  od;
  return [F/rels, ne];
end;

TestJ := function(name, nv, edges, p, maxc)
  local G, ne, c, qs, hom, img, H;
  G := SolGroup(nv, edges, p, [1]); ne := G[2]; G := G[1];
  for c in [1..maxc] do
    hom := EpimorphismPGroup(G, p, c);
    H := Image(hom);
    img := Image(hom, GeneratorsOfGroup(G)[ne+1]);
    Print(name, " p=", p, " class<=", c, " |P|=", p, "^", Length(Factors(Size(H))) , " J nontrivial: ", not IsOne(img), "\n");
    if not IsOne(img) then return true; fi;
  od;
  return false;
end;

# Heawood graph, LCF [5,-5]^7
heawood := Concatenation(List([0..13], i -> [i+1, ((i+1) mod 14)+1]),
   List([0,2..12], i -> [i+1, ((i+5) mod 14)+1]));
k33 := List(Cartesian([1..3],[4..6]), e -> e);
cube := [[1,2],[2,3],[3,4],[4,1],[5,6],[6,7],[7,8],[8,5],[1,5],[2,6],[3,7],[4,8]];
