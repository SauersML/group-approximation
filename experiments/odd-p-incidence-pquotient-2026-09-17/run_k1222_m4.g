# Output: k1222_m4.out / k1222_m9.out.  K_{1,2,2,2} over Z_m (m = q^a): order of J in the
# largest q-quotients of class <= maxc.  Order m of J forces m | fold of any planar cover.
OnBreak := function() FORCE_QUIT_GAP(3); end;
Read("pq.g");
part := [1,2,2,3,3,4,4];
k1222 := Filtered(Combinations([1..7], 2), e -> part[e[1]] <> part[e[2]]);
TestOrd := function(name, nv, edges, m, q, maxc)
  local G, ne, c, hom, img, H;
  G := SolGroup(nv, edges, m, [1]); ne := G[2]; G := G[1];
  for c in [1..maxc] do
    hom := EpimorphismPGroup(G, q, c);
    H := Image(hom);
    img := Image(hom, GeneratorsOfGroup(G)[ne+1]);
    Print(name, " m=", m, " class<=", c, " |P|=", q, "^", Length(Factors(Size(H))),
          " order of J: ", Order(img), "\n");
    if Order(img) = m then return true; fi;
  od;
  return false;
end;
TestOrd("K1222", 7, k1222, 4, 2, 6);
QUIT;
