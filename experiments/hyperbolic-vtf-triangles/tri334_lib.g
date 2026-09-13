# Chamber-transitive triangles of groups of type (A6, L3(2), L3(2)): edge groups S4, face D8.
# Links: A6 on GQ(2,2) (duads/synthemes), L3(2) on PG(2,2) (points/lines).

# Girth of the coset graph Gamma(X; P, L) with face group B = P meet L: vertices cosets Pg, Lg,
# adjacency deduplicated (edges are cosets Bg).
CosetGraphGirthFace := function(X, P, L)
  local T1, T2, n1, adj, g, a, b, dist, par, queue, head, u, w, best;
  T1 := RightTransversal(X, P); T2 := RightTransversal(X, L); n1 := Length(T1);
  adj := List([1..n1 + Length(T2)], i -> []);
  for g in X do
    a := PositionCanonical(T1, g); b := n1 + PositionCanonical(T2, g);
    AddSet(adj[a], b); AddSet(adj[b], a);
  od;
  dist := ListWithIdenticalEntries(Length(adj), -1); par := ListWithIdenticalEntries(Length(adj), 0);
  dist[1] := 0; queue := [1]; head := 1; best := infinity;
  while head <= Length(queue) do
    u := queue[head]; head := head + 1;
    for w in adj[u] do
      if dist[w] = -1 then dist[w] := dist[u] + 1; par[w] := u; Add(queue, w);
      elif w <> par[u] then best := Minimum(best, dist[u] + dist[w] + 1); fi;
    od;
  od;
  return [best, List(adj{[1]}, Length)[1], Length(adj[n1 + 1])];
end;

# Isomorphisms h: S -> T (as GAP homomorphisms) with Image(h, BS) = BT.
IsosMappingFace := function(S, T, BS, BT)
  local base, auts;
  base := IsomorphismGroups(S, T);
  auts := AsList(AutomorphismGroup(T));
  return Filtered(List(auts, a -> base * a), h -> Image(h, BS) = BT);
end;

# Scan F for y such that [sa, sb, y] satisfies the relators of X in generators [a, b, y0].
ExtendByScan := function(F, rels, fgens, sa, sb, ord7class, size)
  local res, c, y, w, ok;
  res := [];
  for c in ord7class do for y in c do
    ok := true;
    for w in rels do
      if MappedWord(w, fgens, [sa, sb, y]) <> () then ok := false; break; fi;
    od;
    if ok and Size(Group(sa, sb, y)) = size then Add(res, y); fi;
  od; od;
  return res;
end;
