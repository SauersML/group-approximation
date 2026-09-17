OnBreak := function() FORCE_QUIT_GAP(3); end;
Read("pq.g"); Read("graphs.g");
girth := function(nv, E) local adj, best, s, dist, par, q, u, w, e;
  adj := List([1..nv], v -> []);
  for e in E do Add(adj[e[1]], e[2]); Add(adj[e[2]], e[1]); od;
  best := infinity;
  for s in [1..nv] do
    dist := List([1..nv], v -> -1); par := List([1..nv], v -> 0); dist[s] := 0; q := [s];
    while Length(q) > 0 do u := Remove(q, 1);
      for w in adj[u] do
        if dist[w] = -1 then dist[w] := dist[u]+1; par[w] := u; Add(q, w);
        elif par[u] <> w then best := Minimum(best, dist[u]+dist[w]+1); fi;
      od;
    od;
  od;
  return [best, Set(List(adj, Length))];
end;
Print("girth/degrees: pappus ", girth(18, pappus), " desargues ", girth(20, desargues), " tutte8 ", girth(30, tutte8cage), " heawood ", girth(14, heawood), " MK ", girth(16, moebiuskantor), " petersen ", girth(10, petersen), "\n");
TestJ("Pappus", 18, pappus, 3, 3);
TestJ("Desargues", 20, desargues, 3, 3);
TestJ("Tutte8cage", 30, tutte8cage, 3, 3);
QUIT;
