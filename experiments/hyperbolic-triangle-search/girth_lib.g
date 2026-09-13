# Girth of the coset graph Gamma(A; E1, E2): vertices right cosets E1 g, E2 g; edges g in A.
CosetGraphGirth := function(A, E1, E2)
  local T1, T2, n1, n2, adj, g, a, b, dist, par, queue, head, u, w, best;
  T1 := RightTransversal(A, E1); T2 := RightTransversal(A, E2);
  n1 := Length(T1); n2 := Length(T2);
  adj := List([1..n1+n2], i -> []);
  for g in A do
    a := PositionCanonical(T1, g); b := n1 + PositionCanonical(T2, g);
    Add(adj[a], b); Add(adj[b], a);
  od;
  dist := ListWithIdenticalEntries(n1+n2, -1);
  par := ListWithIdenticalEntries(n1+n2, 0);
  dist[1] := 0; queue := [1]; head := 1; best := infinity;
  while head <= Length(queue) do
    u := queue[head]; head := head + 1;
    if 2*dist[u] + 1 >= best then break; fi;
    for w in adj[u] do
      if dist[w] = -1 then
        dist[w] := dist[u] + 1; par[w] := u; Add(queue, w);
      elif w <> par[u] then
        best := Minimum(best, dist[u] + dist[w] + 1);
      fi;
    od;
  od;
  return best;
end;
