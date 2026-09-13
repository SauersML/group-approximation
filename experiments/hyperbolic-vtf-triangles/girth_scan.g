# Girth of the coset graph Gamma(A; <x>, <y>) for elements x, y of order 7.
# Vertices: right cosets E1 g and E2 g; edges: g in A, joining E1 g and E2 g.
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

ScanGroup := function(name, A, samples)
  local els7, x, E1, y, E2, tally, i, gi, gen, key, res;
  els7 := Filtered(AsList(A), g -> Order(g) = 7);
  x := els7[1]; E1 := Subgroup(A, [x]);
  tally := rec();
  for i in [1..Minimum(samples, Length(els7))] do
    y := Random(els7);
    if y in E1 then continue; fi;
    E2 := Subgroup(A, [y]);
    gen := Size(Subgroup(A, [x, y])) = Size(A);
    gi := CosetGraphGirth(A, E1, E2);
    key := Concatenation("girth", String(gi), "_gen", String(gen));
    if IsBound(tally.(key)) then tally.(key) := tally.(key) + 1; else tally.(key) := 1; fi;
  od;
  Print(name, " |A|=", Size(A), " #ord7=", Length(els7), " ", tally, "\n");
end;

ScanGroup("PSL(2,8)", Image(IsomorphismPermGroup(PSL(2,8))), 60);
ScanGroup("A7", AlternatingGroup(7), 60);
ScanGroup("PSL(2,13)", Image(IsomorphismPermGroup(PSL(2,13))), 60);
ScanGroup("A8", AlternatingGroup(8), 60);
ScanGroup("PSL(2,27)", Image(IsomorphismPermGroup(PSL(2,27))), 40);
ScanGroup("PSL(2,29)", Image(IsomorphismPermGroup(PSL(2,29))), 30);
Print("DONE\n");
QUIT;
