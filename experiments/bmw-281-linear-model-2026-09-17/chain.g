# G on 3^N points; Sec0(G,M): stabilizer of block [1..M/3] and its action on it
Sec0 := function(G, M)
  local B, S, hom;
  B := [1..M/3];
  S := Stabilizer(G, B, OnSets);
  return Group(List(GeneratorsOfGroup(S), g -> RestrictedPerm(g, B)));
end;
Chain := function(G, N)
  local M, H, k, res;
  M := 3^N; H := G; res := [Size(G)];
  for k in [1..N-1] do
    H := Sec0(H, M); M := M/3; Add(res, [Size(H), IsTransitive(H,[1..M])]);
  od;
  return res;
end;
