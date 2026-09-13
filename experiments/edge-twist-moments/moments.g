# moments.g -- edge-twist moment test (edge-twist-extensions-of-triangle-colimits-moment-test)
# on coset triangles inside a finite group Q: three elements x1,x2,x3 of prime order p give
# vertex groups A1=<x1,x2>, A2=<x1,x3>, A3=<x2,x3>, edge groups <x1> (12), <x2> (13), <x3> (23).
# Their colimit maps onto G=<x1,x2,x3> injectively on vertex groups. For N = kernel we compute
#   dim Z_N   (2-cycles: functions on G summing to 0 on every right coset <x_e> g)
#   dim I_N   (image of the three first moments on Z_N) = rank([B; mu]) - rank(B).
# Girths of the three links are computed by BFS on the coset graphs; only hyperbolic
# triples (sum of 2/girth < 1) are tested.

# Girth of Gamma(A; E1, E2), verbatim from experiments/hyperbolic-vtf-triangles/girth_lib.g.
CosetGraphGirthSub := function(A, E1, E2)
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
CosetGraphGirth := function(A, a, b) return CosetGraphGirthSub(A, Group(a), Group(b)); end;

MomentTest := function(G, xs, p)
    local L, n, F, rows, mus, e, x, E, seen, g, c0, k, row, mu, rB, rBmu, i, pos, mat;
    L := AsSSortedList(G); n := Length(L); F := GF(p);
    rows := []; mus := [];
    for e in [1..3] do
        x := xs[e]; E := Group(x);
        seen := BlistList([1..n], []);
        mu := ListWithIdenticalEntries(n, Zero(F));
        for i in [1..n] do
            if seen[i] then continue; fi;
            g := L[i];
            row := ListWithIdenticalEntries(n, Zero(F));
            for k in [0..p-1] do
                pos := PositionSorted(L, x^k * g);
                seen[pos] := true; row[pos] := One(F); mu[pos] := k * One(F);
            od;
            Add(rows, row);
        od;
        Add(mus, mu);
    od;
    mat := ImmutableMatrix(F, rows);
    rB := RankMat(mat);
    rBmu := RankMat(ImmutableMatrix(F, Concatenation(rows, mus)));
    return rec(n := n, rankB := rB, dimZ := n - rB, dimI := rBmu - rB);
end;

RunFamily := function(Q, p, trials, maxtests)
    local cl, x0, t, xs, A, girths, G, res, tested;
    x0 := First(ConjugacyClasses(Q), c -> Order(Representative(c)) = p);
    x0 := Representative(x0);
    tested := 0;
    for t in [1..trials] do
        xs := List([1..3], i -> x0^Random(Q));
        if Length(Set(List(xs, x -> Group(x)))) < 3 then continue; fi;
        girths := [CosetGraphGirth(Group(xs[1], xs[2]), xs[1], xs[2]),
                   CosetGraphGirth(Group(xs[1], xs[3]), xs[1], xs[3]),
                   CosetGraphGirth(Group(xs[2], xs[3]), xs[2], xs[3])];
        if Sum(girths, g -> 2 / g) >= 1 then continue; fi;
        G := Group(xs);
        res := MomentTest(G, xs, p);
        A := [Size(Group(xs[1], xs[2])), Size(Group(xs[1], xs[3])), Size(Group(xs[2], xs[3]))];
        # chi(N\X) = n (1 - 3/p + sum 1/|A_v|) = 1 - b1 + b2 over F_p, and b2 = dimZ
        Print("Q=", StructureDescription(Q), " p=", p, " girths=", girths, " |A_v|=", A,
              " |G|=", res.n, " dimZ=", res.dimZ, " dimI=", res.dimI,
              " b1(N;F_p)=", res.dimZ + 1 - res.n * (1 - 3/p + Sum(A, a -> 1/a)), "\n");
        tested := tested + 1;
        if tested >= maxtests then return; fi;
    od;
end;
