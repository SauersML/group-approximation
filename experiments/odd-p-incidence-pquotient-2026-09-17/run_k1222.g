# Output: k1222.out.  K_{1,2,2,2} (vertex 1 apex; parts {2,3},{4,5},{6,7}), p=3.
OnBreak := function() FORCE_QUIT_GAP(3); end;
Read("pq.g"); Read("graphs.g");
part := [1,2,2,3,3,4,4];
k1222 := Filtered(Combinations([1..7], 2), e -> part[e[1]] <> part[e[2]]);
Print("edges ", Length(k1222), "\n");
TestJ("K1222", 7, k1222, 3, 5);
QUIT;
