# Output: k1222_p5.out.  K_{1,2,2,2}, p=5, classes <= 5 (Lazard: J dies below class 5).
OnBreak := function() FORCE_QUIT_GAP(3); end;
Read("pq.g");
part := [1,2,2,3,3,4,4];
k1222 := Filtered(Combinations([1..7], 2), e -> part[e[1]] <> part[e[2]]);
TestJ("K1222", 7, k1222, 5, 5);
QUIT;
