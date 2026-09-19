Read("mono3.g"); Read("perm.g");
Read("p5.g"); P := F; e := 5;
r := MonoPc(P, e, 4);
for x in r do
  nat := NaturalHomomorphismByNormalSubgroupNC(P, x[3]); Q := Image(nat);
  zq := Image(nat, Pcgs(P)[1])^(2^(e-1));
  H := BigAvoid(Q, zq, 3);
  Print("   |Q|=2^",Log(Size(Q),2)," greedy core-free index 2^",Log(Index(Q,H),2),"\n");
od;
QUIT;
