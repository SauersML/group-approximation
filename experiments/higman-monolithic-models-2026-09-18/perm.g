# greedy large subgroup avoiding the socle generator zq -> faithful transitive permutation rep
BigAvoid := function(Q, zq, tries)
  local best, t, H, g, K, n;
  best := TrivialSubgroup(Q);
  for t in [1..tries] do
    H := TrivialSubgroup(Q); n := 0;
    while n < 60 do
      g := Random(Q); K := ClosureSubgroupNC(H, g);
      if not zq in K then H := K; n := 0; else n := n+1; fi;
    od;
    if Size(H) > Size(best) then best := H; fi;
  od;
  return best;
end;
PermInfo := function(P, e, r)
  local nat, Q, gens, zq, H, act, imgs;
  nat := NaturalHomomorphismByNormalSubgroupNC(P, r[3]); Q := Image(nat);
  gens := List(Pcgs(P){[1..4]}, g -> Image(nat, g)); zq := gens[1]^(2^(e-1));
  H := BigAvoid(Q, zq, 6);
  act := FactorCosetAction(Q, H); imgs := List(gens, g -> Image(act, g));
  Print("   |Q|=2^",Log(Size(Q),2)," perm degree ",Index(Q,H)," cycle types ", List(imgs, x -> Collected(CycleLengths(x,[1..Index(Q,H)]))), "\n");
  return imgs;
end;
