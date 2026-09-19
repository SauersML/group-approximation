# greedy minimal monolithic quotients of a pq pc group keeping z = a^(2^(e-1)); a = pcgs[1]
MonoPc := function(P, e, tries)
  local z, res, t, N, nat, Q, zq, Om, x, r, gens;
  gens := Pcgs(P){[1..4]};
  z := gens[1]^(2^(e-1));
  if z = One(P) then Print("z trivial\n"); return fail; fi;
  res := [];
  for t in [1..tries] do
    N := TrivialSubgroup(P);
    repeat
      nat := NaturalHomomorphismByNormalSubgroupNC(P, N);
      Q := Image(nat); zq := Image(nat, z);
      Om := Omega(Centre(Q),2,1);
      if Size(Om) > 2 then
        repeat x := Random(Om); until x <> One(Q) and x <> zq;
        N := PreImage(nat, Subgroup(Q, [x]));
      fi;
    until Size(Om) = 2;
    r := [Log(Size(Q),2), List(gens, g -> Log(Order(Image(nat,g)),2)), N];
    Add(res, r);
    Print("  try ",t,": |Q|=2^",r[1]," log2 ord(a,b,c,d)=",r[2],"\n");
  od;
  return res;
end;
