# fast greedy: kill a random hyperplane of Omega_1(Z(Q)) avoiding zq at each step
MonoPc := function(P, e, tries)
  local z, res, t, N, nat, Q, zq, Om, pc, v, f, K, r, gens, rk, hs;
  gens := Pcgs(P){[1..4]};
  z := gens[1]^(2^(e-1));
  if z = One(P) then Print("z trivial\n"); return fail; fi;
  res := [];
  for t in [1..tries] do
    N := TrivialSubgroup(P);
    repeat
      nat := NaturalHomomorphismByNormalSubgroupNC(P, N);
      Q := Image(nat); zq := Image(nat, z);
      Om := Omega(Centre(Q),2,1); rk := Log(Size(Om),2);
      if rk > 1 then
        pc := Pcgs(Om); v := ExponentsOfPcElement(pc, zq) * Z(2);
        repeat f := List([1..rk], i -> Random(GF(2))); until f*v = Z(2);
        K := NullspaceMat(TransposedMat([f]));
        hs := List(K, row -> PcElementByExponents(pc, List(row, IntFFE)));
        N := PreImage(nat, Subgroup(Q, hs));
      fi;
    until rk = 1;
    r := [Log(Size(Q),2), List(gens, g -> Log(Order(Image(nat,g)),2)), N];
    Add(res, r);
    Print("  try ",t,": |Q|=2^",r[1]," log2 ord(a,b,c,d)=",r[2],"\n");
  od;
  return res;
end;
