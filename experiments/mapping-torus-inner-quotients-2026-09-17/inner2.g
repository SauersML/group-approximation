# Bounded-type levels of Gamma = F_2 x|_phi Z (phi = "fig8": a->ab, b->bab; or "id").
# A bounded-type level is an epimorphism Gamma -> G whose restriction to N = <a,b> is onto,
# equivalently a generating pair (A,B) of G and x in G with (A,B)^x = (phi(A),phi(B));
# then t -> x^-1.  Gamma_G = kernel has index |G|.
# Reports ord(A), ord(B), ord(t), d_2, d_3, b_1 of Gamma_G and r_p = (d_p - 1)/|G|.
# By Schreier monotonicity along p-power normal refinements, r_p at a level bounds the
# mod-p gradient of every p-power normal chain through that level from above.
F := FreeGroup("a","b","t"); a := F.1; b := F.2; t := F.3;
mkGam := function(phi)
  local rels;
  if phi = "fig8" then rels := [t*a*t^-1*(a*b)^-1, t*b*t^-1*(b*a*b)^-1];
  else rels := [t*a*t^-1*a^-1, t*b*t^-1*b^-1]; fi;
  return F/rels;
end;
phimap := function(phi, A, B)
  if phi = "fig8" then return [A*B, B*A*B]; else return [A, B]; fi;
end;
dp := function(inv, p) return Number(inv, x -> x = 0 or x mod p = 0); end;
search := function(name, G, phi, maxrep)
  local Gam, n, reps, A, B, x, e, K, inv, seen, key, cnt;
  Gam := mkGam(phi); n := Size(G); cnt := 0; seen := [];
  reps := List(ConjugacyClassesByRandomSearch(G), Representative);
  for A in reps do
    for B in G do
      if Size(Subgroup(G,[A,B])) = n then
        x := RepresentativeAction(G, [A,B], phimap(phi,A,B), OnTuples);
        if x <> fail then
          key := [Order(A), Order(B), Order(x)];
          if not key in seen then
            Add(seen, key);
            e := GroupHomomorphismByImagesNC(Gam, G, [A, B, x^-1]);
            K := Kernel(e); inv := AbelianInvariants(K);
            Print(name, " phi=", phi, " |G|=", n, " ord(a,b,t)=", key,
              " d2=", dp(inv,2), " d3=", dp(inv,3), " b1=", Number(inv,y->y=0),
              " r2=", Float((dp(inv,2)-1)/n), " r3=", Float((dp(inv,3)-1)/n), "\n");
            cnt := cnt + 1; if cnt >= maxrep then return; fi;
          fi;
        fi;
      fi;
    od;
  od;
  if cnt = 0 then Print(name, " phi=", phi, " |G|=", n, " no bounded-type level\n"); fi;
end;
