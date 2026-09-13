# tris_lib.g -- complete enumeration of Hom(G, S) for a triangle of groups
#   G = < p, q, r | R_A(p,q), R_B(q^e1, r), R_C(r^e2, p^e3) >,
# vertex groups A = <p,q>, B = <q,r>, C = <r,p> finite simple, edge groups cyclic, face trivial.
# Lane ex-hyperbolic-triangle-search, 2026-09-13.
#
# Method (embedding classes + double cosets). Fix a hom alpha: A -> S up to S-conjugacy,
# t := alpha(q)^e1, v := alpha(p)^e3. Every beta: B -> S with beta(x_B) = t is
# beta0^(g0 h) with beta0 a class representative, g0 fixed, h in Ct := C_S(t); beta0^(g0 h)
# depends only on the coset U h, U := C_S(beta0^g0 (B)). The C-condition "(beta(y_B)^e2, v)
# satisfies R_C" is invariant under h -> h w for w in V := C_Ct(v). So one test per double
# coset U h V, and #compatible beta = sum over passing double cosets of |U h V| / |U|.
# This is complete: every hom G -> S is found (for simple vertex groups every nontrivial one
# is vertex-injective, so trivial alpha is skipped).

MakeVData := function(A, pair)
  local F;
  F := Range(IsomorphismFpGroupByGenerators(A, pair));
  return rec(grp := A, pair := pair, rels := RelatorsOfFpGroup(F),
             fg := FreeGeneratorsOfFpGroup(F), size := Size(A),
             ords := [Order(pair[1]*pair[2]), Order(pair[1]*pair[2]^-1),
                      Order(pair[1]^2*pair[2]), Order(Comm(pair[1], pair[2]))]);
end;

SatRels := function(V, u, v)
  local w;
  for w in V.rels do
    if MappedWord(w, V.fg, [u, v]) <> One(u) then return false; fi;
  od;
  return true;
end;

# Cheap necessary condition for an injective hom x->u, y->v.
OrdOk := function(V, u, v)
  return Order(u*v) = V.ords[1] and Order(u*v^-1) = V.ords[2]
     and Order(u^2*v) = V.ords[3] and Order(Comm(u, v)) = V.ords[4];
end;

# Nontrivial transitive actions of V.grp of degree <= maxdeg, images of the generating pair.
TransitiveTypes := function(V, maxdeg)
  local res, H, d, act, k, ccs;
  res := []; ccs := List(ConjugacyClassesSubgroups(V.grp), Representative);
  for k in [1..Length(ccs)] do
    H := ccs[k]; d := Index(V.grp, H);
    if d > 1 and d <= maxdeg then
      act := FactorCosetAction(V.grp, H);
      Add(res, rec(deg := d, cls := k, imgs := [Image(act, V.pair[1]), Image(act, V.pair[2])]));
    fi;
  od;
  for H in res do
    if LargestMovedPoint(H.imgs) > H.deg then Error("TransitiveTypes: bad point set"); fi;
  od;
  return res;
end;

# Multisets of type indices with total degree <= n (at least one type).
TypeCombos := function(types, n)
  local res, go;
  res := [];
  go := function(start, chosen, total)
    local i;
    if Length(chosen) > 0 then Add(res, ShallowCopy(chosen)); fi;
    for i in [start..Length(types)] do
      if total + types[i].deg <= n then
        Add(chosen, i); go(i, chosen, total + types[i].deg); Remove(chosen);
      fi;
    od;
  end;
  go(1, [], 0);
  return res;
end;

CombinePerm := function(types, combo, n, gi)
  local L, off, i, t, j;
  L := [1..n]; off := 0;
  for i in combo do
    t := types[i];
    for j in [1..t.deg] do L[off + j] := off + j^t.imgs[gi]; od;
    off := off + t.deg;
  od;
  return PermList(L);
end;

SetsOfDegree := function(types, n)
  return List(TypeCombos(types, n), c -> rec(combo := List(c, i -> types[i].deg),
    cls := List(c, i -> types[i].cls),
    x := CombinePerm(types, c, n, 1), y := CombinePerm(types, c, n, 2)));
end;

# Core loop over alpha and beta class representatives inside an ambient group Amb.
# alphas, betas: lists of records with fields x, y (images of the generating pairs).
CoreSearch := function(Amb, VA, VB, VC, e, alphas, betas, report)
  local a, b, t, v, Ct, V, g0, Y, U, dcs, d, r, u, nb, total, found, stats, orbs;
  found := []; stats := rec(pairs := 0, dcs := 0, ordpass := 0, homs := 0);
  for a in alphas do
    t := a.y^e[1]; v := a.x^e[3];
    Ct := Centralizer(Amb, t); V := Centralizer(Ct, v);
    nb := 0;
    for b in betas do
      g0 := RepresentativeAction(Amb, b.x, t);
      if g0 <> fail then
        stats.pairs := stats.pairs + 1;
        Y := b.y^g0;
        U := Centralizer(Ct, Group(t, Y));
        dcs := DoubleCosetRepsAndSizes(Ct, U, V);
        stats.dcs := stats.dcs + Length(dcs);
        for d in dcs do
          r := Y^d[1]; u := r^e[2];
          if OrdOk(VC, u, v) then
            stats.ordpass := stats.ordpass + 1;
            if SatRels(VC, u, v) then
              if not (SatRels(VA, a.x, a.y) and SatRels(VB, t, r)) then
                Error("CoreSearch: found hom fails a relator check");
              fi;
              nb := nb + d[2] / Size(U);
              stats.homs := stats.homs + 1;
              orbs := List(Orbits(Group(a.x, a.y, r), MovedPoints(Group(a.x, a.y, r))), Length);
              Add(found, rec(p := a.x, q := a.y, r := r, orbits := orbs,
                             acombo := a.combo, bcombo := b.combo));
              if report then
                Print("    HOM alpha=", a.combo, " beta=", b.combo, " orbits=", orbs, "\n");
              fi;
            fi;
          fi;
        od;
      fi;
    od;
    a.nbeta := nb;
  od;
  return rec(found := found, stats := stats, alphas := alphas);
end;

# |Hom(G, Amb)| from a CoreSearch result: each alpha class has |Amb : C_Amb(alpha(A))| members.
TotalHoms := function(Amb, res)
  return Sum(res.alphas, a -> Index(Amb, Centralizer(Amb, Group(a.x, a.y))) * a.nbeta);
end;

# Hom(G, S_n): alpha, beta run over A-sets and B-sets of degree n (types from subgroup classes).
SearchSn := function(VA, VB, VC, e, n, TA, TB)
  local alphas, betas;
  alphas := SetsOfDegree(TA, n); betas := SetsOfDegree(TB, n);
  return CoreSearch(SymmetricGroup(n), VA, VB, VC, e, alphas, betas, true);
end;

# Hom(G, S) for a general finite group S (alpha, beta from AllHomomorphismClasses).
SearchAmb := function(VA, VB, VC, e, S)
  local cls, alphas, betas;
  cls := function(V)
    return List(Filtered(AllHomomorphismClasses(V.grp, S), h -> Size(Image(h)) > 1),
      h -> rec(x := Image(h, V.pair[1]), y := Image(h, V.pair[2]),
               combo := [Size(Centralizer(S, Image(h)))], cls := []));
  end;
  alphas := cls(VA); betas := cls(VB);
  Print("  #alpha classes=", Length(alphas), " #beta classes=", Length(betas), "\n");
  return CoreSearch(S, VA, VB, VC, e, alphas, betas, true);
end;

# Naive check for small n: count r over all elements of order o in S_n with both conditions.
NaiveBetaCount := function(VB, VC, e, n, a, o)
  local t, v, cnt, r;
  t := a.y^e[1]; v := a.x^e[3]; cnt := 0;
  for r in SymmetricGroup(n) do
    if Order(r) = o and OrdOk(VB, t, r) and SatRels(VB, t, r)
       and OrdOk(VC, r^e[2], v) and SatRels(VC, r^e[2], v) then
      cnt := cnt + 1;
    fi;
  od;
  return cnt;
end;
