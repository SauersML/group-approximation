# Check of fpbs-fibered-mod-p-certificates-refute-luck-approximation, Prop 1:
# for Gamma = <a,b,t | t a t^-1 = phi(a), t b t^-1 = phi(b)> and an epimorphism Gamma -> G,
#   d_p(Gamma_G) - 1 = nullity of the Fox matrix F (2 x 3) over F_p[G]        (identity)
#   nullity(F) <= nullity(B), B = the 2 x 2 block (d r_i / d x_j) = t I - J(phi)   (bound)
# nullity = dim of the left kernel of v -> v F on row vectors, via the right regular representation.
Read("inner2.g");
FoxD := function(w, i)   # left Fox derivative of word w (in F) wrt generator i, as list of [sign, prefix]
  local L, res, pre, k, g, e;
  L := LetterRepAssocWord(w); res := []; pre := One(F);
  for k in L do
    if k = i then Add(res, [1, pre]); fi;
    if k = -i then Add(res, [-1, pre*F.(i)^-1]); fi;
    pre := pre * F.(AbsInt(k))^SignInt(k);
  od;
  return res;
end;
nullities := function(G, A, B, x, phi, p)
  local els, n, imgs, hom, Rg, rel, F2, Bm, rows, i, j, blk, one, e, K, inv, dp, rkF, rkB;
  els := AsSSortedList(G); n := Length(els); one := One(GF(p));
  imgs := [A, B, x^-1];
  hom := GroupHomomorphismByImagesNC(F, G, imgs);
  Rg := function(g) local M, h; M := NullMat(n, n, GF(p));
    for h in [1..n] do M[h][PositionSorted(els, els[h]*g)] := one; od; return M; end;
  blk := function(w, k) local M, s; M := NullMat(n, n, GF(p));
    for s in FoxD(w, k) do M := M + s[1]*Rg(Image(hom, s[2])); od; return M; end;
  if phi = "fig8" then rel := [t*a*t^-1*(a*b)^-1, t*b*t^-1*(b*a*b)^-1];
  else rel := [t*a*t^-1*a^-1, t*b*t^-1*b^-1]; fi;
  F2 := List(rel, r -> List([1..3], k -> blk(r, k)));
  Bm := List([1,2], i -> Concatenation(List([1,2], j -> F2[i][j])));
  rows := function(M3, cols) local R, i, j, r; R := [];
    for i in [1,2] do for r in [1..n] do
      Add(R, Concatenation(List(cols, j -> M3[i][j][r]))); od; od; return R; end;
  rkF := rows(F2, [1,2,3]); ConvertToMatrixRep(rkF, p); rkF := RankMat(rkF);
  rkB := rows(F2, [1,2]); ConvertToMatrixRep(rkB, p); rkB := RankMat(rkB);
  K := Kernel(GroupHomomorphismByImagesNC(mkGam(phi), G, imgs)); inv := AbelianInvariants(K);
  dp := Number(inv, y -> y = 0 or y mod p = 0);
  Print("|G|=", n, " p=", p, " phi=", phi, " d_p-1=", dp-1, " nullF=", 2*n-rkF, " nullB=", 2*n-rkB,
        " nullB/|G|=", Float((2*n-rkB)/n), " t=", Runtime(), "ms\n");
end;
G := Image(IsomorphismPermGroup(PSL(2,7)));
for pr in [[G, "fig8"], [Image(IsomorphismPermGroup(PSL(2,8))), "fig8"]] do
  found := false;
  for A in List(ConjugacyClassesByRandomSearch(pr[1]), Representative) do
    if found then break; fi;
    for B in pr[1] do
      if Size(Subgroup(pr[1], [A,B])) = Size(pr[1]) then
        x := RepresentativeAction(pr[1], [A,B], phimap(pr[2], A, B), OnTuples);
        if x <> fail then
          for p in [2,3,5,7] do nullities(pr[1], A, B, x, pr[2], p); od;
          found := true; break;
        fi;
      fi;
    od;
  od;
od;
Print("DONE\n"); QUIT;
