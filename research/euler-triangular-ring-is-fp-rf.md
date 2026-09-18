---
rg: 2
id: euler-triangular-ring-is-fp-rf
kind: claim
title: The triangular Euler ring T_l = [[D, D/Du],[0, Z]] is finitely presented and residually finite, and its off-diagonal corner is the Euler base M ⊇ Z_(l)
distinct_from:
  resolvent-presentation-ring-is-residually-finite: that ring R_l carries Z_(l) as a corner ring e R_l e, whose K_2 contains the infinitely generated tame symbols of K_2(Z_(l)); here Z_(l) sits only in the square-zero bimodule corner, so it contributes no units and no corner ring.
  euler-base-annihilator-over-lamplighter-is-not-fg: that shows the Euler base is not finitely presented over any group ring of an overgroup of Z≀Z; this presents it inside a finitely presented ring instead.
  z-localized-embeds-in-fg-rf-soluble-group: that is the group G_l = M ⋊ (Z≀Z); here G_l sits inside the unit group of T_l as the matrices [[h, m],[0, 1]].
artifacts:
  - research/artifacts/gq-referee-a-euler-triangular-ring-is-fp-rf.md
---

**ESTABLISHED** through `euler-triangular-ring-is-fp-rf-proof`. Lane proof; proof-gap review
PASS by gq-referee-a (report in `artifacts`). It uses no unread citation.

**Notation.**
- `D = A[x^(±1); σ]` is the Euler ring of `resolvent-ring-has-path-normal-form`, with
  `A = Z[u][(u+1+kl)^(-1) : k in Z]` and `σ(u) = u + l`.
- `M = D/Du` is the Euler base, the free `Z_(l)`-module on `f_j = x^(-j) v_0` (`j in Z`), where
  `v_0` is the class of 1. Then `u f_j = lj f_j` and `x f_j = f_(j-1)`, and `M ≅ Z_(l)[y^(±1)]` as in
  `euler-base-annihilator-over-lamplighter-is-not-fg`.
- `T_l = [[D, M],[0, Z]]` is the ring of formal matrices with `D` in the upper left, the
  `(D,Z)`-bimodule `M` in the upper right and `Z` in the lower right, with matrix multiplication and
  `M M = 0`.

**Statement.**
1. **Finite presentation.** `T_l` is isomorphic to the ring with generators `e, u, x, x', B, m` and
   the relations
   - `e^2 = e`;
   - `g = e g e` for `g in {u, x, x', B}`;
   - `x x' = x' x = e`;
   - `x u = (u + l e) x`;
   - `B(u+e) = (u+e)B = e`;
   - `e m = m`, `m e = 0`, `u m = 0`.

   Here `e -> [[1,0],[0,0]]`, the four `D`-generators go to their images in the corner, and
   `m -> [[0, v_0],[0, 0]]`. There are 6 generators and finitely many relations.
2. **Residual finiteness.** For `r >= 1` and `N` a multiple of `l^(r-1)`, let `M_(r,N)` be the
   finite `D`-module `⊕_(j in Z/N) (Z/l^r) f_j`, with `u = lj`, `x` the shift `f_j -> f_(j-1)`, and
   `B = (1+lj)^(-1)`. The reduction `M -> M_(r,N)` is `D`-linear, and the maps
   `T_l -> [[End(M_(r,N)), M_(r,N)],[0, Z/l^r]]` onto finite rings separate the points of `T_l`.
3. **The corner.** The additive group of the corner `e T_l (1-e) ≅ M` contains `Z_(l) f_0`.
4. **Units.** `G_l ≅ {[[h, n],[0,1]] : h in <x, 1+u>, n in M} <= T_l^×`, with `1 + u` acting as `β`.
   This uses that `D` acts faithfully on `M`: `d = Σ_a x^a f_a` acts by `f_j -> Σ_a f_a(lj) f_(j-a)`,
   and a nonzero rational function has finitely many zeros (the case "δ != 0" of
   `resolvent-presentation-ring-is-residually-finite-proof`). Note N1 of gq-referee-a.
