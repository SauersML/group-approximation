---
rg: 2
id: higman-derived-length-three-edge-images-collapse
kind: claim
title: In a nontrivial quotient of Higman's group no opposite pair generates a virtually derived-length-3 group, so the normal closure of F''' is all of H4
distinct_from:
  solvable-by-metabelian-edge-images-collapse-higman-quotients: that needs the second derived subgroup of the image to have finite Hirsch length and leaves open derived length 3 with infinite-rank bottom layer; this kills every image of derived length at most 3, of any rank, by a two-sided b-d-b conjugation chain instead of a rank count.
  virtually-metabelian-edge-images-collapse-higman-quotients: that kills derived length 2; this reduces derived length 3 to it, since the chain puts a^y and c^y into the metabelian group A'.
  higman-b-side-derived-closure-stays-in-bottom-layer: that shows the one-sided (b-side) closure of F^(k) in G_b meets F inside P^(k-1); this shows the two-sided closure in H4 of F''' is everything, so alternating the sides escapes every derived layer.
artifacts:
  - experiments/higman-two-sided-ladder-2026-09-18/ladder.py
  - experiments/higman-two-sided-ladder-2026-09-18/ladder-output.txt
---

**ESTABLISHED** by `higman-derived-length-three-edge-collapse-proof`.

**Statement.** Let `Q` be a quotient of
`H4 = < a, b, c, d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >` (`x^y = y^-1 x y`), and let
`F = <a,c>`, which is free in `H4`.

1. **Powers.** If for some `m >= 1` the subgroup `A = <a^m, c^m>` of `Q` satisfies `A''' = 1`, then
   `Q = 1`. The same holds for `<b^m, d^m>`.
2. **Normal closure.** The normal closure of `F'''` in `H4` is `H4`. In particular
   `ncl_H4(F''') ∩ F = F`, which is not contained in `P'' ∩ P_d''`. Here `P = ncl_F(c)` and
   `P_d = ncl_F(a)`.
3. **Edge images.** If the image of `<a,c>` or of `<b,d>` in `Q` has a finite-index subgroup of
   derived length at most 3, then `Q = 1`.
4. **Trees.** If `Q != 1` acts on a tree without inversions, and every edge stabilizer is virtually
   of derived length at most 3, then `Q` fixes a vertex. So a nontrivial quotient of `H4` never splits
   as an amalgam or HNN extension over such a subgroup.

**Mechanism.** Put `alpha = a^m`, `gamma = c^m`, `P = 2^m`, `gamma_j = alpha^j gamma alpha^-j` and
`N_j = 2^(P^j)`. Then `b^-1 gamma_j b = gamma_j^(N_j)` for `j >= 0`, and on the `d` side
`d^-1 alpha_i d = alpha_i^(N_i)`. Start from an explicit word
`w_0 = [[x,y],[y,x_2]] in F'''` with `x = gamma_1 gamma_0^-1`, `y = gamma_0^-1 gamma_1` and
`x_2 = gamma_0 gamma_1 gamma_0^-2`. Conjugate it by `b`, then `gamma^n`, then `d`, then `alpha^n'`, then `b`.
Each conjugation by `b` or `d` replaces letters by huge powers, and the result `u_3` is a word in
`alpha, gamma` with exponent sums `(0, y)`, `y != 0`, that is trivial in `Q`.
- **Bookkeeping.** `u_3` is tracked by a Fox-calculus count: the image of `u_2` in
  `P/P' = Z[X^±1]` is a formal sum `S(u_1)` evaluated at `t_h -> X^(N_h)`.
- **Why the huge exponents cannot cancel.** `N_(h+1) >= N_h^2`, so for large shifts `n, n'` distinct
  formal terms stay distinct, and the top term dominates.
- **Nonvanishing.** That `S(u_1)` is nonzero is certified by `ladder.py`. The run is exact for
  `m = 1..4`, and a symbolic run (with `N_1 = 2^P` formal) covers all `m >= 2`.
- **Conclusion.** The mirrored chain (`d, b, d`) gives exponent sums `(y, 0)`. So `A/A'` is finite
  and `<alpha^y, gamma^y> <= A'`, which is metabelian. `virtually-metabelian-edge-images-collapse-higman-quotients`
  then gives `Q = 1`.

**Answer to the two-sided question.** The alternating b-side and d-side closures of `F'''` do not stay
in `P'' ∩ P_d''`. Three half-steps are enough:
- one `b`-step takes `F'''` into `P''` (and no further, by `higman-b-side-derived-closure-stays-in-bottom-layer`);
- the `d`-step reaches an element of `P` with nonzero image in `P/P'`;
- the second `b`-step reaches nonzero exponent sums.

The collapse happens in the abelianization, after which the metabelian theorem finishes.
`H4 / <<F'''>>` is trivial, so it is not available as an amenable edge image for Attempt 5.

**What it kills for Attempt 5.**
- **Excluded.** The glued construction `G_1' *_A G_1'` now needs an amenable edge image `A` none of
  whose finite-index subgroups has derived length at most 3.
- **Still open.** Solvable `A` of derived length at least 4, with infinite-rank `A''`, and
  non-elementary-amenable `A`.
- **General `k`.** The chain generalises to `k` half-steps. The input it needs is nonvanishing of
  an order-`(k-2)` formal tower invariant of `iota_b(w_0)` for some `w_0 in F^(k)`. At `k = 3` this is
  `S(u_1) != 0`.
