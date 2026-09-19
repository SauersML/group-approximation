---
rg: 2
id: c2-split-rose-passes-cycle-test-fails-gluing-rank
kind: claim
title: For the admissible (C2) pair the free-factor condition (P_3) holds, so the fibred rose in the basis (pSr, rP, sR, q) passes the canonical-cycle test. It still carries no realization of RP(H,G). A sharper test, the gluing rank, shows this. The three support cells must be glued along zero-sum edge blocks, the least such gluing has rank 7 = 3 + #cells, and the fourth cell does not close up in it
distinct_from:
  c2-fibred-realizations-reduce-to-a-primitive-class: that reduces passing the canonical-cycle test in fibred K(G,1)s to (P_free) and leaves (P_1)-(P_4) open. This proves (P_3) explicitly, so passing complexes exist and (P_free) cannot exclude fibred realizations. It then excludes the first passing rose by a new test that uses the 2-cell count and the Euler characteristic of H, not only the support of the cycle.
  c2-rose-mapping-torus-has-no-one-lift-core: that excludes the standard rose by two lifts of one 2-cell in an index-9 cover, and its (T4) also rejects bases with a coefficient of absolute value 2. That coefficient filter is not implied by the canonical-cycle test. The basis here has coefficients (1, 2, 2), passes that test, and is excluded only by the gluing rank.
  two-cell-injective-maps-realize-relative-eg-pairs: that gives the realization criterion by 2-cell-injective maps K(H,1) -> X, which may fold 1-cells. The gluing-rank test is a necessary condition for such a map into a fixed X, and it applies to maps, not only to subcomplexes of X_H.
---

**ESTABLISHED** through `c2-split-rose-passes-cycle-test-fails-gluing-rank-proof`. Unreviewed.
- (S1) and (S2) are exact. `experiments/c2-split-rose-2026-09-19/pcheck.py` checks the `H_1` identity inside
  the window `T_8 ⊂ N`.
- (S3) is proved by hand.
- (S4) is exact finite computation. Cosets are merged only by window memberships, which are exact
  positive tests, and separated only by the `S_9` cover of the rose node, which is an exact negative
  test. Every pair of vertex classes that occurs is decided. `minrank.py` and `dcell.py` replay (S4) in
  a few seconds.
- (S5) is a computation over the listed bases only.

## Setting

The pair is the one of `admissible-ab-nonzero-two-cell-base-exists`:
- `G = ⟨x,y | w⟩ = F_4 ⋊_φ ⟨y⟩`, with `F_4 = ⟨p,q,r,s⟩` and `φ: p↦q↦r↦s↦rrSqPRs`;
- `H = N ⋊ ⟨y⟩`, with `χ(H) = −2` and `H_2(H) ≅ Z`;
- `c_H` generates `H_1(N)^φ`.

A K(G,1) `X` *passes* when the generator of `Z_2(X_H)` has support injecting into the 2-cells of `X`
(test (T0) of `c2-rose-mapping-torus-has-no-one-lift-core`).

## Statement

- **(S1) `(P_3)` holds.** Put `a = pSr`, `b = rP`, `c = sR`. Then `(a, b, c, q)` is a basis of `F_4`, so
  `⟨a,b,c⟩` is a free factor. Put `F_1 = s⁻¹as`, `F_2 = b` and `F_3 = q⁻¹cq`. These lie in `N`, and
  `c_H = [F_1] + 2[F_2] + 2[F_3]` in `H_1(N)`. So `(P_free)` of the fibred-reduction node holds.
- **(S2) A passing rose.** Let `f` be the rose map of `φ` in the basis `B = (a,b,c,d) = (pSr, rP, sR, q)`:
  `a ↦ dABCbaBcbaDcABcba`, `b ↦ ccbaD`, `c ↦ cbaCdABCbABC`, `d ↦ cba`.
  - The canonical cycle of `(M_f)_H` is `σ_a[N s⁻¹] + 2σ_b[N] + 2σ_c[N q⁻¹]`.
  - It has one lift of each of `σ_a`, `σ_b` and `σ_c`, and none of `σ_d`, so `M_f` passes (T0).
  - No finite cover can exclude this rose through (T0).
  - The same holds for every basis `(a, b, c, d')`.
- **(S3) Gluing-rank test.** Let `X` be an aspherical 2-complex with `π_1 X = G` and `F_X` 2-cells.
  Let `h: K → X` be a 2-cell-injective combinatorial map from a finite 2-dimensional `K(H,1)` with `F`
  2-cells that induces `H ↪ G`. Let `D ⊂ K` be the closure of the cells carrying the canonical cycle.
  1. `F ≤ F_X`, and `rank K^{(1)} = 1 − χ(H) + F`.
  2. `D^{(1)}` is a quotient of the disjoint union of the boundary circles of the support cells. In
     it, the occurrences of each edge of `X_H` fall into blocks of total coefficient zero, one block
     for each edge of `K` over it. The vertices are identified at least as these blocks force.
  3. `rank D^{(1)} ≤ rank K^{(1)}`. When equality holds and `D^{(1)}` is connected, every other cell
     of `K` has its boundary on a closed path in `D^{(1)}`.
- **(S4) The split rose fails (S3).**
  - Here `1 − χ(H) + F ≤ 7`.
  - The support closure `C_0 ⊂ (M_f)_H` has 6 vertices, 16 edges and 3 cells, with `χ = −7`.
  - Its 16 edges carry 43 occurrences, which admit 72 zero-sum block partitions.
  - The least forced rank is 7, attained by exactly one gluing, which is connected. So `F = 4`, and
    the `σ_d` cell of `K` would have to close up in that gluing.
  - The only lift of `σ_d` with boundary in `C_0` is `σ_d[N q⁻¹]`. Its boundary path
    `t · cba · t⁻¹ · d⁻¹` does not close in the gluing: after `t, c, b, a` it reaches the origin of
    the one `K`-edge over `t_N`, not its end.
  - So `M_f` carries no 2-cell-injective map from a `K(H,1)`: it passes (T0) and still does not
    realize.
- **(S5) Neighbouring bases.** Take the bases `(a, b, c, w_1 q w_2)` with `w_1, w_2 ∈ {1, a^{±1}, b^{±1}, c^{±1}}`.
  - There are 49 of them, and all pass (T0).
  - 42 are excluded by (S3) in the same way: least gluing rank 7, and the `d`-cell never closes up.
  - The 7 with `w_2 = a` meet a coset pair that the known covers do not decide, so they are left
    open.

## Consequences for the lane

- The program "`¬(P_free)` excludes every fibred K(G,1)" is dead, because (S1) holds explicitly. The
  fibred remainder is not closed by (T0) alone: passing roses exist.
- (T0) is not sharp. The gluing-rank test (S3) is strictly stronger. It uses `χ(H)` and the number
  of 2-cells of `X`, and it applies to folding maps, not only to subcomplexes of `X_H`.
- In every case computed, the least gluing rank is exactly the bound 7. So the obstruction always
  falls on the last cell, not on a rank count alone.
- `c2-rose-mapping-torus-has-no-one-lift-core` (T4) rejects bases with a coefficient of absolute
  value 2. (T0) does not justify that filter, since the basis `B` has coefficients `(1,2,2)`.
  Bases rejected only by that filter are not excluded until (S3) is run on them.

## Next step

Run (S3) on every rose that passes (T0). Those are the bases containing a free-factor basis
`(a_1, …, a_k)` that carries `c_H` as in (S1). Prove an intrinsic version, for example: in every
passing marked graph, the least zero-sum gluing already uses all `1 − χ(H) + F_X` of the rank, so
the cells outside the support can never close. Then carry the test to slide complexes.
