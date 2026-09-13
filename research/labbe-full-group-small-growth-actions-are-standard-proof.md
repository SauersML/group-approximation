---
rg: 2
id: labbe-full-group-small-growth-actions-are-standard-proof
kind: route
title: Small growth forces confined stabilisers, the classification gives a finite set, and quartic growth of pairs leaves one point
target: labbe-full-group-small-growth-actions-are-standard
requires:
  - full-group-confined-subgroups-are-finite-set-stabilizers
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
  - minimal-aperiodic-wang-shift-exists
artifacts:
  - research/artifacts/labbe-lef-crux-small-growth-models-2026-09-13.md
---

The full derivation is in the artifact: Section 1 (Lemmas 1.1 and 1.2) and Section 2 (Theorem A).

**Inputs.**
- `G = Z^2 ~ Omega_U` is a minimal, free, hence effective, étale groupoid over a Cantor space
  (`minimal-aperiodic-wang-shift-exists`).
- `Gamma = D([[G]]) = A(G)` is finitely generated, infinite and simple
  (`minimal-z2-subshift-derived-full-groups-are-fg-simple`).

**Lemma 1.1.** `St_Gamma(x) = St^0_Gamma(x)`, since a continuous `Z^2`-valued cocycle vanishing at `x` vanishes
near `x`.

**Lemma 1.2.** For `x_1 ≠ x_2` the orbit graph of `(x_1, x_2)` satisfies `|B_k| >= c k^4`.
1. **Walks in two separate pieces.** Take disjoint clopen sets `U_i ∋ x_i` and a syndeticity radius `r_U` for
   the return sets `Lambda_i`. By compactness, finitely many 3-cycles supported in `U_i` realise every return
   jump of length `<= 2 r_U + 1`. Each has `S`-length `<= L`.
2. **Short paths.** A lattice path with nearby returns gives `a_u`, of length `<= 2Lk` and supported in `U_1`,
   with `a_u x_1 = sigma^u x_1` for `u ∈ Lambda_1 ∩ B(k)`. Likewise `b_w` for `x_2`.
3. **Counting.** `a_u b_w (x_1, x_2) = (sigma^u x_1, sigma^w x_2)`, and there are `>= (k/J)^4` distinct pairs.

**Theorem A.** Let `v ∈ Y` and `H = St(v)`.
1. **`H` is confined.**
   - If not, then for each `k` some `gv` has `St(gv) ∩ B_{2k} = {1}`, so `|B_k(Gamma)| <= f(k) = o(k^4)`.
   - By Gromov `Gamma` would be virtually nilpotent, hence residually finite. An infinite simple group is not.
2. **A finite set.** `full-group-confined-subgroups-are-finite-set-stabilizers` gives `St^0(Q) ≤ H ≤ St(Q)`.
3. **Cases.**
   - `Q = ∅`: `v` is fixed.
   - `|Q| = q >= 2`: `Gamma v -> Gamma Q` maps balls onto balls, and ordered tuples cover `Gamma Q` with fibres
     `<= q!` and project onto pairs. So `|B_k(v)| >= c k^4 / q!`, a contradiction.
   - `Q = {x}`: `H = St(x)` by Lemma 1.1, and `gv -> gx` is an isomorphism. ∎
