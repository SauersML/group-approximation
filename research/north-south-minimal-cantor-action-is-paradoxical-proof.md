---
rg: 2
id: north-south-minimal-cantor-action-is-paradoxical-proof
kind: route
title: Proof — conjugate the north–south element off its own fixed points (Neumann's coset lemma), then compress two two-piece copies of X into four disjoint neighbourhoods
target: north-south-minimal-cantor-action-is-paradoxical
requires: []
artifacts:
  - research/artifacts/un-boundary-families-2026-09-13-part1.md
---

Details are in `research/artifacts/un-boundary-families-2026-09-13-part1.md`, §4.

**Lemma N (B. H. Neumann).** If a group is a finite union of left cosets `c_i S_i`, some `S_i` has finite index.

*Proof.* Induct on the number `r` of distinct subgroups among the `S_i`.
- If `r = 1`, the group is a finite union of cosets of one subgroup, which therefore has finite index.
- If `r > 1`, let `S = S_1` and suppose `[Γ:S]` is infinite. Some coset `dS` is not among the listed cosets of `S`, so
  `dS ⊆ ∪_(S_j != S) c_j S_j`.
- Each listed `c_i S` is `c_i d^(-1)(dS) ⊆ ∪_(S_j != S) c_i d^(-1) c_j S_j`. Substituting gives a finite cover by
  cosets of `r - 1` distinct subgroups, and induction applies.

**Proof of the claim.**
1. **Fixed points.** `g^n ξ^+ -> ξ^+`, so `g ξ^+ = ξ^+`, and likewise for `ξ^-`. If `x` is fixed then `x = g^n x`
   lies in every neighbourhood of `ξ^+`, so `x = ξ^+`. Hence `Fix(g) = {ξ^+, ξ^-}`.
2. **A conjugate with four distinct fixed points.** In a minimal action on an infinite compact space every orbit is
   infinite, since a finite orbit is closed and invariant. So `St(ξ^+)` and `St(ξ^-)` have infinite index.
   - The elements `c` with `cξ^+ ∈ {ξ^+, ξ^-}` or `cξ^- ∈ {ξ^+, ξ^-}` form at most four left cosets of these
     stabilizers. By Lemma N they do not cover `Γ`.
   - Take `c` outside them and put `h = cgc^(-1)`. Then `h` is north–south with points `η^± = cξ^±`: apply the
     definition to the compact `c^(-1)K` and the open `c^(-1)V`.
   - `ξ^+`, `ξ^-`, `η^+` and `η^-` are pairwise distinct.
3. **Compression.** `X` is totally disconnected Hausdorff, so the following clopens exist.
   - Pairwise disjoint clopen neighbourhoods `V_1 ∋ ξ^+`, `V_2 ∋ η^+`, `V_3 ∋ ξ^-` and `V_4 ∋ η^-`.
   - A clopen `C` with `ξ^- ∈ C` and `η^- ∉ C`, and a clopen `D` with `ξ^+ ∈ D` and `η^+ ∉ D`.

   Put `A_1 = X \ C`, `A_2 = C`, `B_1 = X \ D` and `B_2 = D`. These are compact and avoid, respectively, the
   repelling points of `g`, `h`, `g^(-1)` and `h^(-1)`. For large `n`, `g^n A_1 ⊆ V_1`, `h^n A_2 ⊆ V_2`,
   `g^(-n) B_1 ⊆ V_3` and `h^(-n) B_2 ⊆ V_4`, and these sets are pairwise disjoint.
