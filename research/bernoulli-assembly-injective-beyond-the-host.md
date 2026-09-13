---
rg: 2
id: bernoulli-assembly-injective-beyond-the-host
kind: claim
title: Over a torsion-free host the Bernoulli cylinder comparison is injective, so Baum--Connes at a Bernoulli coefficient can fail beyond the host only by non-surjectivity, in one of three shapes
distinct_from:
  bernoulli-bc-splits-into-host-and-cylinder-comparison: that reduces Baum--Connes at a Bernoulli coefficient to the host plus the comparison T_r; this proves T_r injective with rank functionals and classifies the three shapes a surjectivity failure can take.
  module-dual-actions-have-no-wandering-open-sets: that excludes proper open invariant sets; this uses proper orbits that are not open, the finite-support configurations, whose orbit representations give rank functionals on the ideal of the fixed point.
---

**ESTABLISHED** by `bernoulli-assembly-injective-beyond-the-host-proof`. Full proofs:
`research/artifacts/bc-bernoulli-rank-functionals-2026-09-13.md`.

**Setting.**
- `G` is countable and torsion-free, and `Z` is a free countable `G`-set. `Λ = {0, ..., n}` with `n >= 1`,
  `X = Λ^Z` and `I_k = C_0({|supp x| >= k})`.
- `T_r : ⊕_([s]) Z -> K_0(I_1 ⋊_r G)`, `[s] ↦ [1_(C_s)]`, is the comparison of
  `bernoulli-bc-splits-into-host-and-cylinder-comparison`.
- A **pattern** is a nonzero finite-support configuration. `t <= x` means `t` is `x` restricted to a nonempty subset of
  its support.

**Theorem.**
1. **Rank functionals.** For each pattern `x`, the orbit representation `π_x` on `l^2(G)` maps `I_1 ⋊_r G` into the
   compact operators. So `r_x = K_0(π_x) : K_0(I_1 ⋊_r G) -> Z` is defined, and `r_x[1_(C_s)]` is the number of
   occurrences `t <= x` of the pattern `s` up to translation.
2. **Injectivity.** `T_r` is injective in both degrees. Hence:
   - `mu_(G, I_1)` is injective;
   - reduced assembly for `F_p wr_Z G` is injective iff reduced assembly for `G` is;
   - beyond the host, question (Q) of `monster-bc-failure-at-measured-coefficient-is-the-module-crux` can fail at a
     Bernoulli coefficient only by non-surjectivity. That is the sign of the known monster failure
     (`monster-bc-detector-lives-on-a-proper-orbit-ideal`, item 1).
3. **Anatomy of a surjectivity failure (`Z = G`).** Each `y ∈ K_0(I_1 ⋊_r G)` has integer pattern coefficients `n(y)`,
   the Möbius inverse of its ranks: `r_x(y) = Σ_(t <= x) n_([t])(y)`. They have two properties:
   - there is a finite `B ⊆ G` such that `n(y)` vanishes on every pattern whose support splits into two
     `B`-separated parts;
   - for every `k`, `y - T_r(n^(<k)(y))` lies in the image of `K_0(I_k ⋊_r G)`.

   So `T_r` fails to be surjective iff at least one of the following holds:
   - **(a)** some class has nonzero coefficients on `B`-connected patterns of unbounded size;
   - **(b)** some nonzero class lies in `∩_k im K_0(I_k ⋊_r G)` and has all ranks `0`;
   - **(c)** `K_1(I_1 ⋊_r G) ≠ 0`.

**What it changes.**
- Rank-at-infinity detectors do exist at dual-module coefficients, on the ideal of the fixed point. The finite-support
  strata are proper orbits that are not open.
- These detectors certify injectivity and see shape (a). Shapes (b) and (c) are invisible to them.
- Over a torsion-free host satisfying trivial-coefficient Baum--Connes, a counterexample for `F_p wr G` is exactly a
  class of shape (a), (b) or (c) over `C_0((Z/p)^G \ {0}) ⋊_r G`.

**Model test.** For `G = Z = Z` and `n = 1`, `T_r` is an isomorphism (Pimsner--Voiculescu), so no shape occurs. For
`x = δ_0 + δ_1` and the one-site pattern `s`, `r_x[1_(C_s)] = 2`.

**Scope.** Groups with torsion are not covered: with nontrivial finite stabilizers the ranks see only dimensions, not
the representation-ring summands. The injectivity statement for wreath products may be known (bounded check: not found
in CEKN arXiv:2210.09209 Sections 1--2).
