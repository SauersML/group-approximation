---
rg: 2
id: bernoulli-assembly-injective-beyond-the-host
kind: claim
title: Over every host the Bernoulli cylinder comparison is injective, so Baum--Connes at a Bernoulli coefficient can fail beyond the host only by non-surjectivity, and over torsion-free hosts only in one of three shapes
distinct_from:
  bernoulli-bc-splits-into-host-and-cylinder-comparison: that reduces Baum--Connes at a Bernoulli coefficient to the host plus the comparison T_r; this proves T_r injective with rank functionals and classifies the three shapes a surjectivity failure can take.
  module-dual-actions-have-no-wandering-open-sets: that excludes proper open invariant sets; this uses proper orbits that are not open, the finite-support configurations, whose orbit representations give rank functionals on the ideal of the fixed point.
---

**ESTABLISHED** by `bernoulli-assembly-injective-beyond-the-host-proof`. Full proofs:
`research/artifacts/bc-bernoulli-rank-functionals-2026-09-13.md` (torsion-free hosts) and
`research/artifacts/bc-bernoulli-rank-functionals-torsion-2026-09-13.md` (every host).

**Setting.**
- `G` is countable and `Z` a countable `G`-set with finite point stabilizers. Items 1 and 2 hold in this
  generality. Item 3 takes `G` torsion-free and `Z = G`. `Λ = {0, ..., n}` with `n >= 1`, `X = Λ^Z` and
  `I_k = C_0({|supp x| >= k})`.
- Pattern stabilizers `G_s` are finite. `T_r : ⊕_([s]) R(G_s) -> K_0(I_1 ⋊_r G)` sends `[τ] ∈ R(G_s)` to
  `[1_(C_s) p_τ]`, with `p_τ ∈ C*(G_s)` a minimal projection of `τ`. By Claim W of the second artifact it is the
  comparison of `bernoulli-bc-splits-into-host-and-cylinder-comparison`, for every `G`. For torsion-free `G`,
  `R(G_s) = Z` and `[s] ↦ [1_(C_s)]`.
- A **pattern** is a nonzero finite-support configuration. `t <= x` means `t` is `x` restricted to a nonempty subset of
  its support.

**Theorem.**
1. **Rank functionals.** For each pattern `x` and each irreducible representation `σ` of its finite stabilizer
   `G_x`, the induced representation `π_(x,σ) = Ind_(G_x)^G(ev_x, σ)` maps `I_1 ⋊_r G` into the compact operators. So
   `r_(x,σ) = K_0(π_(x,σ)) : K_0(I_1 ⋊_r G) -> Z` is defined. On a same-size generator `[τ ⊗ delta_x]` it returns the
   multiplicity of `τ` in `σ`, and it vanishes on larger patterns. For torsion-free `G`, `σ` is trivial, and
   `r_x[1_(C_s)]` counts the occurrences `t <= x` of the pattern `s` up to translation.
2. **Injectivity.** `T_r` is injective in both degrees. Hence:
   - `mu_(G, I_1)` is injective;
   - reduced assembly for `F_p wr_Z G` is injective iff reduced assembly for `G` is;
   - beyond the host, question (Q) of `monster-bc-failure-at-measured-coefficient-is-the-module-crux` can fail at a
     Bernoulli coefficient only by non-surjectivity. That is the sign of the known monster failure
     (`monster-bc-detector-lives-on-a-proper-orbit-ideal`, item 1).
3. **Anatomy of a surjectivity failure (torsion-free `G`, `Z = G`).** Each `y ∈ K_0(I_1 ⋊_r G)` has integer pattern coefficients `n(y)`,
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

**Scope.**
- The anatomy (item 3) is written only for torsion-free `G` and `Z = G`.
- Willett--Yu I (arXiv:1012.4150, Corollary 1.7) find, at a specific commutative coefficient over a large-girth
  monster, assembly that is injective and not surjective. Item 2 gives the same sign at every Bernoulli coefficient,
  beyond the host.
- The injectivity statement for wreath products may be known. Bounded check: not found in CEKN arXiv:2210.09209
  Sections 1--2, nor in Willett--Yu I Section 1.
