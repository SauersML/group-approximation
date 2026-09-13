---
rg: 2
id: bernoulli-defects-vanish-along-bcc-subgroup-tubes
kind: claim
title: The Bernoulli cylinder comparison restricts along subgroup tubes, so every defect vanishes along the tubes of subgroups satisfying Baum--Connes with coefficients and a shape-(a) witness must escape all of them
distinct_from:
  bernoulli-assembly-injective-beyond-the-host: that proves injectivity of T_r and sorts surjectivity failures into shapes (a), (b), (c); this builds a restriction *-homomorphism to subgroup tubes and shows that each shape becomes trivial there when the subgroup satisfies Baum--Connes with coefficients.
  bernoulli-bc-splits-into-host-and-cylinder-comparison: that reduces Baum--Connes at a Bernoulli coefficient to T_r; this localizes T_r along subgroups of the host.
  bc-kun-thom-gap-labels-on-bc-subgroups-pass-trace-test: that restricts gapped projections of a group algebra to subgroups with surjective assembly and tests traces; this restricts K-classes of the Bernoulli ideal crossed product to Bernoulli tubes and tests pattern coefficients, ranks and K_1.
---

**ESTABLISHED** by `bernoulli-defects-vanish-along-bcc-subgroup-tubes-proof`. Full proofs:
`research/artifacts/bc-bernoulli-subgroup-restriction-2026-09-13.md`.

**Setting.**
- `G` is countable and torsion-free, `Z = G`, `X = Λ^G` with `Λ = {0, ..., n}`, and `I_1 = C_0(X \ {0})`.
- For a subgroup `H <= G` and a finite `F ⊆ G`, the **tube** `Y = HF` is a free `H`-set with finitely many orbits.
  `X_Y = Λ^Y` is the closed `H`-invariant set of configurations supported in `Y`.
- `T_r^(H,Y)` is the cylinder comparison of the Bernoulli datum `(H, Y)`, as in
  `bernoulli-bc-splits-into-host-and-cylinder-comparison`.

**Theorem.**
1. **Restriction.** There is a *-homomorphism `Res_(H,F) : I_1 ⋊_r G -> K ⊗ (C_0(X_Y \ {0}) ⋊_r H)`. It preserves every
   rank `r_x` at a finite-support configuration `x ∈ X_Y`, and it sends `[1_(C_s)]` to the finite sum of the `H`-cylinder
   classes of the translates `c·s ⊆ Y`.
   - The construction works because, in the right-regular convention, the regular representation at a configuration
     supported in `HF` lives on `l^2(HF')` for a finite `F'`, and is covariant under left translation by `H`.
2. **Defects vanish along good tubes.** Suppose `T_r^(H,HF)` is surjective. This holds if `H` satisfies Baum--Connes with
   coefficients (CEKN arXiv:2210.09209, Theorem 2.8), for example if `H` is amenable, a-T-menable or hyperbolic. Then for
   every class `y`:
   - the pattern coefficients `n_t(y)`, over patterns `t ⊆ HF`, vanish outside finitely many `H`-orbits;
   - `Res_(H,F)(y) = 0` whenever all ranks of `y` vanish;
   - `Res_(H,F)` kills `K_1(I_1 ⋊_r G)`.
3. **Where a witness lives.** Consider a class outside `im T_r^G`, of shape (a), (b) or (c) of
   `bernoulli-assembly-injective-beyond-the-host`.
   - Shapes (b) and (c) restrict to zero along every tube of a subgroup satisfying Baum--Connes with coefficients.
   - For shape (a), for each such tube only finitely many of the `G`-orbits of patterns carrying coefficients have a
     translate inside it.

**What it changes for `bernoulli-cylinder-comparison-fails-for-some-group`.**
- **No thin ghosts.** A spectral projection whose infinite expansion runs along a cyclic, free, hyperbolic or amenable
  subgroup gives no witness, for instance coefficients on arbitrarily long paths along one infinite cyclic subgroup.
- **Shape (a) must spread.** Its coefficients must spread over pattern shapes that no good subgroup tube contains, as the
  embedded expanders of a monster do.
- **Local tests for (b) and (c).** Any detector for shapes (b) or (c) must see configurations that are not supported in a
  good tube.

**Model tests.**
- For `H = {e}`, `Res` is the finite family of ranks on `Λ^F`, and item 2 is empty.
- For `H = G` satisfying Baum--Connes with coefficients and `F = {e}`, `Res` is the identity and item 2 is CEKN's
  isomorphism.
- For `G = Z` and `H = 2Z`, `F = {0, 1}`, one `Z`-cylinder orbit splits into two `2Z`-orbits, as item 1 says.

**Scope.**
- Torsion-free hosts only.
- The theorem constrains where a witness lives. It does not decide whether one exists.
- Bounded novelty check: the construction is not in CEKN Sections 1--2 nor in the predecessor artifacts. Web search was
  unavailable.
