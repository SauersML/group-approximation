---
rg: 2
id: topologically-free-matricial-crossed-el-simple-kazhdan-lef
kind: claim
title: For a minimal topologically free Cantor action of a finitely generated group whose binary crossed product is finitely generated and maps unitally into a matrix ultraproduct, EL_n over it is infinite finitely generated simple Kazhdan LEF
distinct_from:
  binary-el-simple-iff-minimal-topologically-free: that is the simplicity equivalence over F_2 for any countable acting group; this adds finite generation, property (T) and LEF under the matricial hypothesis, stated as the single Theorem 2 of the unified note.
  finite-model-subshift-elementary-groups-simple-kazhdan-lef: that assumes a free action with finite pattern models; this assumes only topological freeness and a unital homomorphism into a matrix ultraproduct, which covers the non-free lamplighter host.
  lamplighter-bernoulli-crossed-products-simple-kazhdan-lef: that is one instance of this claim, the lamplighter action of Z/2 wr Delta on 2^Delta, proved there through the Steinberg criterion.
  exactly-matricial-rings-have-lef-general-linear-groups: that needs an injective embedding and gives LEF of GL_N; here the homomorphism need not be injective, and simplicity of EL_n supplies injectivity on the group.
artifacts:
  - research/artifacts/sk-simpler-unify-proposal-2026-09-13.md
  - research/artifacts/sk-simpler-unify-proposal-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed; queued with sk-verify-7).**
- **Hypotheses:**
  - a finitely generated group `L` acts minimally on a Cantor set `Z`;
  - no nontrivial element of `L` fixes a nonempty open set;
  - `R = LC(Z,F_2) ⋊ L` is finitely generated as a ring;
  - `R` has a unital ring homomorphism into an algebraic ultraproduct `∏_ω M_{N_k}(F_2)`.
- **Conclusion:** for every `n ≥ 3`, the group `EL_n(R)` is infinite, finitely generated, simple, LEF, and has property (T).

Instances:
- The note's Theorem 1: `L = Z` acting on an infinite minimal subshift, with the periodic-word models.
- The lamplighter host of `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`, with the models `F_2^{Q_n} × Q_n`.
- The Toeplitz envelopes of `rf-toeplitz-subshifts-over-residually-finite-groups`, using `residually-finite-actions-give-matricial-crossed-products`.

A non-instance (model test):
- The boundary action of `F_d` on `∂F_d` is minimal and topologically free, and its crossed product is finitely generated.
- It has no unital homomorphism into any matrix ultraproduct over `F_2`. Its Leavitt family `s_i^* s_j = δ_ij 1`, `Σ_i s_i s_i^* = 1` would force normalized rank `1 = d`.
- Correspondingly, the resulting group is nonsofic (on main).

This claim is Theorem 2 of the unified candidate in `research/artifacts/sk-simpler-unify-proposal-2026-09-13.md`. Its §1 gives a complete elementary proof (clopen towers, one copy of `GL_d(F_2)`, the level ideal, the kernel argument for LEF).

Route: `topologically-free-matricial-crossed-el-simple-kazhdan-lef-proof`.

**Review (sk-verify-8, 2026-09-13, `research/artifacts/sk-review-8-2026-09-13-part3.md`):** PASS (§1). Re-derived: density of small sets by topological freeness; the commuting criterion and the scalar step (`c = 1` from the constant coefficient of `cc^(-1)`); the tower matrix units, and the product formula `f u_a e_V f′u_b ∈ {0, ε_(a,b^(-1))}` for a symmetric generating set; simplicity of `GL_d(F_2)`; the level ideal with covering; LEF through the kernel missing `e_12(1)`; and the three instances. The unified candidate's §2 LaTeX drops rev3's `e_ij(1)` clause (G1′, §2 of the artifact). Keep rev3 l.167–181 verbatim.
