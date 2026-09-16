---
rg: 2
id: weak-matricial-stability-kills-centralizer-even-cohomology
kind: claim
title: Weakly matricially stable linear groups have rationally even-acyclic torsion centralizers
distinct_from:
  dadarlat-matricial-stability-obstruction: that imports Dadarlat's theorems, which see the even rational cohomology of the whole group, i.e. only the sector g = 1; this asks the same vanishing for the centralizer of every finite-order element, which is strictly stronger (the toy group (Z^2 x Z/3) x| Z/2 of the artifact has H^{2k}(G;Q) = 0 but a torsion centralizer with H^2 = Q).
  exel-loring-relative-quasirep-invariant: that is an invariant on H_2(G;Z) of the whole group, built from quasi-representations of G; this concerns even rational cohomology of centralizers of torsion elements, seen on eigenspaces of the torsion element.
  finite-order-root-cannot-carry-a-corona-bott-class: that shows a corona pair one of whose members has finite order carries no Bott class; here the finite-order element only cuts out an eigenspace, and the pair compressed to that eigenspace consists of infinite-order centralizer elements.
artifacts:
  - research/artifacts/laurent-sl4-delocalized-bott-2026-09-16.md
---

**OPEN.** Let `G ⊂ GL_n(K)` be a finitely generated linear group over a field `K`. Suppose `G` is weakly
matricially stable, in Dadarlat's sense as quoted in `dadarlat-matricial-stability-obstruction` (every sequence of
ucp maps satisfying his condition (1) is, after padding with homomorphisms, pointwise close to homomorphisms). Then
`H^{2k}(Z_G(g);Q) = 0` for every finite-order `g ∈ G` and every `k ≥ 1`.

**Relation to known results.**
- For `g = 1` this is contained in Dadarlat's Corollary 1.3 (arXiv:2007.12655), quoted in
  `dadarlat-matricial-stability-obstruction`, which covers all countable linear groups.
- The statement is the "delocalized" form of that corollary: the conjugacy classes of finite-order elements are the
  sectors of the delocalized Chern character of `K^0_G(E̲G)`, and the `(g)`-sector computes `H^*(Z_G(g);Q)`.

**Evidence (artifact §§1–2, 5).**
- *Elementary obstruction.* For commuting `s_1, s_2 ∈ Z_G(g)` and an `ord(g)`-th root of unity `ω`, the Bott index
  `β_ω` of the polar parts of the compressions of `φ_n(s_1), φ_n(s_2)` to the `ω`-spectral projection of `φ_n(g)` is
  defined for large `n` for every asymptotic homomorphism `φ_n`. It vanishes on homomorphisms, is invariant under
  pointwise `o(1)` perturbation, and is additive under direct sums (artifact Lemmas 1.1–1.3). So `β_ω ≠ 0` obstructs
  matricial stability and its padded variant for unitary asymptotic homomorphisms (artifact Corollary 1.4).
- *The sector phenomenon is real.* `G = (Z^2 × Z/3) ⋊ Z/2` (the reflection acting by `(u,v,w) ↦ (u, v^{-1}, w^{-1})`)
  has `H^{2k}(G;Q) = 0` for all `k ≥ 1`, so Dadarlat's theorems are silent. But `Z_G(w) = Z^2 × Z/3` has
  `H^2 = Q`, and an explicit asymptotic homomorphism has `β_ω = +1`, `β_ω̄ = −1` (artifact Proposition 2.3,
  replayed numerically in `experiments/laurent-sl4-delocalized-bott-2026-09-16/`). So `G` is not matricially stable.
  This is not a test of this claim, which is an implication in the other direction.
- *Consistency.* Finite groups, virtually free groups, and the twelve stable wallpaper groups listed in Dadarlat's
  2024 survey all have torsion centralizers with `H^{2k}(;Q) = 0` for `k ≥ 1` (artifact §5).

**What it would give.** Route `laurent-sl4-instability-from-delocalized-dadarlat`: for `q ≥ 4` and
`g = diag(a, a^{-1}, 1, 1)` with `a² ≠ 1`, `H^2(Z_Λ(g);Q) ≠ 0` for `Λ = SL_4(F_q[t,t^{-1}])`, so this claim
refutes matricial stability of `Λ`.

## Attempts

- **Dadarlat's proof run over `E̲G` instead of `BG` (artifact §5, steps P1–P6).** The plan:
  - (P1) Kasparov's surjection `γKK^G(C,C) → RK^0_G(E̲G)`.
  - (P2) quasidiagonality of `γ`-classes (survey Theorem 6.1, read at source).
  - (P3) realize a quasidiagonal class on a proper cocompact `Y ⊂ E̲G` by pushing the cutoff projection
    `p_Y ∈ C_c(Y) ⋊ G` through the coaction `f u_s ↦ f u_s ⊗ u_s` and the compressions of a quasidiagonal Cuntz pair.
  - (P4) weak matricial stability turns the result into a difference of flat equivariant bundles.
  - (P5) flat bundles have delocalized Chern character concentrated in degree 0 in every sector.
  - (P6) `E̲G^g` is a model for `E̲Z_G(g)`, and `lim^1` vanishes, so a nonzero class in `H^{2k}(Z_G(g);Q)` is seen
    on some `Y`.
  - **Where it dies.** (P3) is an adaptation of Dadarlat's Mishchenko-projection argument that I have not seen
    written. The survey's sketch assumes `G` torsion free "for simplicity", and the agreement of the cutoff
    realization with Kasparov's restriction map is unproven. (P1), the normalization of Lück's delocalized Chern
    character in (P5), and the `Q`-coefficient `lim^1` step in (P6) are recalled, not read.
- **The invariant `β_ω` gives only the obstruction direction.** Lemmas 1.1–1.4 of the artifact show that a nonzero
  `β_ω` refutes stability. This claim needs the converse realization: a nonzero centralizer class must be *produced*
  by some asymptotic homomorphism. That realization problem is exactly (P1)–(P3).
- **Explicit induced models do not realize it in the application.** For `N ⊴ G` of finite index with `⟨g⟩ ∩ N = 1`,
  induced asymptotic homomorphisms have `β_ω` independent of `ω` (artifact Lemma 4.1). In `Λ`, Weyl antisymmetry then
  forces `β_ω = 0` (artifact Corollary 4.2). So a proof for `Λ` cannot come from inducing from such `N`.
