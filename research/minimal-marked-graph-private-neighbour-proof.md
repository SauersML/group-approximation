---
rg: 2
id: minimal-marked-graph-private-neighbour-proof
kind: route
title: Align the denominators into one row, then cut with an opposite root
target: minimal-marked-graph-private-neighbour
requires: [kun-thom-nonsofic-wreath]
artifacts:
  - research/artifacts/kun-thom-private-neighbour-2026-08-18.md
---

## Direct proof

The prerequisite supplies the pair `Γ < G` and the marked element; everything
else below is self-contained.  Sections refer to
`research/artifacts/kun-thom-private-neighbour-2026-08-18.md`, which carries
the computations in full.

**Step 0 — the graph is symmetric and every root direction is marked.**
`δ = diag(-1,1,-1,1,…,1) ∈ SL_r(F_q) ⊆ Γ` conjugates `h = e₁₂(μ)` to
`h^{-1}`, so `D = D^{-1}`; a monomial matrix of determinant one carries `h`
to `e_{pq}(±μ)`, so `h_{pq} ∈ D` for all `p ≠ q`.  Both use `r ≥ 3` (to
absorb a sign at a third index) and Suslin stability
`SL_r(R₊) = EL_r(R₊) = Γ`.  (Artifact, Lemma 1.)

**Step 1 — denominators are ideals of infinite index.**  For `0 ≠ f ∈ R`,
`I_f = {a ∈ R₊ : af ∈ R₊} = x^{w⁻}R₊`, and `[R₊ : I_f] = ∞` when `f ∉ R₊`.
This is the denominator lemma already proved in
`marked-double-coset-infinite-degree-proof`; it is restated as Lemma 2 of the
artifact and is the only external input to Steps 3--4.

**Step 2 — `mD` is polynomial.**  For `M = Ah^{±1}B` with `A,B ∈ Γ`,
`mM = mAB ± AE₁₂B ∈ M_r(R₊)`, since `mμ = 1`.  (Artifact, Lemma 3.)

**Step 3 — the neighbour chart and its exact stabilizer.**  A block
computation valid in every characteristic gives

```text
h_{pq}^{-1}e_{qp}(a)h_{pq} ∈ Γ  ⟺  μa ∈ R₊ and μ²a ∈ R₊  ⟺  a ∈ m²R₊,
```

whence `z_a = e_{qp}(a)h_{pq}Γ` runs over an `R₊/m²R₊`-indexed family of
distinct neighbours of the base point.  (Artifact, Theorem 4 and
Corollary 5.)

**Step 4 — row alignment.**  Given `g₁Γ,…,g_sΓ ≠ Γ` in `N/Γ`, each `g_i` has
a nonpolynomial entry (else `g_i ∈ SL_r(R₊) = Γ`).  The shear
`v(a) = I + Σ_{j≥2}a_jE_{1j} ∈ Γ` fixes the base coset and makes the
`(1,k_i)` entry of `v(a)g_i` an affine function of `a`; the set where that
entry is polynomial is empty or a coset of a subgroup meeting one coordinate
axis in `I_f`, hence of infinite index.  A finite union of such cosets misses
a point (B. H. Neumann, or the box count of Step 6).  (Artifact, Lemma 6.)

**Step 5 — cut.**  With all competitors carrying a denominator in row `p`,
adjacency of `z_a` to `g_iΓ` forces, via
`row_p(mM_i) = (m+a)row_p(g_i) − row_q(g_i)` and Step 2, the condition
`af_i + c_i ∈ R₊` with `f_i ∉ R₊`; that is one coset of `I_{f_i}`.  Choosing
`a` outside the finitely many bad cosets makes `z_a` adjacent to the base
point and to no competitor.  (Artifact, Lemma 7.)

**Step 6 — assemble.**  `⟨Γ,h⟩ = N` (`notes/NOTEPAD.md`, `(AB5)`), so the
component of `Γ` is `N/Γ` and no edge crosses components.  Left-translate a
chosen `y ∈ F` to the base point, apply Steps 4--5 inside its component, and
translate back.  Since a private neighbour in one component has no
neighbours in the others, the general finite `F ⊆ X` follows.  (Artifact,
Theorem 8.)

## Scope

The route proves the claim as stated and nothing more.  It gives no
information about invariant graphs strictly larger than `S_min`, about the
action of `G` on the lamp algebra, or about any approximation property; and
it is non-effective only in the sense that Steps 4--5 pick a point outside a
finite union of cosets — Section 5 of the artifact makes even that choice
explicit and generic.
