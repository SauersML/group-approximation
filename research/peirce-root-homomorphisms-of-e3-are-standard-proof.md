---
rg: 2
id: peirce-root-homomorphisms-of-e3-are-standard-proof
kind: route
title: Matrix units from the Steinberg relations, with fullness in place of direct finiteness
target: peirce-root-homomorphisms-of-e3-are-standard
requires: []
artifacts:
  - research/artifacts/sk-iso-rigidity-2026-09-13-part1.md
---

**Peirce root groups.** For `x ∈ E_iME_k` and `y ∈ E_kME_j`, with `i, j, k` distinct:
- `x² = 0`, so `(1+x)^{-1} = 1−x`;
- `yx = 0` and `xyx = 0`, since `E_jE_i = 0`;
- so `[1+x, 1+y] = (1+x)(1+y)(1−x)(1−y) = 1 + xy`.

Also `(1+x)(1+x') = 1 + x + x'` for `x, x' ∈ E_iME_j`, so `P_ij ≅ (E_iME_j, +)`.

**The maps φ_ij.** `e_ij(r+s) = e_ij(r)e_ij(s)` makes `φ_ij: R → E_iME_j` additive, and it is bijective by
hypothesis. Applying `α` to `[e_ik(r), e_kj(s)] = e_ij(rs)` gives, for distinct `i, j, k`,

  (∗) `φ_ij(rs) = φ_ik(r) φ_kj(s)`.

With `s = 1`, `φ_ij(r) = φ_ik(r) a_kj`. With `r = 1`, `φ_ij(s) = a_ik φ_kj(s)`.

**Step 1: `a_ik a_ki = E_i` for `i ≠ k`.**
- Let `j` be the third index. Then `φ_ij(s) = a_ik φ_kj(s)` and `φ_kj(s) = a_ki φ_ij(s)`, so `φ_ij(s) = a_ik a_ki φ_ij(s)`
  for all `s`.
- Put `c = E_i − a_ik a_ki ∈ E_iME_i`. Since `φ_ij` is onto `E_iME_j`, `c E_iME_j = 0`, so `cME_j = 0`.
- So `c M E_j M = 0`. Fullness `M E_j M = M` gives `cM = 0`, so `c = 0`.

**Step 2: matrix units.**
- `a_ij a_jk = φ_ij(1)φ_jk(1) = φ_ik(1) = a_ik` for distinct `i, j, k`, by (∗).
- `a_ij a_ji = E_i` by Step 1.
- `a_ii a_ij = a_ij = a_ij a_jj`, since `a_ij ∈ E_iME_j`.
- `a_ij a_kl ∈ E_iME_jE_kME_l = 0` when `j ≠ k`.
- `Σ a_ii = Σ E_i = 1`.

This proves item 1.

**Step 3: θ is a ring isomorphism.**
- *Bijective.* `θ` is `φ_12` followed by `z ↦ z a_21`, which maps `E_1ME_2 → E_1ME_1` with inverse `z ↦ z a_12`, since
  `a_21a_12 = E_2` and `a_12a_21 = E_1`.
- *Unital.* `θ(1) = a_12a_21 = E_1`.
- *Multiplicative.* By (∗) with `k = 3`, `φ_12(rs) = φ_13(r)φ_32(s)`. Moreover `φ_13(r) = φ_12(r)a_23`,
  `φ_32(s) = a_31φ_12(s)` and `a_23a_31 = a_21`. So `φ_12(rs) = φ_12(r) a_21 φ_12(s)`, and
  `θ(rs) = φ_12(r)a_21φ_12(s)a_21 = θ(r)θ(s)`.

This proves item 2.

**Step 4: Θ.** By Step 2, `M = ⊕ E_iME_j`.
- *Multiplicative.* `Θ(rE_ij)Θ(sE_kl) = a_i1θ(r)a_1j a_k1θ(s)a_1l = δ_jk a_i1θ(r)E_1θ(s)a_1l = Θ(δ_jk rs E_il)`.
- *Unital.* `Θ(I) = Σ a_i1 E_1 a_1i = 1`.
- *Bijective.* The inverse is `z ↦ Σ θ^{-1}(a_1i z a_j1) E_ij`, using `a_i1 a_1i = E_i`.

**Step 5: `α = Θ` on generators.** We need `φ_ij(r) = a_i1θ(r)a_1j` for all `i ≠ j`, using the two consequences of (∗)
and the relations of Step 2:
- `(1,2)`: `θ(r)a_12 = φ_12(r)a_21a_12 = φ_12(r)`.
- `(1,3)`: `φ_13(r) = φ_12(r)a_23 = θ(r)a_12a_23 = θ(r)a_13`.
- `(2,1)`: `φ_21(s) = a_23φ_31(s) = a_23φ_32(s)a_21 = a_23a_31φ_12(s)a_21 = a_21θ(s)`.
- `(2,3)`: `φ_23(s) = a_21φ_13(s) = a_21θ(s)a_13`.
- `(3,1)`: `φ_31(s) = a_32φ_21(s) = a_32a_21θ(s) = a_31θ(s)`.
- `(3,2)`: `φ_32(s) = a_31φ_12(s) = a_31θ(s)a_12`.

So `α(e_ij(r)) = 1 + a_i1θ(r)a_1j = Θ(e_ij(r))`, and both are homomorphisms that agree on the generators of `E_3(R)`.
This proves item 3.

**Consequences.**
- *Standard ⇒ Peirce roots.* A standard homomorphism `g ↦ hΨ(g)h^{-1}`, with `Ψ` a ring isomorphism, maps `A_ij` onto
  the Peirce root groups of `E_k = hΨ(E_kk)h^{-1}`. These idempotents are full because `E_kk` is full in `M_3(R)`.
- *Converse.* Item 3.
- *`M = M_3(S)`, `E_k = E_kk`.* Then `E_11M_3(S)E_11 = S`.

**Model tests.**
- `R = S`, `M = M_3(S)`, `E_k = E_kk`, `α = id`: `a_ij = E_ij`, `θ = id`, `Θ = id`.
- `α = ` conjugation by `h ∈ GL_3(S)`: `E_k = hE_kkh^{-1}`, `a_ij = hE_ijh^{-1}`, `Θ = ` conjugation by `h`.
- *Fullness.* It is used once, in Step 1. If `E_iME_j = 0` for some `i ≠ j`, no bijection from `A_ij(R) ≠ 0` onto `P_ij`
  exists, so a vanishing Peirce space is excluded by the hypothesis. Whether fullness follows from bijectivity alone is
  not settled here.
