---
rg: 2
id: dihedral-cantor-crossed-product-k1-has-exponent-four
kind: claim
title: If an infinite minimal Cantor system (Y,S) has an involution P with PSP = S^(−1), then K_1(LC(Y,F_2)⋊D_∞) is killed by 4, so no matrix ring over it is a matrix ring over LC(X,F_2)⋊Z for an infinite minimal Cantor system X
distinct_from:
  binary-subshift-ring-k1-is-half-orbit-index: that identifies K_1 of a minimal Z-crossed product over F_2 with Z through the half-orbit index; this uses it as input and shows that an orientation-reversing index-two extension makes K_1 4-torsion
  minimal-cantor-crossed-product-k-theory-formula: that computes K_n of Z-crossed products through the twisted Laurent fibration; this handles D_∞-crossed products by restriction of scalars along an index-two subring, with no fibration
artifacts:
  - research/artifacts/dihedral-cantor-k1-exponent-four-2026-09-16.md
---

**Setting.**
- `(Y,S)` is an infinite minimal Cantor system.
- `P: Y → Y` is a homeomorphism with `P² = id` and `PSP = S^(−1)`.
- `⟨S,P⟩ ≅ D_∞` acts on `Y`, and `A = LC(Y,F_2) ⋊ D_∞` with `δ_g f δ_g^(−1) = f∘g^(−1)`.
- `A′ = LC(Y,F_2) ⋊_S Z ⊆ A` is the rotation part.

**Statement.**
1. **(Transfer doubles.)** Let `i_*: K_1(A′) → K_1(A)` be induced by inclusion and `tr: K_1(A) → K_1(A′)` by
   restriction of scalars along `A = A′ ⊕ A′δ_P`. Then `i_* ∘ tr = 2`. This holds for any `F_2`-algebra `A` with a unit
   `v` such that `vA′v^(−1) = A′`, `v² ∈ A′` and `A = A′ ⊕ A′v`.
2. **(Exponent four.)** `4·K_1(A) = 0`.
3. **(Not a Z-crossed product.)** For every infinite minimal Cantor system `(X,T)` and all `m, n ≥ 1`,
   `M_m(A) ≇ M_n(LC(X,F_2) ⋊_T Z)` as rings.

**Why.**
- `δ_P δ_S δ_P^(−1) = δ_S^(−1)`, so the generator `[δ_S]` of `K_1(A′) ≅ Z` becomes 2-torsion in `K_1(A)`.
- Over `F_2`, restriction of scalars followed by induction is multiplication by 2. The kernel of multiplication
  `A ⊗_(A′) A → A` is `A(1⊗v + v⊗1)`, a bimodule twisted by the inner automorphism `Ad(v)`, hence isomorphic to `A`.
- By contrast `K_1(LC(X,F_2) ⋊ Z) ≅ Z` (`binary-subshift-ring-k1-is-half-orbit-index`), and `K_1` is Morita invariant.

**Generalisation (artifact §5, Proposition 5).** Let `G ⊇ H` be ample Hausdorff groupoids with `H` clopen and
`H^(0) = G^(0)`. Let `B` be a compact open full bisection with `G = H ⊔ HB`, `BHB^(−1) = H` and `BB ⊆ H`. Suppose
conjugation by `1_B` acts as `−id` on `K_1(A_(F_2)(H))`. Then `4·K_1(A_(F_2)(G)) = 0`.

**Scope.**
- No freeness or effectiveness is assumed.
- Over a ring with `2 ≠ 0` the transfer gives `x + θ′_*(x)` instead of `2x`, and the argument yields no torsion
  bound. Characteristic 2 makes the twisting automorphism inner.
- An exact check of the bimodule identities on finite crossed products `F_2^(Z/n) ⋊ D_n` is in
  `experiments/dihedral-cantor-k1-exponent-four-2026-09-16/`.

Proof in the `-proof` route and the artifact §1–§3. Unreviewed.
