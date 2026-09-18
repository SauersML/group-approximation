---
rg: 2
id: recognizable-morphism-scale-collapse-proof
kind: route
title: Covariantize, inflate on the operator tower, evaluate child idempotents two-sidedly on a small parent ball, and use recognizability to recover the corner projection; compressions by width projections then conjugate the corner by the parent translations
target: recognizable-morphisms-collapse-quantum-rigidity-to-one-scale
requires:
  - morphism-towers-double-covariant-tiling-scales
  - sft-crossed-product-fp-iff-quantum-rigid
  - sft-wall-rigidity-iff-idempotent-commutator-ideal
artifacts:
  - research/artifacts/gq-bh-g2-labbe-morphic-scale-collapse.md
---

The full proof is in the artifact, §1–§7. Notation follows `morphism-towers-double-covariant-tiling-scales` (TA):
- `W_T = ⊕_((i,j)) P_(ij) W'` is the tower;
- `A_l` are the tower translations, with `B_l = A_l^(−1)` moving the pointer by `+e_l`;
- `M_(=m)(0)` and `N_(=n)(0)` are the parent width and height projections.

1. **Covariantization** (artifact Lemma 1). On `⊕_(t ∈ Z^2) W`, let summand `t` carry `E(z + t)`, and let `u^g` shift
   the summands. The result is a covariant `D`-family, and it commutes iff the original family does.
2. **TA in any dimension** (§3). TA §2–§5 use no finiteness except in the dimension count.
3. **Two-sided evaluation** (Lemma 2). Put `R' = ⌈R/2⌉ <= D'`.
   - For `z ∈ B_R`, `E_b(z)` acts on summand `(i,j)` as `ev_(B_(R'))(f^b_(ij,z))`. Here `f^b_(ij,z)(ρ)` is the
     indicator that `ρ` is legal, that `ρ(0) ∈ S_(ij)`, and that the layout of `ρ` has letter `b` at `(i,j) + z`.
   - Induct along a lattice path that moves away from `0`. Forward steps are TA Proposition 5.
   - Backward steps use `E_b(z − e_1) = B_1 E_b(z) A_1`. The tower formulas give:
     - `F_(ij)` on components `(i+1, j)`;
     - `u_1^(−1)[Σ_m F_(m−1,j) M_(=m)(0)] u_1` on `(0,j)`.

     These are the operator form of the layout identity at a block's left edge. Widths `>= 2` keep every support in
     `B_(R')`.
4. **Corner operators** (Lemma 3). Put `G_a = Σ_(π legal, ∂π = a) prod_(h ∈ B_R) E_(π(h))(h)`. On summand `(i,j)` it is
   `ev(ρ ↦ [∂(ω-window at (i,j)) = a])`. By (H3) this is `δ_((i,j),(0,0)) E'_a(0)`. So `Q_00 = Σ_a G_a` is the corner
   projection, and `μ_m = Σ_(w(a)=m) G_a = Q_00 M_(=m)(0)`.
5. **Corner calculus** (Lemma 4). With widths `>= 2`:
   - `B_1^m` carries `M_(=m)(0) x` once around its block, so `Q_00 A_1^(−m) μ_m Q_00 = u_1^(−1) M_(=m)(0)`;
   - the only composition of `m` into widths that ends in `M_(=m)` is `m` itself, so
     `Q_00 μ_m A_1^m Q_00 = M_(=m)(0) u_1`;
   - hence `Q_00 A_1^(−m) μ_m A_1^m Q_00 = M_(=m)(−e_1)`.
6. **Descent** (Proposition 5). Suppose the child family commutes. Its algebra `𝒞` is commutative and stable under
   `A`-conjugation, and it contains `Q_00` and `μ_m`. The corner `𝒞_00` is commutative and contains `E'_a(0)`,
   `M_(=m)(0)` and `M_(=m)(−e_1)`.
   - For `X ∈ 𝒞_00`, `Σ_m M_(=m)(0) u_1 X u_1^(−1) M_(=m)(0) = u_1 X u_1^(−1)`, because `X` commutes with
     `u_1^(−1) M_(=m)(0) u_1`.
   - Each term is the corner of `μ_m A_1^m X̃ A_1^(−m) μ_m ∈ 𝒞`, since `A_1^(−m) μ_m` maps into the corner.
   - The inverse direction and `u_2` are similar.
   - So `𝒞_00 ∋ E'_a(Z)` for all `Z`, and the parent family commutes.
7. **Theorem** (§7).
   - Item 1 is 1 + 2 + 6.
   - Item 2 follows from item 1 together with monotonicity: a `(D+1)`-family is a `D`-family.
   - Item 3: covariantization and the tower preserve an invariant filtration whose quotients are classical. So a
     non-commuting filtered family at scale `D >= D_*` gives one at scale `2^j D`, which contradicts
     `sft-wall-rigidity-iff-idempotent-commutator-ideal`, item 4, at large scale.
   - Item 4 is the same proof with `Ω_S ≠ Ω_T`. Steps 3–6 use (H3) only on layouts of `ω(Ω_S)`.
