# Scale collapse for SFTs with a recognizable shape-consistent self-morphism

Lane bh-g2-labbe, 2026-09-18. Lane proof, elementary, unreviewed. It builds on Theorem A (§1–§5) of
`research/artifacts/labbe-covariant-tower-inflation-2026-09-16.md`, cited below as **TA**. All notation not
defined here is TA's.

## 0. Outcome

- **Theorem.** Let `Ω ⊆ A^(Z^2)` be an SFT with forbidden patterns in `B_r`. Let `ω` be a 2-dimensional morphism on
  `L(Ω)` that satisfies:
  - (H1) `ω(L(Ω)) ⊆ L(Ω)`;
  - (H2) every letter image has width and height `>= 2`;
  - (H3) `ω` is locally recognizable at radius `R` (§1).

  Put `D_* = max(r, 1, ⌈R/2⌉)`. Then a non-commuting `D`-family with `D >= D_*`, of any dimension, yields a
  non-commuting covariant `2D`-family. Hence `Ω` is quantum rigid iff it is `D_*`-rigid.
- **Labbé.** For `Ω_U` with `ω^2`: `r = 1`, and `R = 3` by exact computation
  (`research/artifacts/gq-bh-g2-labbe-recognizability-radius.md`). So `D_* = 2`.
- **What is new relative to TA.**
  1. Families of arbitrary dimension, and non-covariant ones, via covariantization (§2).
  2. Non-commutation is **transferred**. TA only needed existence of a module. Here, commutation of the tower family
     forces commutation of the parent (§4–§6). This is where recognizability enters.
- This is the letter-dependent-shape case that `self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale` left
  open ("Scope: … not claimed").

## 1. Setting

- **Balls.** `B_D = [−D, D]^2` (sup norm), as in TA.
- **`D`-family.** On a `k`-space `W` of any dimension: idempotents `E_a(z)` with
  - (Q1) a partition of unity at each `z`;
  - (Q2) `[E_a(z), E_b(z')] = 0` for `|z − z'|_∞ <= 2D`;
  - (Q3) `prod_(h∈B_D) E_(π(h))(z+h) = 0` for `π ∉ L_(B_D)(Ω)`.

  It is **covariant** if there are commuting invertibles `u_1, u_2` with `E(z) = u^z E(0) u^(−z)`.
- **`D`-rigid** means every `D`-family over `k` commutes. **Quantum rigid** means `D`-rigid for some `D >= r`.
- **Monotonicity.** A `(D+1)`-family is a `D`-family: for (Q3), expand an illegal `B_D`-pattern over its (illegal)
  extensions to `B_(D+1)`, whose factors commute. So `D`-rigid implies `(D+1)`-rigid.
- **Norms.** A sup-`D`-family is an `ℓ¹`-`D`-family, and an `ℓ¹`-`2D`-family is a sup-`D`-family. So quantum
  rigidity does not depend on the norm, and scale `2` below means sup-scale `2`.
- **Layouts.** For `x ∈ Ω`, the layout of `ω(x)` places the block `ω(x(c))` at `[X_(c_1), X_(c_1+1)) × [Y_(c_2), Y_(c_2+1))`.
  - `X_0 = Y_0 = 0`.
  - `X_(c+1) − X_c = w(x(c, 0))` and `Y_(c+1) − Y_c = h(x(0, c))` for all `c ∈ Z`, negative `c` included.
  - By TA (M1) and (M2) this is consistent, and it is a point of `Ω` by (H1).
  - The same formulas give the layout of a legal pattern `ρ` on a box.
- **(H3) Local recognizability at radius `R`.** There is a map `∂ : L_(B_R)(Ω) → A ⊔ {∗}` such that, for every
  `x ∈ Ω` and every `p ∈ Z^2`:
  - `∂(ω(x)|_(p + B_R)) = x(c)` if `p = (X_(c_1), Y_(c_2))`, the lower-left corner of the block of `c`;
  - `∂(ω(x)|_(p + B_R)) = ∗` otherwise.

  If `ω` is recognizable (unique `ω`-representations) and onto up to a shift, (H3) holds for some `R` by
  compactness. For Labbé it is verified directly.

## 2. Covariantization

**Lemma 1.** Given a `D`-family `(E_a(z))` on `W`, let `W'' = ⊕_(t∈Z^2) W` (algebraic direct sum).
- `E''_a(z)` acts on summand `t` as `E_a(z + t)`.
- `(u^g v)_t = v_(t+g)`.

Then `(W'', E'', u)` is a covariant `D`-family, and it commutes iff `(E_a(z))` does.

*Proof.* Everything acts summand-wise, so (Q1)–(Q3) hold. For covariance,
`(u^g E''(0) u^(−g) v)_t = E(t+g) v_t = (E''(g) v)_t`. Summand `0` carries the original family. ∎

## 3. TA in arbitrary dimension

The following hold for covariant `D'`-families of any dimension, with the same proofs:
- TA §2–§5: Lemma 1 (column- and row-constancy), Lemma 2 (the tower maps `A_l`, `B_l = A_l^(−1)` commute), the
  definition of `E_b(z) = A^z E_b(0) A^(−z)` on `W_T = ⊕_((i,j)∈I) P_(ij) W'`, Proposition 5, and Theorem A.

Finite dimension enters TA only in the dimension count. **Conventions**, from TA §3:
- `B_1` moves the pointer by `+e_1`. On leaving a block of width `m` it applies `u_1^(−1) M_(=m)(0)`.
- `A_1` moves the pointer by `−e_1`.
- `E_b(z)` reads the child letter at offset `z` from the pointer.
- The parent covariance gives `u_1^(−1) M(0) u_1 = M(−e_1)`.

## 4. Two-sided evaluation

Fix a covariant `D'`-family `(W', E', u)`, `D' >= 1`, its tower `(W_T, E, A)`, and `R >= 1` with
`R' := ⌈R/2⌉ <= D'`.
- `B_(R')` has sup-diameter `2R' <= 2D'`, so the `E'_a(c)`, `c ∈ B_(R')`, commute.
- `B_(R') ⊆ B_(D')`, so the evaluation map `ev := ev_(B_(R'))` kills illegal patterns (TA (E1), (E4), with `B_(R')`
  in place of `Q`).

For `(i,j) ∈ I`, `z ∈ B_R` and `b`, define `f^b_(ij,z)(ρ)` for `ρ ∈ L_(B_(R'))(Ω)`:
- it is `1` iff `ρ(0) ∈ S_(ij)` and the letter of the layout of `ρ` at `(i,j) + z` is `b`;
- it is `0` on illegal `ρ`.

The position lies in the layout, since widths are `>= 2`:
- `X_(−R') <= −2R' <= −R <= i + z_1`;
- `X_(R'+1) >= w(ρ(0)) + 2R' > i + R`;
- and likewise vertically.

**Lemma 2.** For `z ∈ B_R`, `E_b(z)` preserves every summand and `(E_b(z) v)_(ij) = ev(f^b_(ij,z)) v_(ij)`.

*Proof.* Induct along a lattice path from `0` to `z` whose coordinates move monotonically away from `0`.
- **Forward steps** (`z_1 >= 0`, to `z + e_1`). This is TA Proposition 5's computation. The shifted term
  `u_1 ev(f^b_(0j,z)) u_1^(−1)` stays inside `ev`: pointer at column `0`, offset `z_1 <= R − 1`, reads parent columns
  `<= ⌊z_1/2⌋` (TA Lemma 3), so `<= ⌊z_1/2⌋ + 1 <= R'` after the shift.
- **Backward steps** (`z_1 <= 0`, to `z − e_1`). Here `E_b(z − e_1) = B_1 E_b(z) A_1`. With the diagonal entries
  `F_(ij)` of `E_b(z)`, the formulas of TA §3 give:
  - `(B_1 E_b(z) A_1 v)_(i+1,j) = F_(ij) v_(i+1,j)`, since `F` commutes with `M(0)` and `v_(i+1,j) ∈ M_(>i+1)(0) W'`;
  - `(B_1 E_b(z) A_1 v)_(0j) = u_1^(−1) [Σ_m F_(m−1,j) M_(=m)(0)] u_1 v_(0j)`.

  Conjugation by `u_1^(−1)` moves an evaluation on parent sites `K` to `K − e_1` (TA (E3) with `g = −e_1`). The
  classical layout identities are:
  - within a block: `f_(i+1,j,z−e_1)(ρ) = f_(ij,z)(ρ)`;
  - at a block's left edge: `f_(0j,z−e_1)(ρ) = Σ_m [w(ρ(−e_1)) = m] f_(m−1,j,z)(ρ(· − e_1))`. The previous block
    starts at `−m`, and it has the same height by (M1).

  The support bound: pointer at column `m − 1 >= 1` with offset `|z_1| <= R − 1` reads parent columns
  `>= −⌈(R−2)^+/2⌉`, which is `>= −R' + 1`. After the shift the columns are `>= −R'`.
- **Vertical steps.** The same, with `A_2, B_2, u_2, N`.

Every intermediate function reads a child position in `(i,j) + B_R`, so all supports lie in `B_(R')`. ∎

## 5. Corner operators

Assume (H3) with radius `R`, and `⌈R/2⌉ <= D'`. For `a ∈ A`, the product below is well defined, since its factors
commute by Lemma 2. Define:
- `G_a := Σ_(π ∈ L_(B_R)(Ω), ∂(π) = a) prod_(h∈B_R) E_(π(h))(h)`;
- `Q_00 := Σ_a G_a`;
- `μ_m := Σ_(w(a)=m) G_a` and `η_n := Σ_(h(a)=n) G_a`.

**Lemma 3.** `G_a` acts as `E'_a(0)` on summand `(0,0)` and as `0` on every other summand. So:
- `Q_00` is the projection onto summand `(0,0)`;
- `μ_m = Q_00 M_(=m)(0)` and `η_n = Q_00 N_(=n)(0)`.

*Proof.*
1. By Lemma 2, on summand `(i,j)` the product for `π` is `ev(ρ ↦ [ρ(0) ∈ S_(ij)] [layout(ρ)|_((i,j)+B_R) = π])`.
2. For legal `ρ` the window `layout(ρ)|_((i,j)+B_R)` is legal: it is a sub-block of `ω(ρ)`, by (H1) and
   factoriality. So the sum over legal `π` with `∂(π) = a` gives `ev(ρ ↦ [ρ(0) ∈ S_(ij)] [∂(window) = a])`.
3. Extend `ρ` to `x ∈ Ω`. The window is `ω(x)|_((i,j) + B_R)`, and `(i,j)` lies in the block of `0`. By (H3),
   `∂ = x(0) = ρ(0)` if `(i,j) = (0,0)`, and `∂ = ∗` otherwise.
4. So the entry is `δ_((i,j),(0,0)) ev([ρ(0) = a]) = δ_((i,j),(0,0)) E'_a(0)`, by TA (E5). ∎

**Lemma 4 (corner calculus).** Identify operators `Y = Q_00 Y Q_00` with operators on `W' = P_00 W'`. For every
width `m`:
- (a) `Q_00 A_1^(−m) μ_m Q_00 = u_1^(−1) M_(=m)(0)`;
- (b) `Q_00 μ_m A_1^m Q_00 = M_(=m)(0) u_1`;
- (c) `Q_00 A_1^(−m) μ_m A_1^m Q_00 = M_(=m)(−e_1)`.

The same holds with `(A_2, u_2, η_n, N_(=n), −e_2)`.

*Proof.* Let `x ∈ P_00 W'`.
- **(a)** `B_1^m` moves `M_(=m)(0) x` along columns `1, …, m − 1` of its block. The terms
  `u_1^(−1) M_(=t)(0) M_(=m)(0)` vanish for `t < m`, and the vector wraps at step `m`. The result is
  `u_1^(−1) M_(=m)(0) x`, in summand `(0,0)`.
- **(b)** `A_1 x = Σ_(m') M_(=m')(0) u_1 x`, placed in summand `(m' − 1, 0)`: the last column of the previous block,
  of width `m'`. Further `A_1`-steps move left inside a block, and a piece leaves a block only from column `0`. So
  the `(0,0)`-component of `A_1^m x` is
  `Σ_(m_1+⋯+m_k = m) M_(=m_k)(0) u_1 ⋯ M_(=m_1)(0) u_1 x`.
  Now `μ_m` multiplies by `M_(=m)(0)`. Since every width is `>= 2`, only `k = 1` survives.
- **(c)** Apply (a) to the output of (b). This gives `u_1^(−1) M_(=m)(0) u_1 x = M_(=m)(−e_1) x`. ∎

## 6. Commutation descends

**Proposition 5.** Under the hypotheses of §5, suppose all `E_b(z)` (`b ∈ A`, `z ∈ Z^2`) commute. Then all
`E'_a(Z)` commute.

*Proof.*
1. **The algebra.** Let `𝒞` be the algebra generated by the `E_b(z)`. It is commutative. It is stable under
   `Y ↦ A^g Y A^(−g)`, since `A^g E_b(z) A^(−g) = E_b(z+g)`. It contains `G_a`, `Q_00`, `μ_m`, `η_n`.
2. **Restriction to the corner.** Each `Y ∈ 𝒞` commutes with `Q_00`, so it preserves `W' = P_00 W'`. Let `𝒞_00` be
   the commutative algebra of restrictions. By Lemmas 3 and 4(c), `𝒞_00` contains:
   - `E'_a(0)`, `M_(=m)(0)`, `N_(=n)(0)`;
   - `M_(=m)(−e_1)` and `N_(=n)(−e_2)`.
3. **Stability under the parent shift.** Let `X ∈ 𝒞_00`, the restriction of `X̃ = Q_00 X̃ Q_00 ∈ 𝒞`.
   - By Lemma 4(a),(b), `Σ_m (Q_00 μ_m A_1^m Q_00) X (Q_00 A_1^(−m) μ_m Q_00) = Σ_m M_(=m)(0) u_1 X u_1^(−1) M_(=m)(0)`.
     Since `X` commutes with `M_(=m)(−e_1) = u_1^(−1) M_(=m)(0) u_1`, the element `u_1 X u_1^(−1)` commutes with
     `M_(=m)(0)`, so the sum is `u_1 X u_1^(−1)`.
   - Each term is the restriction of `Q_00 μ_m (A_1^m X̃ A_1^(−m)) μ_m Q_00 ∈ 𝒞`. So `u_1 X u_1^(−1) ∈ 𝒞_00`.
   - In the same way, `Σ_m (Q_00 A_1^(−m) μ_m Q_00) X (Q_00 μ_m A_1^m Q_00) = u_1^(−1) X u_1`, using that `X`
     commutes with `M_(=m)(0)`. Each term is the restriction of `Q_00 (μ_m X̃ μ_m)(−m e_1) Q_00`. So
     `u_1^(−1) X u_1 ∈ 𝒞_00`.
   - The same argument works for `u_2^(±1)`.
4. **Conclusion.** By induction on `|Z|_1`, `E'_a(Z) = u^Z E'_a(0) u^(−Z) ∈ 𝒞_00`. So all `E'_a(Z)` commute. ∎

## 7. The theorem

**Theorem.** Assume (H1)–(H3) with radius `R`, and put `D_* = max(r, 1, ⌈R/2⌉)`. Fix a field `k`.
1. **Transfer.** For `D >= D_*`, every non-commuting `D`-family for `Ω` over `k` yields a non-commuting covariant
   `2D`-family for `Ω` over `k`.
2. **Collapse.** The following are equivalent: `Ω` is quantum rigid; `Ω` is `D_*`-rigid; `Ω` is `D`-rigid for every
   `D >= D_*`. By `sft-crossed-product-fp-iff-quantum-rigid`, `LC(Ω,k) ⋊ Z^2` is finitely presented iff `D_*`-local
   operator tilings commute. In the notation of `sft-wall-rigidity-iff-idempotent-commutator-ideal`, this means
   `J_(D_*) = 0`.

*Proof.*
1. Covariantize (Lemma 1), and apply TA Theorem A, in any dimension (§3), with `D' = D`. The result is a covariant
   `2D`-family. By Proposition 5 (with `⌈R/2⌉ <= D`) it commutes only if the covariantized family commutes, and so
   only if the original family commutes.
2. `D_*`-rigid implies `D`-rigid for `D >= D_*` (monotonicity), and both imply quantum rigid. Conversely, suppose
   `Ω` is `D_0`-rigid but some `D`-family with `D >= D_*` does not commute. Item 1 gives non-commuting families at
   scales `2^j D`, and `2^j D >= D_0` for large `j`. By monotonicity this contradicts `D_0`-rigidity. ∎

## 8. Labbé's shift

- **(H1), (H2).** `ω^2` satisfies them (TA §6, Theorem C; exact check 4: minimum side `2`). Also `r = 1`
  (nearest-neighbor Wang shift, `minimal-aperiodic-wang-shift-exists`).
- **(H3) at `R = 3`.** This is exact, in `gq-bh-g2-labbe-recognizability-radius.md`. Every legal `7×7` window
  determines whether its center is an `ω^2`-block corner, and if so the parent letter. The computation finds 420
  legal `7×7` windows and no conflict. At `R = 2` there are conflicts, so `R = 3` is optimal for `ω^2`. The single
  morphism `ω` is recognizable at `R = 1` (94 legal `3×3` windows), but it violates (H2).
- **Corollary.** `D_* = max(1, 1, 2) = 2`. Over every field `k`, the following are equivalent:
  - `Ω_U` is quantum rigid;
  - it is `2`-rigid, meaning every family of 19-tile idempotent partitions, in any dimension, that commutes at
    sup-distance `<= 4` and kills the non-occurring `5×5` patterns, commutes (there are 229 legal `5×5` patterns);
  - it is `D`-rigid for every `D >= 2`.
- **Group side.** By `zd-derived-full-group-fp-forces-quantum-rigidity`, if `char k ∉ {3,5}`, one non-commuting
  `2`-family over `k` makes both `LC(Ω_U,k) ⋊ Z^2` and `D([[Ω_U]])` non-finitely presented.

## 9. Checks and limits

- **Constant shape.** `self-similar-sfts-are-quantum-rigid-iff-rigid-at-one-scale` needs no recognizability: its
  block grid `NZ + [0,N)^2` is fixed. Here the grid is operator valued (the tower pointer). Recognizability is used
  exactly once, to put `Q_00` into the child algebra (Lemma 3). Without it, the compression of a commutative algebra
  by a non-commuting projection need not be commutative.
- **Walls (item 3 of the claim node).** Upper-triangular families have an invariant filtration with classical
  quotients. Covariantization and the tower preserve such a filtration, and the quotients stay classical, since the
  tower is built from `E'(0)` and `u^(±1)`. So a wall certificate at a scale `D >= D_*` gives a non-commuting
  filtered family at scale `2^j D` for every `j`. By `sft-wall-rigidity-iff-idempotent-commutator-ideal`, item 4,
  that contradicts wall rigidity at large scale. Hence, if `labbe-shift-is-wall-rigid` holds, `Ω_U` is
  `2`-wall-rigid. The partition data agrees: fault hits come in adjacent rows, columns and anti-diagonals, or in one
  golden digital strip of thickness `φ^2` (claim node `labbe-shift-is-quantum-rigid-iff-rigid-at-scale-two`).
- **Determinism.** By `determinism-closure-certifies-quantum-rigidity`, determinism closures fail for `Ω_U` at every
  scale, `2` included. A proof of `2`-rigidity has to be contextual. It must cross fault normals at resonant
  separations. By the transfer, it may use relations at any larger scale, since `J_2 = 0` iff `J_D = 0` for one,
  equivalently every, `D >= 2`.
- **Not decided.** Whether `J_2(Ω_U) = 0` is still open. The theorem only fixes where the answer lives.
- **Two shifts.** Proposition 5 applies to any `ω : L(Ω_S) → L(Ω_T)` with (H2), and with (H3) on the layouts
  `ω(x)`, `x ∈ Ω_S`. A non-commuting `Ω_S`-family at scale `D >= max(r_S, 1, ⌈R/2⌉)` then gives a non-commuting
  `Ω_T`-family at scale `2D`. Without a self-morphism of `Ω_T` this is one doubling, not an iteration. So if `Ω_T` is
  `D_0`-rigid, then `Ω_S` is `D`-rigid for all `D >= max(r_S, 1, ⌈R/2⌉, ⌈D_0/2⌉)`; in particular, `Ω_T` quantum
  rigid implies `Ω_S` quantum rigid. Chains of recognizable morphisms, such as Labbé's substitutive description of
  Jeandel–Rao-type shifts, would transport rigidity along the chain. Their (H3) radii were not computed here.
