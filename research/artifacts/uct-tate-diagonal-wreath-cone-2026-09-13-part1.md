# The Tate diagonal is the crossed product of one weakly contractible wreath object (part 1)

Lane ex3-uct-tate-diagonal, 2026-09-13. Unreviewed. Continues
`research/artifacts/uct-kk-norm-functor-2026-09-13-part3.md` §9–11 and uses its notation:
`G = Z/p = <σ>`, `1_T = cone(P → C)` the Tate object, `N` the norm functor, `D = C*_r(Γ)`,
`Δ : τ(D) → N(D)` the diagonal, `T(Δ) = 1_T ⊗ Δ`, `Z_Γ = cone(T(Δ))`.

**Sources read from the PDFs on 2026-09-13.**
- **Meyer–Nest, arXiv:math/0312292v3.**
  - Prop. 4.4: `N` is weakly contractible iff `KK(P, N) = 0` for all `P ∈ CI`.
  - Def. 4.5 and Thm. 4.7: `<CI>` and `CC` are complementary. The Dirac triangle is
    `ΣN → P → C_0(X) → N`, with `P(A) ≅ P ⊗ A` and `N(A) ≅ N ⊗ A`, and `A ∈ CC` iff `P ⊗ A ≅ 0`.
  - p. 24: `Obs F(A) ≅ F(N ⊗ A)`.
  - Thm. 5.2: the assembly map with coefficients `A` is an isomorphism iff
    `K_*((G ⋉ X) ⋉_r^Obs A) ≅ 0`.
  - Thm. 8.3: if a dual Dirac morphism exists, `γ_A = 0` iff `A ∈ CC`, and `γ_A = id` iff `A ∈ <CI>`.
  - Thm. 8.5: for a-T-menable groups, weakly contractible objects are `0`.
- **Nishikawa–Petrosyan, arXiv:2509.15070v2.**
  - Def. 4.1.
  - Thm. 5.2: if `G` acts isometrically, continuously and properly on a weakly geodesic, uniformly
    locally finite hyperbolic metric space, then for every compact `F` and finite `F`-set `Ω`,
    `G ≀_Ω F` satisfies Baum–Connes with coefficients.
  - p. 26: the γ-element definitions (classical sense and Meyer–Nest sense).

## 1. Setting

- `Γ` is a torsion-free countable discrete group and `p` a prime.
- `W := Γ ≀ G = Γ^p ⋊ G` with quotient map `q : W → G`. The shift acts by `(σ·c)_i = c_(i−1)` (indices mod `p`).
- `H := ΔΓ × <σ>`.
- A `G`-algebra is a `W`-algebra through `q`, written `q^*`.
- `ε := [ℓ²(W/H)] ∈ KK^W(C_0(W/H), C)`, with `C_0(W/H)` acting by multiplication, hence by compacts,
  and operator `0`.
- `Y := cone(ε) ⊗ q^*(1_T) ∈ KK^W`.

## 2. Group theory

**Lemma 1.**
- (a) `N_W(<σ>) = C_W(σ) = H`.
- (b) Every nontrivial finite subgroup of `W` is conjugate to `<σ>`.
- (c) For `F = w<σ>w^(−1)`, the only `F`-fixed point of `W/H` is `wH`, and every other `F`-orbit is free.

*Proof.*
- (a) `G` is abelian, so `wσw^(−1) ∈ Γ^p σ`. Hence `wσw^(−1) ∈ <σ>` forces `wσw^(−1) = σ`.
  An element `cσ^k` commutes with `σ` iff `σ·c = c`, iff `c` is constant.
- (b) `Γ^p` is torsion-free, so a finite `F` injects into `G`. If `F ≠ 1`, choose a generator
  `w = cσ`. Then `w^p = c(σ·c)⋯(σ^(p−1)·c)`, whose first coordinate is `c_1 c_p c_(p−1) ⋯ c_2`, and the
  other coordinates are cyclic conjugates of it. So `w^p = 1` iff `c_1 c_p ⋯ c_2 = 1`.
  Put `b_1 = 1` and `b_i = c_i b_(i−1)` for `2 ≤ i ≤ p`. Then `c_i = b_i b_(i−1)^(−1)` for `i ≥ 2`, and
  `c_1 = b_1 b_p^(−1)` is exactly the relation `c_1 c_p ⋯ c_2 = 1`. So `c = b·(σ·b)^(−1)`, i.e.
  `bσb^(−1) = cσ`. (This is `H^1(Z/p; Coind Γ) = H^1(1; Γ) = pt`.)
- (c) The case `F = <σ>` is part 3, Lemma 4 (`Γ` torsion-free). The general case follows by conjugation. ∎

## 3. Theorem A

1. `Res^W_F Y ≃ 0` for every finite `F ≤ W`. So `Y ∈ CC_W`, and in addition `Res^W_(Γ^p) Y ≃ 0`.
2. `W ⋉_r Y ≅ cone(T(Δ) ⋊ G) = Z_Γ ⋊ G`, compatibly with the dual `Ĝ`-actions through `q`.
3. `T(Δ) ⋊ G` is a KK-equivalence iff `W ⋉_r Y ≃_KK 0`. `T(Δ)` is a `KK^G`-equivalence iff
   `W ⋉_r Y ≃ 0` in `KK^Ĝ`.
4. If `W` satisfies Baum–Connes with coefficients, then `K_*(W ⋉_r (Y ⊗ B)) = 0` for every separable
   `W`-algebra `B`. This holds for every torsion-free hyperbolic `Γ` by Nishikawa–Petrosyan Thm. 5.2,
   with `F = Ω = G`. Examples: torsion-free uniform lattices in `Sp(n,1)`, which act properly and
   cocompactly by isometries on quaternionic hyperbolic space.
5. If `Γ` is a-T-menable, then `Y ≅ 0` in `KK^W`, so `T(Δ)` is a `KK^G`-equivalence. Here `W` is
   a-T-menable as a finite extension of `Γ^p`, and Meyer–Nest Thm. 8.5 applies.

*Proof.*
1. **Finite subgroups.**
   - `F = 1`: `Res^G_1 1_T ≃ 0`.
   - `F = w<σ>w^(−1)`: as an `F`-algebra, `C_0(W/H)` is the `c_0`-direct sum over `F`-orbits, and `ε`
     splits accordingly. The fixed orbit `{wH}` contributes `id_C`. A free orbit `O` contributes a map
     out of `C(O) ⊗ q^*1_T ≅ Ind_1^F Res^F_1 1_T ≃ 0`, since `F → G` is an isomorphism. Countable direct
     sums exist in `KK^F` and cones commute with them. So `Res_F(ε ⊗ 1)` is an equivalence and its cone
     vanishes.
   - `Γ^p`: `Res^W_(Γ^p) q^*1_T` is the inflation of `Res^G_1 1_T ≃ 0`.
2. **Crossed product.** Descent is triangulated, so `W ⋉_r Y = cone(j_r^W(ε ⊗ 1_A))` with `A = q^*1_T`.
   - The projection `δ_H ∈ C_0(W/H)` is full in `W ⋉_r (C_0(W/H) ⊗ A)`, and its corner is
     `H ⋉_r Res A` (Green imprimitivity).
   - Cut down to that corner, `j_r^W(ε ⊗ 1_A)` is the module `δ_H·(ℓ²(W/H) ⊗ W ⋉_r A) ≅ W ⋉_r A`, on
     which `H ⋉_r A` acts by left multiplication through the inclusion. That action is compact, so the
     class is the class of the inclusion `ι : H ⋉_r A → W ⋉_r A`.
   - `H ⋉_r A = 1_T ⋊_r (Γ × G) = (1_T ⊗ τD) ⋊ G` and `W ⋉_r A = (1_T ⊗ N D) ⋊ G`, so
     `ι = T(Δ) ⋊ G` (part 3, §11(b)).
   - `Ĝ` acts on both sides by characters through `q`, and `ι` is equivariant.
3. The first statement is the cone of 2. The second is Baaj–Skandalis duality for finite abelian `G`
   (standard, not re-read): `KK^G(A, B) ≅ KK^Ĝ(A ⋊ G, B ⋊ G)`.
4. `CC` is a tensor ideal (Meyer–Nest Lemma 4.2), so `Y ⊗ B ∈ CC`. Then `N ⊗ (Y ⊗ B) ≅ Y ⊗ B`
   (Thm. 4.7), so the obstruction functor at `Y ⊗ B` equals `K_*(W ⋉_r (Y ⊗ B))`, which vanishes by
   Thm. 5.2.
5. Meyer–Nest Thm. 8.5. ∎

**Remarks.**
- 4 replaces the sketch in part 3 §11(c) ("cellular localization step not fully checked"). No
  localization onto the `σ`-singular set is needed, because the singular stratum is already cancelled
  inside `Y`.
- **The Skandalis summand, exactly.** Assume `W` has a γ-element. For `Γ ≤ Sp(n,1)` this comes from
  Kasparov's construction for discrete subgroups of the almost connected Lie group
  `Sp(n,1)^p ⋊ G` (recalled, not re-read). Then `Y = (1 − γ_W)Y` by Thm. 8.3.
  - So part 3 §11(e)'s map between `(1 − γ)`-parts is the crossed product of one concrete object `Y`.
  - `Y` is contractible on the finite-index subgroup `Γ^p`, not only on finite subgroups.
- The answer depends on `Γ` only through `W` and `Y`. It is independent of `n` and of which cocompact
  lattice, in the sense that commensurable `Γ` give the same question up to finite index.

## 4. The open question, stated exactly

For a torsion-free uniform lattice `Γ ≤ Sp(n,1)`, `n ≥ 2`, and `Y` as above: is `W ⋉_r Y ≃ 0` in `KK^Ĝ`?
- A sufficient condition is `Y ≅ 0` in `KK^W`.
- A necessary condition is `W ⋉_r Y ≃_KK 0`.

Part 2 records the attempts on this.
