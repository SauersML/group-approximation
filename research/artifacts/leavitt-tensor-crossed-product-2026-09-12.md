# Leavitt tensor powers are unital twisted crossed products by Z^(d-1)

Lane `bh-coherence-kumjian-pask`, 2026-09-12. Written for
`leavitt-tensor-powers-have-trivial-k-theory` and its prime-field twin, after
`leavitt-tensor-powers-are-not-left-coherent` killed the coherence route.

**Summary.**
- **Structural result (derivation, §1–§3).** Let `k` be a field and
  `L = L_k(1,2)`. For every `d >= 2`, `L^(⊗d)` is a unital Passman crossed
  product `C ∗ Z^(d−1)`.
  - The coefficient ring is `C = L_0^(⊗(d−1)) ⊗ L`.
  - The twisting is by an action together with a cocycle valued in `C^×`.
  - `C` is left and right semihereditary and regular supercoherent, with
    `K_n(C) = 0` for every `n ∈ Z`.
- **Consequence (§4, conditional).** The K-theoretic Farrell–Jones conjecture
  for `Z^(d−1)`, with coefficients in a uniformly regular additive category,
  would give `K_n(L^(⊗d)) = 0` for all `n`. That step is owned by lane
  `bh-leavitt-nil-k-regularity`, which verifies the imports. Nothing below
  establishes it.

The decomposition is the Steinberg-algebra form of a groupoid fact. Let
`c_1, ..., c_d` be the degree cocycles on `G^d`, where `G` is the Cuntz
groupoid. Then `G^d` is a twisted semidirect product of the subgroupoid
`{c_1 = ... = c_(d−1) = 0}` by `Z^(d−1)`, with one bisection of each degree
`e_j − e_(j+1)`.

## 1. Units of degree e_j − e_(j+1)

`L` has generators `x_1, x_2` of degree `1` and `y_1, y_2` of degree `−1`, with
`y_i x_j = δ_ij` and `x_1 y_1 + x_2 y_2 = 1`. `L` is strongly `Z`-graded, and
`A = L^(⊗d)` is strongly `Z^d`-graded with `A_v = L_(v_1) ⊗ ... ⊗ L_(v_d)`.

For `1 <= j <= d−1`, with the displayed factors in positions `j` and `j+1`, put

```text
u_j  = Σ_i 1^(⊗(j−1)) ⊗ x_i ⊗ y_i ⊗ 1^(⊗(d−j−1)),
u_j' = Σ_i 1^(⊗(j−1)) ⊗ y_i ⊗ x_i ⊗ 1^(⊗(d−j−1)).
```

On the two displayed factors:
- `u_j u_j' = Σ_(i,l) x_i y_l ⊗ y_i x_l = Σ_i x_i y_i ⊗ 1 = 1`;
- `u_j' u_j = Σ_(i,l) y_i x_l ⊗ x_i y_l = Σ_i 1 ⊗ x_i y_i = 1`.

So `u_j` is a unit of degree `e_j − e_(j+1)`. For `d = 2` it is the unit `u` of
`leavitt-tensor-powers-are-not-left-coherent`.

## 2. The crossed product decomposition

Let `Λ = {v ∈ Z^d : v_1 + ... + v_d = 0} ≅ Z^(d−1)`, with basis `e_j − e_(j+1)`.
For `λ = Σ_j m_j (e_j − e_(j+1))`, put `u^λ = u_1^(m_1) ⋯ u_(d−1)^(m_(d−1))`, a
unit of degree `λ`. Let

```text
C = ⊕_(c ∈ Z) A_(c e_d) = L_0^(⊗(d−1)) ⊗ L.
```

**Lemma 2.1.** `A = ⊕_(λ ∈ Λ) u^λ C`, and `u^λ C (u^λ)^(−1) = C` for every `λ`.
So `A` is a crossed product `C ∗ Λ`: a `Λ`-graded ring with a unit in every
component and degree-zero component `C`. With `α_λ = Ad(u^λ)|_C` and
`ω(λ, μ) = u^λ u^μ (u^(λ+μ))^(−1)`,

```text
(u^λ c)(u^μ c') = ω(λ, μ) u^(λ+μ) α_μ^(−1)(c) c',    ω(λ, μ) ∈ C^×.
```

*Proof.*
1. **Decomposition.** Every `v ∈ Z^d` is uniquely `λ + c e_d`, with
   `c = v_1 + ... + v_d` and `λ = v − c e_d ∈ Λ`. Since `u^λ` is a unit of
   degree `λ`, `(u^λ)^(−1) A_v ⊆ A_(c e_d)`, so `A_v = u^λ A_(c e_d)`. Summing
   over `v` gives `A = ⊕_λ u^λ C`. The sum is direct because the summands lie in
   distinct `Z^d`-degrees.
2. **Invariance.** Conjugation by a homogeneous unit preserves every degree, so
   it maps `A_(c e_d)` onto itself.
3. **Cocycle.** `ω(λ, μ)` is a unit of degree `0`, and `A_0 = L_0^(⊗d) ⊆ C`. The
   multiplication formula is the rule `u^λ u^μ = ω(λ, μ) u^(λ+μ)` together with
   `c u^μ = u^μ α_μ^(−1)(c)`. ∎

**The cocycle is not a coboundary of the obvious kind.** On the three
displayed factors for `d = 3`:
- `u_1 u_2 = Σ_(i,l) x_i ⊗ y_i x_l ⊗ y_l = Σ_i x_i ⊗ 1 ⊗ y_i`;
- `u_2 u_1 = Σ_(i,l) x_i ⊗ x_l y_i ⊗ y_l`.

These differ, so `u_1` and `u_2` do not commute.

**Examples of sub-crossed products.**
- `H = Z(e_(d−1) − e_d)` gives `C ∗ H = L_0^(⊗(d−2)) ⊗ L ⊗ L`.
- `H = Z(e_1 − e_2)` gives `C ∗ H = B ⊗ L_0^(⊗(d−2)) ⊗ L`, where `B` is the
  algebraic Bernoulli crossed product of `leavitt-tensor-powers-are-not-left-coherent`.

In particular the intermediate crossed products are not coherent.

## 3. The coefficient ring

**Lemma 3.1.** Let `C = L_0^(⊗(d−1)) ⊗ L` with `d >= 1`. Then:
1. `C` is left and right semihereditary;
2. `C[t_1, ..., t_p]` is regular coherent for every `p >= 0`, so `C` is regular
   supercoherent;
3. `K_n(C) = 0` for every `n ∈ Z`.

*Proof.*
- **As a colimit.** `L_0` is the directed union of the subalgebras
  `span{x_μ y_ν : |μ| = |ν| = m} ≅ M_(2^m)(k)`. The inclusions append a letter:
  `x_μ y_ν = Σ_j x_(μj) y_(νj)`, which is the diagonal map `a ↦ a ⊗ 1_2`. Hence
  `C = colim_m C_m`, with `C_m = M_(N_m)(L)` and `N_m = 2^(m(d−1))`. The
  connecting maps are diagonal, so each `C_(m+1)` is free as a left and as a
  right `C_m`-module.
- **Part 1.** `L` has global dimension at most `1` (the `d = 1` case of
  `leavitt-tensor-global-dimension-bound`), so it is hereditary, and so is every
  `C_m`. A finitely generated left ideal `I` of `C` is generated inside some
  `C_m`, by a left ideal `I_m` that is projective. Since `C` is flat over `C_m`,
  `I = C ⊗_(C_m) I_m` is projective. The right side follows through the
  involution.
- **Part 2.** `L` is regular supercoherent (Ara–Cortiñas arXiv:1108.0352v3
  Lemma 6.1, node `ara-cortinas-leavitt-tensor-k-theory-vanishes`), and so is
  every matrix ring over it. Now `C[t_1, ..., t_p]` is the colimit of
  `M_(N_m)(L[t_1, ..., t_p])` along free extensions.
  - Every finitely generated left ideal, and every finitely presented module, is
    extended from some stage.
  - At that stage it is finitely presented, with a finite resolution by finitely
    generated projectives.
  - Flat base change preserves both properties.

  This is the flat filtered colimit argument quoted in ABC Section 7, as in
  attempt 8 of `leavitt-tensor-powers-are-left-coherent`.
- **Part 3.** Nonconnective K-theory commutes with filtered colimits of rings
  and is Morita invariant, so `K_n(C) = colim_m K_n(C_m) = colim K_n(L)`. Now
  `K_n(L) = 0` for every `n ∈ Z`, by Ara–Cortiñas Proposition 6.2 with `R = k`,
  imported in `ara-cortinas-leavitt-tensor-k-theory-vanishes`. ∎

Part 1 gives a uniform bound: every finitely presented `C`-module has projective
dimension at most `1`. This is the kind of uniform regularity that Nil-vanishing
theorems for additive categories ask of their coefficients.

## 4. What the decomposition does for the K-theory claim

`KH(L^(⊗d)) = 0` is already known (ABC Theorem 8.6, attempt 1 of
`leavitt-tensor-powers-have-trivial-k-theory`). The open part is `K`. By
Lemma 2.1, `K_*(L^(⊗d)) = K_*(C ∗ Z^(d−1))`.

**The conditional step.** Suppose two statements hold for the additive category
of finitely generated free `C`-modules, with the `Z^(d−1)`-action coming from
`(α, ω)`:
1. the K-theoretic Farrell–Jones conjecture with coefficients in additive
   categories holds for `G = Z^(d−1)`;
2. the relative assembly from the trivial family to `VCyc` is an equivalence,
   because the twisted Nil terms vanish for uniformly regular coefficients.

Then `K(C ∗ G) ≃ EG_+ ∧_G K(C)`, which is contractible by Lemma 3.1(3). So
`K_n(L^(⊗d)) = 0` for every `n`, over every field. That settles
`leavitt-tensor-powers-have-trivial-k-theory` at `k = F_2` and its prime-field
twin.

**A second form of the step.** Replace 2 by the values on cyclic subgroups. For
each infinite cyclic `H ≤ Λ`, `C ∗ H = C[t, t^(−1); α]` with `t = u^h`, a skew
Laurent ring by an automorphism and with no cocycle.
- If the twisted Laurent fundamental theorem holds over the regular
  supercoherent ring `C` in all degrees, with twisted Nils vanishing, then
  `K_*(C ∗ H) = 0`.
- Then `H^G(E_(VCyc) G; K_C)` has zero coefficients on every orbit type that
  occurs, and vanishes.
- Negative degrees matter here. The equivariant Atiyah–Hirzebruch spectral
  sequence has `p >= 0`, so `K_1` and `K_2` of the target need
  `K_q(C ∗ H) = 0` for every `q <= 2`, including `q < 0`.

**Status.**
- **Checked here:** Lemma 2.1 and Lemma 3.1, from main's imports.
- **Owned elsewhere:** the Farrell–Jones inputs (Bartels–Reich coefficients,
  Wegner for CAT(0) groups, Bartels–Lück Nil vanishing for additive categories)
  and the twisted Laurent theorem. They are verified by lane
  `bh-leavitt-nil-k-regularity`, not here.
- **Why coherence of the intermediates does not matter.** The conjecture
  computes `K(C ∗ G)` from `K(C)` or from the values `K(C ∗ H)`, and each of
  those is computed from the coherent base `C`. The non-coherence shown in
  `leavitt-tensor-powers-are-not-left-coherent` lives in the module categories
  of the intermediate crossed products, which the assembly isomorphism never
  touches.
