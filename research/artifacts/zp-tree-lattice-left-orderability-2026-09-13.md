# Left-orderability of lattices in products of trees: transcribing Deroin–Hurtado (part 1)

Lane z1-22-lo-simple-bm, 2026-09-13. Serves `irreducible-tree-product-lattices-are-not-left-orderable`
(open) and, through it, Zaremsky Problem 1.22 (`zaremsky-1-22-left-orderable-simple-group-of-type-f`).
Unreviewed working notes.

Source read: D. Witte Morris, *Non-left-orderability of lattices in higher-rank semisimple Lie groups
(after Deroin and Hurtado)*, arXiv:2407.09742v1 (13 Jul 2024), pages 1–28, read from the PDF. Page
numbers below are that version's. Statements quoted from it are marked [WM].

## 1. Target

Let `T_1`, `T_2` be locally finite trees and `G_i ≤ Aut(T_i)` closed, non-compact and 2-transitive on
`∂T_i`. Let `G = G_1 × G_2` and let `Γ ≤ G` be a cocompact lattice with dense projections. Target:
`Γ` has no faithful action on `R` by orientation-preserving homeomorphisms.

For Problem 1.22 the relevant `Γ` are torsion-free and simple, for example the simple finite-index
subgroups of the Burger–Mozes lattices in `U(A_(2n)) × U(A_(2m))`. Below `Γ` is torsion-free with
trivial abelianization.

## 2. Dictionary

| Witte Morris, p-adic | products of two trees |
|---|---|
| `K` compact open | `K = K_1 × K_2`, the stabilizer of a base vertex `o = (o_1, o_2)` |
| `K\G/Γ` finite (Note 3.5) | same argument: `G/Γ` compact and `K` open |
| `A`, maximal split torus | `A = ⟨α_1, α_2⟩ ≅ Z^2` with `α_1 = (a_1, 1)`, `α_2 = (1, a_2)`, where `a_i ∈ G_i` is hyperbolic with axis through `o_i`, attracting end `ξ_i^+` and repelling end `ξ_i^-` |
| minimal parabolics containing `A` | the four products `P_(ε_1 ε_2) = G_(1, ξ_1^(ε_1)) × G_(2, ξ_2^(ε_2))` of end stabilizers |
| Weyl chambers | the four closed quadrants of `A ⊗ R = R^2`; `W_P = {α_1^m α_2^l : m, l ≥ 0}` for `P = P_(++)` |
| `U_a^+ = {u : a^n u a^(-n) → 1 as n → −∞}` | for `a = α_1^m α_2^l` with `m, l ≥ 0`: `con(a_1^(-m)) × con(a_2^(-l))`, whose elements fix pointwise larger and larger balls toward `ξ_i^+`, so `U_a^+ ⊆ P_(++)` |
| centralizer of a wall element | `C_G(α_1) = C_(G_1)(a_1) × G_2 ⊇ 1 × G_2` |

Basic facts used below.

- **(F1)** `K_i` is transitive on `∂T_i`. A boundary-2-transitive closed `G_i` is locally
  `∞`-transitive (`burger-mozes-infinitely-transitive-tree-groups`, item 1), so `K_i` is transitive on
  every sphere around `o_i`, hence on ends. So `G_i = K_i G_(i,ξ)` and `G = KP` for each `P` above.
- **(F2)** `G_(i,ξ^+)` and `G_(i,ξ^-)` generate `G_i`. The generated subgroup `L` contains
  `G_(i,ξ^+)`. It is transitive on `∂T_i`, because `G_(i,ξ^-)` is transitive on `∂T_i ∖ {ξ^-}` and
  `G_(i,ξ^+)` moves `ξ^-` off itself. For `g ∈ G_i` choose `l ∈ L` with `l ξ^+ = g ξ^+`. Then
  `l^(-1) g ∈ G_(i,ξ^+) ⊆ L`. So the four parabolics generate `G`.
- **(F3)** For the interior element `a = α_1 α_2`,
  `{p ∈ G : {a^n p a^(-n) : n ≤ 0} bounded} = P_(++)`. Conjugating by `a^(-m)` for `m ≥ 0` stays
  bounded exactly when `p` fixes both attracting ends (bounded Busemann displacement there).

## 3. Step-by-step transfer

Status: **general** means the step uses only `K` compact open, `Γ` discrete and cocompact, and the
action on `R`. **tree** means an argument for trees is needed and given or sketched. **gap** means
still open.

1. **Theorem 3.15 / 4.1, the almost-periodic space `Z`** (p. 9, pp. 17–18). The construction uses
   Deroin–Kleptsyn–Navas–Parwani [14, Props. 8.1, 8.4] and is **general**. Step (2), freeness of the
   `R`-action, uses Theorem 2.4(3) (every action of `Γ` on `S^1` has a finite orbit) and finite
   abelianization. Trivial abelianization holds for simple `Γ`. Circle rigidity is **gap G7**.
2. **Definition 3.17, Lemma 3.21, Definition 3.24, Lemma 3.25** (pp. 9–10). **General**: they use `K`
   open, `Γ ∩ K = 1`, and Lipschitz control from a finite generating set.
3. **Stationarity of `μ_Z` and `μ_X`** (Proposition 4.7, Corollary 4.8, Example 5.7). **General**. When
   `G ≠ KΓ`, Witte Morris §5 extends `μ_Γ`-harmonic functions to `μ_G`-harmonic ones using a random
   walk on the finite set `K\G/Γ` (Proposition 5.6, pp. 27–28). Only `K` open and `Γ` cocompact are
   used. So Assumption 3.6 (`G = KΓ`) is not specific to algebraic groups and costs nothing extra here.
4. **Theorem 3.28, Furstenberg's decomposition** `μ_X = ∫_K k_* μ_X^P dm_K` with a unique
   `P`-invariant `μ_X^P` (p. 10). This needs the Poisson boundary of the bi-`K`-invariant, spread-out,
   compactly supported `μ_G` to be `G/P = ∂T_1 × ∂T_2` with its `K`-invariant measure. `P` is amenable
   (end stabilizers are amenable) and `G = KP` (F1). **Gap G4**: identify the Poisson boundary for
   non-algebraic `G_i`, possibly with `μ_G = μ_1 ⊗ μ_2` and isotropic walks on each tree.
5. **Proposition 3.29** (p. 11). (1) uses finite abelianization: **general** for simple `Γ`. (2) is
   Lemma 4.10 (p. 19), **general** (`K` open). (3) and (4) use `G = ⟨K, P⟩`, which is (F1).
6. **Definition 3.30, Lemmas 3.31, 4.11, 4.12** (pp. 11, 20): `χ_P : A → R` is a homomorphism because
   `A ⊆ P`. **General**. Lemma 4.13 (ergodicity of `μ_X^P`) rests on the uniqueness in Theorem 3.28
   (gap G4) and Proposition 4.20.
7. **Lemma 3.32 / 4.14, local contraction** (pp. 12, 21). **General** ergodic theory.
8. **Key Proposition 3.33, global contraction** (p. 12; §3G, §4E).
   - Proposition 3.44 / 4.19 (p. 23) uses the trichotomy [14, Thm. 7.1]. The case of a nontrivial
     homomorphism `Γ → R` is excluded by trivial abelianization. The case of a commuting fixed-point-free
     homeomorphism reduces to a `Γ`-action on `S^1` and needs circle rigidity (**gap G7**).
   - Proposition 3.45 / 4.20 (Jensen plus martingale convergence) is **general**.
   - Theorem 3.46 (Karlsson–Margulis) holds for the proper CAT(0) space `T_1 × T_2` and compactly
     supported `μ_G`.
   - Corollary 3.48 needs one element `â_P ∈ W_P ∖ {1}` of the **discrete** group `A` along which the
     random walk travels sublinearly. **Gap G5**: tune `μ_G` so that the drift vector of the walk on
     `T_1 × T_2` is `(p t_1, q t_2)` for positive integers `p`, `q`, where `t_i` is the translation
     length of `a_i`. Drifts of isotropic walks vary continuously with the weights of a bi-`K_i`-invariant
     measure.
   - Proposition 3.49 (deterministic direction) is standard for product walks. Proposition 3.50 and
     Remark 4.21 use only `U_a^+ ⊆ P` and commutation inside `A`.
9. **Corollary 3.35, invariance under `C_G(a)`** (pp. 12–13; Remark 4.16, p. 22). Inputs:
   - the Mautner lemma for `a` and `U_a^+` (general);
   - the analog of Proposition 2.8(2) (p. 6): `G/Γ` has no proper closed nonempty set invariant under
     `⟨a, U_a^+⟩`. That proof uses Moore ergodicity of `a` on `G/Γ` and an open big cell.
     - For a wall element `a = α_1^m`, ergodicity of `a` follows from ergodicity of `G_1` on `G/Γ`
       (dense projection to `G_2`) plus the Howe–Moore property of `G_1`.
     - For interior elements use `product-of-tree-groups-has-factorwise-howe-moore` (unreviewed).
     - **Gap G3**: confirm Howe–Moore for the `G_i` at hand.
   - an open big cell: `P_a^- U_a^+` contains a neighbourhood of `1`. For `G_i` with Tits' independence
     property and 2-transitive local actions, such as `U(F)` and `U(F)^+` with `F` 2-transitive:
     - Let `g` fix a large ball `B` around `o_i`. The ends `gξ^+` and `ξ^+` leave `B` through the same
       vertex `x`.
     - The fixator of the half-tree behind the edge just past `x` acts transitively on the ends of the
       other half-tree. This uses independence plus 2-transitivity of the local action.
     - So some `u` in that fixator has `u g ξ^+ = ξ^+`. This `u` lies in the contraction group toward
       `ξ^+` and fixes `B`, and `ug` fixes `ξ^+` and `B`.
     - **tree**, written out for independence groups only.
10. **Corollary 3.42 / 4.17, propagating invariance** (pp. 13–14, 22–23). Case 1 (`A_good` invariant
    under the Weyl group) gives invariance under all four parabolics, hence under `G` by (F2): **tree**,
    done. Case 2 is §4 below: **tree**, done given step 9.
11. **Proposition 4.23, `χ_P(â_P) < 0`** (p. 25). Uses Corollaries 3.48 and 4.8: same status as step 8.

## 4. Case 2 of Corollary 4.17 for products of trees

Assume the conclusions of steps 1–9. Following [WM, Cor. 4.17] (p. 22), let `Q_good` be the set of
minimal parabolics `Q ⊇ A` with `μ_X^Q = μ_X^P`, let `A_good` be the union of their chambers, and let
`H = {a ∈ A : χ_P(a) < 0}`. WM shows `H ⊆ A_good` and, for every Weyl element `w`, either
`w(A_good) = A_good` or `w(A_good)` misses the interior of `A_good`. Here the Weyl group is `(Z/2)^2`
acting on `R^2` by sign changes.

- **Reduction to a coordinate half-plane.** Write `χ_P(α_1^m α_2^l) = c_1 m + c_2 l`. If `c_1 c_2 ≠ 0`,
  the open half-plane `H` meets the interiors of three quadrants. Each of them is good, because an
  interior point lies in only one chamber. Every Weyl element then maps `A_good` onto a set meeting
  its interior, so `A_good` is Weyl-invariant: Case 1. `χ_P ≠ 0` by Proposition 4.23. So in Case 2
  exactly one of `c_1`, `c_2` vanishes. Say `c_2 = 0` and `c_1 ≠ 0`.
- **One factor of invariance.** Put `ε = sign(−c_1)`, so `χ_P(α_1^ε) < 0`. Some good chamber `W_Q`
  contains `α_1^ε`. By Proposition 4.23 and `H ⊆ A_good`, we may take `Q` with `α_1^ε` on the
  boundary of `W_Q`, so `U^+_(α_1^ε) ⊆ Q`. `μ_X^Q = μ_X^P` and `χ_Q = χ_P`. Corollary 3.35 for `Q`
  gives that `μ_X^P` is invariant under `C_G(α_1^ε) ⊇ 1 × G_2`.
- **Spreading the invariance.** `1 × G_2` is normal in `G`, so every `k_* μ_X^P` is `G_2`-invariant,
  and so is `μ_X = ∫_K k_* μ_X^P dm_K`. `μ_X` is `K`-invariant, hence invariant under
  `K G_2 = K_1 × G_2`.
- **The abelian subgroup.** Let `Γ_0 = Γ ∩ (K_1 × G_2)`. By Lemma 3.25 every `γ ∈ Γ_0` has
  `D_γ^leaf = 1` `μ_X`-a.e., so `γ` commutes with the `R`-flow. So `[Γ_0, Γ_0]` acts trivially on `Z`.
  `Γ` acts faithfully on `Z` [WM, p. 23], so `Γ_0` is abelian.
- **Contradiction, more simply than WM's Zariski-density step.** `Γ_0` is the stabilizer in `Γ` of the
  vertex `o_1 ∈ T_1`.
  - `Γ` is torsion-free and discrete, so it acts freely on `T_1 × T_2`, and `Γ_0` acts freely on
    `{o_1} × T_2`.
  - `Γ_0` has finitely many orbits on the vertices `{o_1} × V(T_2)`: two of them in one `Γ`-orbit are
    related by an element fixing `o_1`, and `Γ` has finitely many vertex orbits.
  - So `Γ_0` is a finitely generated free group acting freely and cocompactly on `T_2`.
  - `T_2` is not a line, since `G_2` is 2-transitive on `∂T_2`, which has more than two points. So
    `Γ_0` is non-abelian. Contradiction.

(Equivalently, `Γ_0` projects densely into `K_1`, which is non-abelian.)

## 5. Where the transcription stands

Settled for trees: steps 2, 3, 5, 6 (modulo G4), 7, the big cell for independence groups, and the
propagation (Case 1 via F2, Case 2 via §4). Open inputs:

- **G4**: Furstenberg decomposition over `P = G_(1,ξ_1) × G_(2,ξ_2)`, i.e. the Poisson boundary of
  `μ_G`;
- **G5**: realizing the drift direction by an element of `A ≅ Z^2`;
- **G7**: every action of `Γ` on `S^1` has a finite orbit. For simple `Γ` this is that every circle
  action has a fixed point;
- **G3**: Howe–Moore and Moore ergodicity for the non-algebraic factors;
- the technical points WM declares ignored (ergodic components in Corollary 3.35 and Lemma 4.14,
  `μ_X` versus `μ_X^P` in Remark 4.21), which Deroin–Hurtado treat in the real case.

None of the settled steps needs linearity of `Γ`, so the transcription is not blocked for non-linear
Burger–Mozes lattices. Part 2 addresses G7 through bounded cohomology.
