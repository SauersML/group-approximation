---
rg: 2
id: adder-hosts-linearize-odd-odometer-roots-proof
kind: route
title: Conjugating the adder by id x g gives the fibered translation by g, so the group is the orbit span semidirect Gamma; sections stay in the span because tree automorphisms are 1-Lipschitz; the natural copy is the criterion node's construction on digit pairs
target: adder-hosts-linearize-odd-odometer-roots
requires:
  - natural-q-rtimes-2-in-2v-h-iff-odd-odometer-roots
  - fg-metabelian-groups-have-roots-at-finitely-many-primes
---

Lane proof (bh-free-16, 2026-09-18). Notation as in the claim. `M = M(Γ)`.

## Step 1. Structure

- **Products.** `(x, y) ↦ (x + ψ(y), g(y))` composed after `(x + ψ'(y), g'(y))` is
  `(x + ψ'(y) + ψ(g'(y)), g g'(y))`. So pairs `(ψ, g)` multiply as in `M ⋊ Γ`, with `Γ` acting on functions by
  precomposition. The set is closed under inverses since `M` is `Γ`-stable.
- **Generators.** `A = (ι, 1)` and `id × g = (0, g)`, so `G_Γ ⊆ M ⋊ Γ`.
- **Conjugates of the adder.** `(id × g)^-1 ∘ A ∘ (id × g)` sends `(x, y) ↦ (x, gy) ↦ (x + gy, gy) ↦ (x + g(y), y)`.
  This is `F_g = (g, 1)`.
- **Equality.** Sums of the `F_g` give all `(ψ, 1)` with `ψ ∈ M`, so `G_Γ = M ⋊ Γ`.
- **Translations.** `T_c × id = (c, 1)` lies in `G_Γ` iff `c ∈ M`.
- **Constants.** `1 = ι∘T_1 − ι ∈ M`, so `Z ⊆ M`.

## Step 2. Self-similarity on T_4

The letters are pairs `(x_0, y_0)`, and `x = x_0 + 2x'`, `y = y_0 + 2y'`.
- **`id × g`.** Its section is `id × g|_(y_0)`, which lies in `G_Γ` because `Γ` is self-similar.
- **`F_ψ`, reduction.** Write `ψ = Σ n_g g` (finite sum). Tree automorphisms are 1-Lipschitz, with
  `g(y_0 + 2y') = g(y_0)_0 + 2 g|_(y_0)(y')`, where `g(y_0)_0 ∈ {0,1}` is the first output digit. Hence
  `ψ(y_0 + 2y') = e + 2ψ'(y')`, with `e = Σ n_g g(y_0)_0 ∈ Z` and `ψ' = Σ n_g g|_(y_0) ∈ M`.
- **`F_ψ`, its section.** `F_ψ` sends the letter `(x_0, y_0)` to `(j, y_0)`, with `j ≡ x_0 + e (mod 2)`. Its section
  is `F_(ψ' + (x_0 + e − j)/2)`, and `ψ' + (x_0 + e − j)/2` lies in `M + Z = M`.

So every section of every element lies in `G_Γ`.

## Step 3. The natural copy

- **The action.** On `X = ({0,1}^2)^Z`, with colour 1 the positions `>= 0` and colour 2 the positions `< 0`, let
  `Q ⊆ Q_2` act by addition on the `x`-sequence with carries upward, and let `2` act by the shift `u` of both
  sequences. `u` is multiplication by 2 on each and commutes with the construction. This is a faithful action of
  `Q ⋊ ⟨2⟩`.
- **The odd part.** For `c ∈ Z_(2) ⊆ Z_2`, the translation has no negative-position digits. It acts on colour 1 as
  `T_c × id = F_c`, which lies in `G_Γ` by Step 1 when `c ∈ M`. As a global bisection it lies in `2V_(G_Γ)`.
- **The rest.** `u` lies in `2V` over the 4-ary colours, as the inverse-baker shift of pairs. So
  `u^-k F_c u^k` is the translation by `c/2^k`, and together these give `Q ⋊ ⟨2⟩`, exactly as in Step 4 of the
  criterion node's proof.
- **Pseudo-freeness.** Suppose `(ψ, g)` fixes a vertex with trivial section. Then `g` is the identity on a cylinder,
  and `ψ` vanishes on a cylinder. Pseudo-freeness of `Γ` forces `g = 1`, and the stated condition on `M` forces
  `ψ = 0`. The converse is similar.

## Step 4. Necessary conditions

- **`Γ` non-abelian.** If `Γ` is abelian and finitely generated, `G_Γ = M ⋊ Γ` is finitely generated metabelian. A
  copy of `Z_(2) = Z[1/P]`, with `P` the odd primes, contradicts `fg-metabelian-groups-have-roots-at-finitely-many-primes`
  item 2.
- **`Γ` not piecewise-affine over one `Z[1/N]`.** If every element of `Γ` is piecewise affine on cylinders, with
  coefficients in `Z[1/N]` (this class is closed under composition), then every element of `M` is too. A constant in
  `M` equals such a function on an open set, so it lies in `Z[1/N]`.

## Step 5. The bottleneck

A finitely presented `H` with `Z_(2)` in `H`, or in `M`, is finitely presented, is residually finite (it acts
faithfully on a rooted tree), and contains `Z_(2)`. This is exactly `z-localized-embeds-in-fp-rf-group` at `l = 2`,
and so (SL) with `S = {2}`. The one-dimensional alternative needs Möbius germs at `∞`. For the natural action on
`P^1(Q_2)`, the germ of `x ↦ x + q` at `∞` has sections `w ↦ w/(1 + cw)`, `c ∈ 2Z_(2)`. So the coefficient group
must also contain the lower unipotent `Z_(2)`, which is the rational Iwahori situation. ∎

## Remark (what was tried by hand)

- **XOR masks.** Take `ρ_e(y) = y ⊕ e` (digitwise XOR with a fixed mask `e`). Then `ρ_e(y) − y = e − 2(y ∧ e)`. A
  `Z`-combination `Σ n_e (ρ_e − ι)` is constant only if `Σ n_e e_k = 0` at every digit `k`, and then the constant is
  `Σ n_e e = 0`. So digitwise masks add no constants.
- **Masks with affine elements.** Combined with translations and multiplications by odd `p`, the constants found
  were only those of the affine pieces.
- **What is left.** A witness must use carry-producing elements that are not affine, for example non-affine
  automata with free subgroups. There `Z[Γ]` is non-Noetherian, and the metabelian and Krull-type obstructions
  do not apply.
