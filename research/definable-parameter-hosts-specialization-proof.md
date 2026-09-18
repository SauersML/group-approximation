---
rg: 2
id: definable-parameter-hosts-specialization-proof
kind: route
title: The relator locus of a finitely presented definable action is a parameter-free definable set, so it has tame points avoiding any finite set of nontrivial elements, and nonidentity in a tame member is an existential condition decidable in PSPACE
target: definable-parameter-hosts-cap-simple-subgroups-at-pspace
artifacts:
  - research/artifacts/gq-bh-bh-free-32-order-rigidity.md
---

Lane proof, not independently reviewed. Notation as in the target. For a word
`w = s_1 ⋯ s_L` in `g_i^{±1}`, write `w_θ` for the composite of the maps defined by the formulas at
parameter `θ`. For type (A), read `ξ` for `θ`.

## Step 1: the relator locus is definable without parameters

"`w_θ(x) = y`" is the formula `∃x_1 … x_{L-1}` asserting the chain
`(x, x_1) ∈ Γ_{s_L}(θ)`, `(x_1, x_2) ∈ Γ_{s_{L-1}}(θ)`, …, `(x_{L-1}, y) ∈ Γ_{s_1}(θ)`. For an
inverse letter, swap the two coordinates of the graph. Let `G = ⟨g_1..g_m | r_1..r_q⟩`, and let
`Θ` be the set of parameters `θ` such that:

- each `γ_i(θ, ·, ·)` is the graph of a bijection of `X_θ = χ(θ, ·)` (a first-order condition), and
- `∀x ∈ X_θ: r_{j,θ}(x) = x` for every `j`.

Then `Θ` is defined by a formula without parameters:
- For (R), a first-order formula over the ordered field `R` with rational coefficients.
- For (A), a first-order formula over synchronous ω-regular relations, hence an ω-regular set.
  Such relations are closed under Boolean operations and projection by Büchi's theorem; see
  Khoussainov--Nerode 1995 or Blumensath--Grädel 2000 on automatic structures.

`θ_0 ∈ Θ`. For every `θ ∈ Θ`, von Dyck gives a homomorphism `φ_θ: G → Bij(X_θ)` with
`φ_θ(w) = w_θ`.

## Step 2: tame points (item 1)

Let `F ⊆ G ∖ {1}` be finite, with each `f ∈ F` fixed as a word. Put
`Θ_F = Θ ∩ ⋂_{f ∈ F} {θ : ∃x ∈ X_θ, f_θ(x) ≠ x}`. It is defined without parameters, and it is
nonempty because the action at `θ_0` is faithful.

- **(R).** The real algebraic numbers form a real closed field and an elementary substructure of
  `R` (Tarski). The sentence `∃θ, θ ∈ Θ_F` has rational coefficients and holds in `R`, so it holds
  in `R_alg`. That gives `θ ∈ Θ_F ∩ R_alg^k`.
- **(A).** A nonempty ω-regular set is accepted by a nonempty Büchi automaton, which accepts a
  lasso word `u v^ω` (Büchi). So `Θ_F` contains an ultimately periodic `ξ`.

At that tame `θ`, `φ_θ(f) = f_θ ≠ id` for all `f ∈ F`. ∎

## Step 3: simple subgroups (item 2, first half)

Let `S ≤ G` be finitely generated and simple, and pick `s ∈ S ∖ {1}`. Apply Step 2 with `F = {s}`.
Then `ker φ_θ ∩ S` is a normal subgroup of `S` not containing `s`, so it is trivial. Hence `S` is
isomorphic to `φ_θ(S)`, a finitely generated group in the tame member at `θ`. ∎

## Step 4: tame members have word problem in PSPACE (item 2, second half)

Fix a tame `θ` and a finitely generated `Γ ≤ Bij(X_θ)` whose generators are words in the `g_i`.
A word `w` of length `L` in these generators is a word of length `O(L)` in the `g_i`. It is
nontrivial iff `∃x, x_1, …, x_{L'}: x ∈ X_θ, chain(x, x_1, …, x_{L'}), x_{L'} ≠ x`.

- **(R).** This is an existential sentence over `R` with `O(nL)` variables. It is a conjunction of
  `O(L)` copies of fixed Boolean combinations of polynomial (in)equalities of bounded degree. The
  finitely many algebraic constants of `θ` are fixed variables, each pinned by its minimal
  polynomial and a rational isolating interval. The existential theory of the reals is decidable in
  PSPACE (Canny 1988, *Some algebraic and geometric computations in PSPACE*). So `WP(Γ) ∈ PSPACE`.
- **(A).** Fold the lasso `ξ = u v^ω` into the automata, so that each graph becomes a
  parameter-free synchronous Büchi automaton on two tracks. Nontriviality is nonemptiness of a
  Büchi automaton on `L'+2` tracks: the product of `L'+1` fixed automata and a fixed automaton
  for `x_{L'} ≠ x`. A state of the product is a tuple of `O(L)` fixed-size components.
  The acceptance condition is generalized Büchi, one condition per factor; a round-robin counter of
  `O(log L)` bits handles it. A lasso
  can be guessed on the fly: guess the stem and the loop letter by letter, store one state tuple,
  and check for an accepting visit. So nonemptiness is in NSPACE`(O(L))` ⊆ PSPACE (Savitch).
  Hence `WP(Γ) ∈ PSPACE`. ∎

## Step 5: items 3 and 4

- **Item 3.** The trivial words of `G` are recursively enumerable, since `G` is finitely
  presented. The nontrivial words are recursively enumerable too: enumerate tame parameters `θ`
  (algebraic tuples by minimal polynomials and isolating boxes, or lassos). For each, decide
  `θ ∈ Θ` and `w_θ ≠ id` by Tarski's decision procedure, resp. Büchi's. If `w ≠ 1` in `G`, then
  Step 2 with `F = {w}` produces such a `θ`. If `w = 1` in `G`, then `w_θ = id` for all `θ ∈ Θ`.
- **Item 4.** If `Q ≤ S` with `S` as in item 2, then writing the generators of `Q` as words in
  those of `S` reduces `WP(Q)` to `WP(S)` in linear time. A finitely presented simple `G` is its own
  `S`.

## Remarks

- **Isolation.** If `θ_0` is isolated in `Θ`, modulo a definable symmetry such as rescaling, then
  `θ_0` itself is tame. For (R) this is Tarski: an isolated point of a set defined without
  parameters is definable without parameters. For (A) it is Büchi: an isolated point is a
  singleton ω-regular set, hence a lasso. This is the mechanism of
  `fp-bieri-strebel-line-groups-are-deformation-rigid`.
- **Genericity.** Conversely, at a Zariski-generic `θ_0` the set `Θ` contains a neighborhood of
  `θ_0` in the parameter variety. This is the mechanism of
  `fp-piecewise-projective-groups-rigidity-criterion`. The analogue for (A) is a normal
  (finite-state random) address. That analogue is not needed here and is not written out.
