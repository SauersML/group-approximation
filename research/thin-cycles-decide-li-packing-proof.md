---
rg: 2
id: thin-cycles-decide-li-packing-proof
kind: route
title: Dickson's lemma plus monotonicity of the rare-type count along expansions turns any bounded-packing family into a hitting set with a thin growth cycle; (2_Γ) re-imports one-layer expansions into every power family
target: thin-cycles-decide-li-packing
requires:
  - perron-weights-do-not-give-li-finiteness
---

**Lane proof, not independently reviewed.** Notation is that of
`perron-weights-do-not-give-li-finiteness`. Units are trivial, so the unit-classes of
objects of `𝐗(*)` are exactly the type multisets `𝐦_x ∈ ℕ^{𝔛(*)}`: permutations of
indices are units, and nothing else is.

## 1. "If"

This direction is §5 of `perron-weights-do-not-give-li-finiteness-proof`.

## 2. "Only if"

Suppose (Pack) fails: infinitely many classes `x_i` satisfy `ρ(x_i) ≤ B`.

**Step 1 (a hitting set).**
- The multisets `𝐦_{x_i}` are distinct. By Dickson's lemma, pass to a subsequence that is
  non-decreasing coordinatewise.
- Let `T_∞` be the set of types whose multiplicity tends to infinity along the
  subsequence, and `R = 𝔛(*) ∖ T_∞`. Then `𝐦_{x_i}(R) ≤ B'` for all `i`.
- If some `γ ∈ Γ` had its codomain type set inside `T_∞`, then using `γ` alone gives
  `ρ'(x_i) ≥ min_{τ ∈ 𝔛(𝐝γ)} 𝐦_{x_i}(τ) → ∞`, a contradiction. So `R` is a hitting set.

**Step 2 (monotonicity).**
- A morphism `* → x_i` in `Π` is a sequence of steps. Each step replaces one piece of type
  `τ` by the codomain of a generator `γ` with `𝐭(γ) = X(τ)`.
- The change in `𝐦(R)` is `#(R-pieces of 𝐝γ) − [τ ∈ R] ≥ 1 − 1 = 0`, by the hitting
  property.
- It is `0` exactly for **thin steps**: `τ ∈ R` and exactly one `R`-piece. Every other step
  raises `𝐦(R)` by at least `1`.
- So each path `* → x_i` has at most `B'` non-thin steps, and at every moment there are at
  most `B'` pieces of `R`-type.

**Step 3 (a long thin lineage).**
- A thin step replaces an `R`-piece by exactly one `R`-piece, its successor. So the
  `R`-pieces form boundedly many lineages: at most `B'` pieces exist at once, and at most
  `B'` new ones are born in non-thin steps, besides the pieces of `*`.
- `|x_i| → ∞`, while the non-thin steps add at most `B'·C` pieces in total (`C` is the
  largest codomain size). So the number of thin steps with a **further piece** (growth
  steps) tends to infinity.
- Some lineage therefore contains unboundedly many growth steps.

**Step 4 (a cycle).**
- The types along that lineage form a walk in the finite directed graph whose edges are
  the thin generators (domain `τ ∈ R` to its unique `R`-child).
- A walk decomposes into simple cycles plus a simple path, and the simple path has fewer
  than `|𝔛(*)|` edges.
- Once the walk has more than `|𝔛(*)|` growth edges, one of its simple cycles contains a
  growth edge. Its types occur in `𝐗(*)`. ∎

**Decidability.**
- `𝔛(*)` is computable as the closure of the types of `*` under the codomains of `Γ`
  (a finite closure computation).
- There are finitely many subsets `R` to check, and cycle detection in a finite graph is
  decidable.

## 3. Powers of the tree coding

Take `𝔖_N` = paths of length `≤ N`, so `‖c‖ = ⌈|c|/N⌉`.
- For `c` with `|c| = LN − j` (`1 ≤ j < N`), the fitting set is `𝔰 = {s : |s| ≤ j}`.
- In `γ(∅, 𝔰)`, the pieces for `|s| < j` are `X(r(s); all out-edges) = ∅`, and the
  leftover is `X(v; 𝔰) = ∅`. So `γ(∅, 𝔰)` is the `j`-step expansion. For `j = 1` it is the
  one-step expansion.
- Every reachable letter occurs at the end of words of every length, so all these
  generators lie in `Γ(*)`.
- Every `j`-step expansion contains `a` or `a^{-1}`, because each single step does. So
  `R = {a, a^{-1}}` is hitting for all of `Γ`, and "one-step expand `a`" is a thin growth
  cycle. By §1, (Pack) fails for every `N`.

## 4. The raw product 2-graph

The vertices are the pairs `(ℓ,m)`, with colour-1 edges `(ℓ,m) → (ℓ',m)` (`ℓ' ≠ ℓ^{-1}`)
and colour-2 edges similarly. The Garside family is Li's `S_P = {0,1}²`, so
`‖c‖ = max(d_1, d_2)`.
- For `c` of degree `(d_1, d_2)` with `d_1 > d_2`, `𝔰` is the set of colour-2 edges at the
  endpoint. On `∂Ω`, `γ(∅, 𝔰)` is the colour-2 expansion `(ℓ,m) → (ℓ, m')`
  (`m' ≠ m^{-1}`): the leftover is empty on `∂Ω`, and so are the edge pieces of full
  expansions, so full expansions are the square expansions.
- `R = {ℓ ∈ {a^{±1}}} ∪ {m ∈ {c^{±1}}}` is hitting. Every square, colour-1 or colour-2
  expansion leaves three choices of the moving letter(s), so it can reach `a^{±1}` in
  colour 1 or `c^{±1}` in colour 2.
- The colour-2 expansion of `(b,c)` has `R`-children `{(b,c)}` only, together with
  `(b,d)` and `(b,d^{-1})`. That is a thin growth cycle.

This is exactly the configuration that Li's hypothesis `#𝔳𝔡^{-1}(ε_j)𝔳 ≥ 2` in
`thm:k-graphs` excludes, since two colour-2 loops at `(b,c)` would give two `R`-children.

## Lesson for general BH

The whole obstruction to finiteness of a coded full group lives in the one-layer move
graph of the category, and Li's (`2_Γ`) guarantees that every Garside family sees it. A
thin cycle is a rare type that one move regenerates alone. Loops in every colour at every
state (Li, via Matui's recoding) remove all thin cycles at once, and that is the design
target for any new category presenting a boundary groupoid.
