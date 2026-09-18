---
rg: 2
id: coarsely-injective-groups-with-torsion-rips-proof
kind: route
title: Run Zaremsky's small-ball criterion on the orbit set and collapse the stabilizer twins
target: coarsely-injective-groups-with-torsion-have-contractible-rips
requires:
  - zaremsky-rips-contractibility-criterion
  - flag-complex-proper-vertex-transitive-action-rips
---

Notation as in the target claim. Put `X = G x_0 ⊆ E`, a set of points of `E`, and
`ρ(x, y) = d(x, y)` for `x, y ∈ X`.

**Step 0: an integer metric on the orbit.** Put `ρ' = ⌈ρ⌉` on `X`. It is a metric: it
vanishes only on the diagonal because `ρ` does, and `⌈a + b⌉ ≤ ⌈a⌉ + ⌈b⌉`. For an integer
`t`, `ρ ≤ t` iff `ρ' ≤ t`. `G` acts on `(X, ρ')` by isometries, transitively.

The `ρ'`-ball of radius `t` about `x_0` is the set of orbit points `g x_0` in the closed
ball `B = B(x_0, t)` of `E`. Each such `g` satisfies `g x_0 ∈ gB ∩ B`, so by properness
there are finitely many such `g`, hence finitely many such points. By transitivity every
`ρ'`-ball of radius `t` has the same finite cardinality `n_t`. A set of `ρ'`-diameter `t`
lies in the `ρ'`-ball of radius `t` about any of its points, so property (*) of
`zaremsky-rips-contractibility-criterion` holds. The stabilizer `G_(x_0)` is finite by
properness (applied to `B(x_0, 1)`), and no triviality of it is used.

**Step 1: the criterion.** Let `t > t_0` be an integer, so `t ≥ 4δ + 4D + 3`. Put
`r_t = ⌈t/2 + δ + D⌉`. Then `r_t ≤ t/2 + δ + D + 1 < t`. Let `S ⊆ X` have
`ρ'`-diameter `t`; then `ρ(s, s') ≤ t` on `S`. Let
`Y_S = {y' ∈ X : ρ'(y', s) ≤ r_t for all s ∈ S}`, the centres (in `X`) of the radius-`r_t`
balls containing `S`. `Y_S` is finite by Step 0. Consider the finite family of balls
`B(s, t/2)` for `s ∈ S` and `B(y', r_t)` for `y' ∈ Y_S`. It satisfies the hypothesis of
coarse injectivity:

- `ρ(s, s') ≤ t = t/2 + t/2`;
- `ρ(s, y') ≤ r_t ≤ t/2 + r_t`;
- `ρ(y', y'') ≤ ρ(y', s) + ρ(s, y'') ≤ 2 r_t` for any `s ∈ S`.

So some `p ∈ E` has `d(p, s) ≤ t/2 + δ` for all `s ∈ S` and `d(p, y') ≤ r_t + δ` for all
`y' ∈ Y_S`. By coboundedness choose `y ∈ X` with `d(p, y) ≤ D`. Then:

- `ρ(y, s) ≤ t/2 + δ + D` for every `s ∈ S`, so `ρ'(y, s) ≤ r_t`. So `S` lies in the
  `ρ'`-ball of radius `r_t < t` centred at the point `y` of `X`, and `y ∈ Y_S`.
- For every `y' ∈ Y_S`, `ρ(y, y') ≤ D + r_t + δ ≤ t/2 + 2δ + 2D + 1 ≤ t`, since
  `t ≥ 4δ + 4D + 2`. So `ρ'(y, y') ≤ t`: the centre `y` lies within `t` of the centre of
  every other radius-`r_t` ball containing `S`.

These are the hypotheses of Zaremsky's Theorem 3.1 (as imported in
`zaremsky-rips-contractibility-criterion`: balls centred at points of `X`, for all
`t > t_0`). Hence `VR_(t_0)(X, ρ')` is contractible. The same verification works for every
base `t_1 ≥ t_0` (the hypotheses are required only for `t > t_1`), so `VR_t(X, ρ')` is
contractible for every integer `t ≥ t_0`.

**Step 2: twin collapse.** Fix an integer `t ≥ t_0` and let `K = VR_t(X, ρ')`.

- `K` is a flag simplicial complex: its simplices are the finite subsets of `X` whose
  points are pairwise within `t`.
- `K` is locally finite, by Step 0.
- `G` acts on `K` by simplicial automorphisms, transitively on vertices, with finite
  vertex stabilizers `G_(g x_0) = g G_(x_0) g^-1`.
- `K` is contractible by Step 1.

By `flag-complex-proper-vertex-transitive-action-rips` with `v = x_0`, the set
`S = {g ≠ 1 : g x_0 = x_0 or g x_0 is adjacent to x_0}` is a finite symmetric generating set
and `P_1(G, S) ≃ K` is contractible. Two distinct orbit points are adjacent in `K` iff
`ρ' ≤ t` iff `d ≤ t`, and `g x_0 = x_0` gives `d = 0 ≤ t`. So
`S = {g ≠ 1 : d(x_0, g x_0) ≤ t} = T_t`. ∎

**Hypothesis check.** Where torsion-freeness was used in
`coarsely-injective-groups-rips-proof` (Step 0 there: injectivity of `g ↦ g x_0`, so that
`ρ` is a metric on `G`), it is replaced here by working on `X` and by the twin-collapse
lemma. Everything else is the same computation, done on orbit points.

**Model test.** `G = D_∞` acting on `R` (injective, `δ = 0`) by the maps `x ↦ ±x + n`,
`n ∈ Z`, with `x_0 = 0`. Then `G_0 = Z/2` (the reflection `x ↦ -x`), `X = Z`, `D = 1/2`,
`t_0 = 4`. `VR_4(Z)` is contractible, `T_4 = {g ≠ 1 : |g(0)| ≤ 4}` has 17 elements and
contains the reflection, and the clique complex of `Cay(D_∞, T_4)` has the twin pairs
`{n, reflected n}` over each integer and collapses onto `VR_4(Z)`. ✓
