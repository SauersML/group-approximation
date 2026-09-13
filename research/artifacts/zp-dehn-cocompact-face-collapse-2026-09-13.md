# Zaremsky 1.17: where finite-index faces enter, and what replaces them (part 1)

Lane z1-17-dehn-cocompact, 2026-09-13. Unreviewed analysis. It feeds
`zaremsky-1-17-dehn-function-from-cocompact-action-data`,
`dehn-bound-from-action-data-without-finite-index-faces` and
`some-action-violates-dehn-bound-without-finite-index-faces`.

## 1. The hypothesis in Llosa Isenrich–Weis

Source: arXiv:2608.07191v1, pp. 10–14, read on 2026-09-13.

- Section 3 assumes that `X` is *locally finite in degree 2* (Definition 2.23:
  `[G_e : G_σ] < ∞` for every 2-cell `σ` and edge `e ⊂ σ`). For a cocompact
  `G`-simplicial complex this says exactly that every edge lies in finitely
  many 2-cells. The 2-cells containing `e` form finitely many `G_e`-orbits,
  and the orbit of `σ` is `G_e / G_σ`.
- `X̂` (Remark 2.22) has vertex fibers `EG_v`, edge fibers `EG_e × e`, and for
  each 2-cell `σ` a `G_σ`-orbit of hexagonal disks `gP_σ`. The disks are
  attached through `G_σ`-equivariant maps `ψ_{e,σ} : EG_σ^(0) = G_σ → EG_e^(0)`.
- Theorem 3.3 (tree diagrams) uses no hypothesis on 2-cells.
- The hypothesis enters in Lemma 3.4 (face collapse). To push a loop edge
  lying over `e` across `σ`, the loop vertex `γ(0) ∈ EG_e^(0)` is joined inside
  `EG_e` to the image of `EG_σ^(0)` by a path `μ_1` of length
  `≤ [G_e : G_σ] − 1`. Remark 3.5 turns this into the constant `C(X)` used in
  Proposition 3.6, which converts a van Kampen diagram of area `A` into a tree
  diagram, lengthening the loop by `(2C + 4)·A` and adding `A·(C + 1)` 2-cells.
  (Pages 15–16, the rest of the proof of Theorem C, are not read yet.)

## 2. Face collapse without the hypothesis

Let `p ∈ G_e` be the position of the loop over `e`. Pushing across `σ` costs

```text
c(p, σ) = min_{s ∈ G_σ} d_{G_e}(p, ψ_{e,σ}(s)) ≤ edist_X( d_G(p, ψ_{e,σ}(G_σ)) ),
```

using `d_{G_e}(g_0, g_1) ≤ dist^G_{G_e}(d_G(g_0, g_1))` (Remark 3.2 of the
paper). Nothing else in the face collapse changes. When `[G_e : G_σ] < ∞`,
`c(p, σ) ≤ [G_e : G_σ] − 1` for every `p`. In general `d_G(p, ψ_{e,σ}(G_σ))`
is the `G`-distance from the loop to the disks over `σ`, and the length of the
loop does not bound it: the 2-cells containing `e` include infinite orbits
`G_e·σ_0 ≅ G_e / G_σ`, all at `X`-distance 0 from `e`, at `G`-distances from
`p` that grow along the coset space.

So a proof of (UB) in general cannot take an arbitrary minimal-area diagram
over `X`. It has to choose a filling whose 2-cells are `G`-close to the loop,
and the cost of that choice is a datum that `δ_X`, `δ_{G_v}` and distortion do
not obviously control.

## 3. A candidate extra datum: coarse intersection at corners

Suppose a 2-cell `σ = [v_1, v_2, v_3]` meets the current loop along two
consecutive edges `e = [v_1, v_2]` and `f = [v_2, v_3]`. The loop positions
`p_e ∈ G_e`, `p_f ∈ G_f` satisfy `d_{G_{v_2}}(p_e, p_f) ≤ L`, where `L` is the
length of the connector inside `EG_{v_2}`. Since `X` is simplicial and the
action has no inversions, `G_e ∩ G_f = G_{v_1} ∩ G_{v_2} ∩ G_{v_3} = G_σ`.
The cost of pushing across `σ` at this corner is governed by

```text
κ_X(L) = max over corners (v; e, f; σ) of
         sup { d_{G_v}(p, G_σ) : p ∈ G_e, d_{G_v}(p, G_f) ≤ L },
```

the coarse intersection function of the two edge stabilizers inside the vertex
stabilizer, relative to their intersection. (With the conjugations `c_{e,σ}`
of the complex of groups the cosets shift by bounded elements; that does not
change `κ_X` up to `≃`.)

Calibrations:

- Under `[G_e : G_σ] < ∞`, `G_e` lies in a bounded neighbourhood of `G_σ`, so
  `κ_X` is bounded.
- For `A × B` acting on `T_A × T_B` (products of Bass–Serre trees), square
  stabilizers `G_{e_A} × G_{e_B}` usually have infinite index in the edge
  stabilizers. At a corner, `G_e = G_{e_A} × B_w`, `G_f = A_v × G_{e_B}` and
  `G_v = A_v × B_w`. If `p = (a, b)` with `a ∈ G_{e_A}` and
  `d(p, G_f) ≤ L`, then `d_{B_w}(b, G_{e_B}) ≤ L`, so
  `d(p, G_{e_A} × G_{e_B}) ≤ L`. Hence `κ_X(L) ≤ L`: products of trees are in
  the linear regime.

A disk diagram need not have corners (a hexagon triangulated from a central
vertex has none), but pushing across a 2-cell with one boundary edge creates
two boundary edges carrying the disk's own positions. Whether a collapse order
exists in which every uncontrolled collapse happens at a corner is the first
open step.

## 4. Next targets

1. Prove Theorem C with `[G_e : G_σ] < ∞` replaced by a bound on `κ_X`
   (conjectural form:
   `δ_G(n) ≼ δ_X(n) · max_v δ_{G_v}( edist_X‾( κ_X‾(D δ_X(n)) ) )`), or find
   where corner collapses cannot be arranged.
2. Search for an action in setting (S) of the root whose `κ_X` is
   superpolynomial while `δ_X`, the `δ_{G_v}` and all stabilizer distortions
   are polynomial. That is the shape a counterexample to (UB) has to take.
   Convex or quasiconvex stabilizers (CAT(0), hyperbolic, Deligne complexes of
   2-dimensional Artin groups) keep `κ_X` linear, so the search has to leave
   them.
