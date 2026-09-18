---
rg: 2
id: free-group-boundary-shift-is-quantum-rigid
kind: claim
title: The boundary shift of a free group is a nearest-neighbour SFT that is 1-quantum rigid over every field, by domination along geodesics
distinct_from:
  euclidean-building-boundary-shifts-are-quantum-rigid: that is the open higher-rank question for building lattices; this is its rank-one case, which that node lists as suggested first step 1.
  boundary-crossed-product-is-a-leavitt-path-algebra: that proves the crossed-product algebra is finitely presented; this proves quantum rigidity directly, which is the property gate G2 of the master route asks for.
  permutive-triangle-sfts-are-quantum-rigid: that is a determinism mechanism over Z^2; this is a domination mechanism over a free group, where non-pointing letters force the far site.
---

**ESTABLISHED** (lane proof, elementary; bh-invent-12, 2026-09-18; not independently reviewed; no
priority claimed).

## Setting

- `Λ = F_d` (`d ≥ 1`) with free basis and symmetric generating set `S`, acting on its Cayley tree.
- For `c ∈ ∂F_d`, a reduced infinite word, put `x_c(γ) =` the first letter of the reduced word
  `γ^(-1) c`. This is the direction at `γ` toward `c`.
- `X = {x_c : c ∈ ∂F_d} ⊆ S^Λ`, with `(g.x)(h) = x(g^(-1) h)`. Then `c -> x_c` is an equivariant
  homeomorphism `∂F_d -> X`.

## Statement

1. **Finite type.** `X` is the nearest-neighbour SFT given by two rules: if `x(γ) = s`, then
   `x(γt) = t^(-1)` for every `t ≠ s`, and `x(γs) ≠ s^(-1)`.
2. **Rigidity.** `X` is `1`-quantum rigid, hence `D`-quantum rigid for every `D ≥ 1` (monotonicity),
   over every field and on every vector space. Quantum families are as in
   `fp-v-times-subshift-full-groups-force-quantum-rigidity`.
3. **Not free.** For `d ≥ 2`, `F_d` acts on `X` minimally and topologically freely, but not freely: `g ≠ 1` fixes
   its two endpoints. So `X` is a rigid calibration of gate G2 in the topologically free form.

## Proof

**1.** Both rules hold for `x_c`. Conversely, given `x` obeying them, follow `x` from `1`:
`s_1 = x(1)`, `s_2 = x(s_1)`, and so on. The second rule makes `s_1 s_2 ⋯` a reduced word `c`. The
first rule forces every site off the ray `{s_1 ⋯ s_j}` to point toward the ray, so `x = x_c`.

**2.** Let `(E_s(q))` be a `1`-quantum family on `W_0`. Sites within distance 2 commute.

*Step 1 (one-step domination).* Let `w` and `w' = wu` be adjacent, and `a ≠ u` a letter at `w`.
- The rule forces `x(w') = u^(-1)` whenever `x(w) = a`.
- All operators on the ball `B_1(w)` commute. Summing (Q3) over the extensions of each forbidden pair
  `(a at w, b at w')` with `b ≠ u^(-1)` gives `E_a(w) E_b(w') = 0`.
- Hence `E_a(w) = E_a(w) E_(u^(-1))(w') = E_(u^(-1))(w') E_a(w)`, written `E_a(w) ≤ E_(u^(-1))(w')`.

*Step 2 (transitivity).* Write `E ≤ F` for `E = EF = FE`. If `E ≤ F` and `F ≤ G`, then
`EG = EFG = EF = E` and `GE = GFE = FE = E`, so `E ≤ G`. This holds even though `E` and `G` were not
assumed to commute.

*Step 3 (far domination).* Let `q' ≠ q`, joined by the reduced path `q' = w_0, w_1 = w_0 u_1, …,
w_n = w_(n-1) u_n = q`. Put `u = u_1`, the letter at `q'` pointing to `q`, and `t = u_n^(-1)`, the
letter at `q` pointing to `q'`.
- For `s ≠ u`, Step 1 at `(w_0, w_1)` gives `E_s(q') ≤ E_(u_1^(-1))(w_1)`.
- Since `u_(i+1) ≠ u_i^(-1)` (the path is reduced), Step 1 at `(w_i, w_(i+1))` gives
  `E_(u_i^(-1))(w_i) ≤ E_(u_(i+1)^(-1))(w_(i+1))`.
- Step 2 then gives `E_s(q') ≤ E_t(q)` for every `s ≠ u`.
- By symmetry, `E_r(q) ≤ E_u(q')` for every `r ≠ t`.

*Step 4 (commutation).* Take letters `r` at `q` and `s` at `q'`.
- **`s ≠ u`:** `E_s(q') ≤ E_t(q)`, so `E_s(q')` commutes with `E_t(q)`. For `r ≠ t`,
  `E_r(q) E_s(q') = E_r(q) E_u(q') E_s(q') = 0`, and `E_s(q') E_r(q) = E_s(q') E_u(q') E_r(q) = 0`.
- **`s = u`:** `E_u(q') = I − Σ_(s' ≠ u) E_(s')(q')` commutes with `E_t(q)` by the first case. For
  `r ≠ t`, `E_r(q) ≤ E_u(q')`, so they commute.

So every pair commutes. `∎`

**Consequence (ring side).** With `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products` (no
freeness needed there), `LC(X, k) ⋊ F_d` is finitely presented over every field. That agrees with
`boundary-crossed-product-is-a-leavitt-path-algebra`, which is a consistency check.

## Lesson for general BH

In a tree, a letter that does **not** point toward a far site forces the whole geodesic, so it
dominates the far letter. Rigidity is then pure transitivity of "≤" between idempotents; no
commutation beyond distance 2 is ever assumed. This is the rank-one prototype of "hyperbolic geometry
supplies quantum rigidity". The higher-rank version, for building lattices, is obtained without a
direct argument, by transfer from finite presentation
(`a2-lattice-boundary-skew-shifts-are-quantum-rigid`).
