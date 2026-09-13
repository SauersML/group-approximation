---
rg: 2
id: zaremsky-1-17-dehn-function-from-cocompact-action-data
kind: claim
title: "Zaremsky Problem 1.17 resolved: is the Dehn function of a group bounded by its action data on a simply connected complex?"
root: true
distinct_from:
  cocompact-action-data-do-not-determine-dehn-function: that settles the literal two-sided reading negatively with F_2 x Z versus F_2 * Z; this is the upper-bound reading of the problem, open beyond trees and finite-index faces.
  llosa-isenrich-weis-dehn-bound-for-cocompact-actions: that is the imported upper bound for trees and for simplicial complexes whose face stabilizers have finite index in their edge stabilizers; this is the question in general.
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 17, verbatim:
"(Vague:) If a finitely presented group acts cocompactly on a highly connected
complex with finitely presented cell stabilizers, prove that the Dehn function
is determined by the filling function of the complex, the Dehn functions of the
stabilizers, and the distortion of the stabilizers."

**Setting (S).** A group `G` acts cellularly, cocompactly and without
inversions on a simply connected simplicial complex `X` whose combinatorial
Dehn function `δ_X(n)` is finite for every `n`. Vertex stabilizers are finitely
presented and edge stabilizers finitely generated, so `G` is finitely presented
(Brown's criterion). For the first Dehn function, simple connectivity is the
relevant connectivity; higher connectivity matters for higher Dehn functions.
Write `dist_X(n) = max { dist^G_{G_σ}(n) : σ a cell of X, dim σ ≤ 2 }`
(distortion in the whole group) and `f̄` for the superadditive closure of `f`.

**Reading (R1), "determined by" as a two-sided statement: false.**
`cocompact-action-data-do-not-determine-dehn-function` shows that `F_2 × ℤ`
and `F_2 * ℤ` act on trees with identical data and have Dehn functions `n²`
and `n`.

**Reading (R2), an upper bound: the question this root tracks.** In setting (S),
is

```text
δ_G(n) ≼ δ_X(n) · max_v δ_{G_v}( dist_X‾( δ_X(n) ) )          (UB)
```

Llosa Isenrich–Weis (arXiv:2608.07191, Theorems B and C;
`llosa-isenrich-weis-dehn-bound-for-cocompact-actions`) prove (UB), with edge
distortion only, when `X` is a tree (with the factor `n` in place of `δ_X(n)`)
and when `[G_e : G_σ] < ∞` for every 2-cell `σ` and edge `e ⊂ σ`. Their paper
says this answers Zaremsky's question in these cases. The open content is
setting (S) without the finite-index hypothesis on 2-cell stabilizers.

For a fixed data triple, the countably many actions in (S) always admit some
dominating function, so the meaningful form of the problem is an explicit
formula such as (UB), not the bare existence of a bound.

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-1-17-by-yes` requires
  `dehn-bound-from-action-data-without-finite-index-faces`.
- **No**: `zaremsky-1-17-by-no` requires
  `some-action-violates-dehn-bound-without-finite-index-faces`.

Never write a `requires: []` route into this claim. A different explicit
formula valid throughout (S) also answers the problem; record it as a new
answer claim with its own route here.

## Attempts

- 2026-09-13 (z1-17-dehn-cocompact): imported Theorems B and C of Llosa
  Isenrich–Weis and settled (R1) negatively. Next target: where their proof
  uses `[G_e : G_σ] < ∞` (moving edge-stabilizer discrepancies across 2-cells)
  and whether 2-cell stabilizer distortion or distortion of intersections of
  stabilizers is forced. Products of trees violate the hypothesis; checking
  that they satisfy (UB) (Theorem B for the factors plus the product formula
  for Dehn functions) is the first calibration.
- 2026-09-13, same lane: `research/artifacts/zp-dehn-cocompact-face-collapse-2026-09-13.md`
  and its part 2. Without finite-index faces the lifted complex `X̂` of the
  paper is still simply connected, so `δ_G ≃ δ_{X̂}` throughout (S). (UB)
  reduces to bounding face-collapse detours; with trivial face stabilizers
  these are twists along infinite edge links, i.e. relations among
  edge-stabilizer elements inside vertex stabilizers. Products of trees keep
  twists linear. Related work to read before any novelty claim: Sauer–Weis,
  arXiv:2606.25897 (polynomial homological Dehn functions from non-proper
  actions).
