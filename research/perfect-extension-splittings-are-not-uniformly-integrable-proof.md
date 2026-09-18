---
rg: 2
id: perfect-extension-splittings-are-not-uniformly-integrable-proof
kind: route
title: "Average the splitting cocycle against the almost invariant densities; uniform integrability makes the averages asymptotically additive, and the ultralimit is a homomorphism nonzero on z"
target: perfect-extension-splittings-are-not-uniformly-integrable
requires:
  - lifted-thompson-t-perfect-centre-cubically-elliptic
---

Notation as in the target. As in Step 1 of
`central-extension-haagerup-from-measurable-euler-splitting-proof`, we may assume the cocycle
identity holds everywhere on a conull invariant set. Then `β(z, ·) = 1`.

**Part 1.** Suppose, for contradiction, that `β(g, ·)` is uniformly integrable (UI) for `{ν_n}`
for every `g` (after passing to the subsequence). We derive a contradiction in five steps.

- (a) *Transport.* `h_*ν_n` has density `(κ(h)ξ_n)²`, so
  `‖h_*ν_n − ν_n‖_1 ≤ ‖κ(h)ξ_n − ξ_n‖_2 · ‖κ(h)ξ_n + ξ_n‖_2 ≤ 2‖κ(h)ξ_n − ξ_n‖_2 → 0`.
- (b) *Averages.* UI families are bounded in `L¹`. So `u_n(g) = ∫ β(g, ·) dν_n` is finite and
  `sup_n |u_n(g)| < ∞`. Also `u_n(z) = 1`.
- (c) *Defect.* By the cocycle identity and a change of variables,
  `u_n(gh) − u_n(g) − u_n(h) = ∫ β(g, hx) dν_n(x) − u_n(g) = ∫ β(g, ·) d(h_*ν_n − ν_n) =: D_n`.
- (d) *Defect → 0.* Fix `K` and split `β(g, ·) = β_K + r_K`, where `β_K = β(g, ·) 1_{|β(g,·)| ≤ K}`.
  - `|∫ β_K d(h_*ν_n − ν_n)| ≤ K ‖h_*ν_n − ν_n‖_1 → 0` by (a).
  - `∫ |r_K| dν_n ≤ ε(K) := sup_n ∫_{|β(g,·)|>K} |β(g, ·)| dν_n`, which tends to `0` as `K → ∞`.
  - `∫ |r_K| d(h_*ν_n) = ∫ |r_K(hx)| dν_n(x)`. Here `x ↦ β(g, hx) = β(gh, x) − β(h, x)` is a
    difference of two UI families, so it is UI. Hence this term is at most some `ε'(K)`, also
    tending to `0`, uniformly in `n`.

  So `limsup_n |D_n| ≤ ε(K) + ε'(K)` for every `K`, and therefore `D_n → 0`.
- (e) *Ultralimit.* Let `ω` be a nonprincipal ultrafilter on `N`, and put `u(g) = lim_ω u_n(g)`.
  It is finite by (b), additive by (c) and (d), and `u(z) = 1`. This is a homomorphism `G → R`
  that is nonzero on `z`, contradicting the hypothesis. ∎(1)

**Part 2.**
- *Bounded splitting.* If every `β(g, ·)` is in `L^∞(μ)`, it is UI for every family of
  probabilities `ν_n ≪ μ`. So almost invariant vectors would contradict 1.
- *Invariant probability.* If `μ` is an invariant probability, `ξ_n = 1` is an invariant vector.
  A single integrable function is UI, so some `β(g, ·)` fails to be integrable. ∎(2)

**Part 3.**
- *Perfectness.* `T̄` is perfect by `lifted-thompson-t-perfect-centre-cubically-elliptic`
  (item 2). So `Hom(T̄, R) = 0`.
- *The circle splitting.* For `x ∈ S^1 = R/Z`, let `x̃ ∈ [0,1)` be its lift, and set
  `β(g, x) = ⌊g(x̃)⌋` for `g ∈ T̄`.
  - Cocycle identity: every `g ∈ T̄` commutes with `y ↦ y + 1`, and `hx` has lift
    `h(x̃) − ⌊h(x̃)⌋`. So `gh(x̃) = g(\widetilde{hx}) + ⌊h(x̃)⌋`, which gives
    `β(gh, x) = β(g, hx) + β(h, x)`.
  - Normalization: `z(x̃) = x̃ + 1`, so `β(z, ·) = 1`.
  - Boundedness: `g` is increasing with `g(1) = g(0) + 1`, so
    `β(g, ·) ∈ {⌊g(0)⌋, ⌊g(0)⌋ + 1}`.
- *Pulling back.* If `f : X → S^1` is measurable and `T`-equivariant a.e., then
  `β_X(g, x) = β(g, f(x))` is a bounded measurable Euler splitting over `X`. Part 2 then gives
  the conclusion. ∎(3)

**Scope.**
- Part 3 recovers, qualitatively and from perfectness alone, the Koopman half of the circle
  kill in `lifted-thompson-t-extractable-cocycles-bounded-on-centre`. It covers the `T`-spaces
  `S^1` itself, `S^1 × S^1` (off the diagonal), and orbits `O ⊂ S^1` with counting measure
  (subsuming the TC1 kill). Spaces on which `z` acts nontrivially, such as `R`, are not
  `T`-spaces, so they are outside its scope.
- It does not give that kill's quantitative constants. It says nothing about representations
  that are not Koopman representations of spaces over `S^1`.
