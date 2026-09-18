---
rg: 2
id: perfect-extension-splittings-are-not-uniformly-integrable
kind: claim
title: "If Hom(G,R) vanishes on the central z, a measurable Euler splitting over a nonsingular Q-space with Koopman almost invariant vectors is never uniformly integrable; so for T-bar every space mapping equivariantly to S^1 has Koopman spectral gap"
distinct_from:
  lifted-thompson-t-extractable-cocycles-bounded-on-centre: that bounds cocycles of T-bar with a circle measure extraction by paradoxicality with explicit constants; this kills uniformly integrable Euler splittings over arbitrary nonsingular spaces, using only that Hom(G,R) vanishes on z, and recovers the circle case only qualitatively
  lifted-thompson-t-perfect-centre-cubically-elliptic: that uses perfectness against commensurating actions; this uses perfectness against measurable splittings of the Euler class
  central-extension-haagerup-from-measurable-euler-splitting: that is the positive criterion; this is the class-kill telling which of its witnesses cannot exist
artifacts: []
---

**ESTABLISHED** by `perfect-extension-splittings-are-not-uniformly-integrable-proof`.

**Setting.** As in `central-extension-haagerup-from-measurable-euler-splitting`: `z ∈ G` is
central of infinite order, `Q = G/⟨z⟩` acts nonsingularly on `(X, μ)` with Koopman
representation `κ`, and `β : G × X → R` is a measurable cocycle with `β(z, ·) = 1` a.e.

**Statement.**
1. Assume every homomorphism `G → R` vanishes on `z` (for instance `G` perfect). Let `ξ_n ≥ 0`
   be unit vectors with `‖κ(q)ξ_n − ξ_n‖ → 0` for all `q`, and put `ν_n = ξ_n² μ`. Then there is
   no subsequence along which, for every `g ∈ G`, the functions `β(g, ·)` are uniformly
   integrable for `{ν_n}`, that is, `lim_{K→∞} sup_n ∫_{|β(g,·)|>K} |β(g, ·)| dν_n = 0`.
2. In particular, if every `β(g, ·)` is essentially bounded, then `κ` has no almost invariant
   vectors. And if `μ` is a `Q`-invariant probability, then some `β(g, ·)` is not in `L¹(μ)`.
3. (For `T̄`.) `G = T̄` and `Q = T` satisfy the hypothesis of 1, since `T̄` is perfect. The integer
   part of the lift, `β(g, x) = ⌊g(x̃)⌋` with `x̃ ∈ [0,1)`, is a bounded Borel Euler splitting over
   `S^1`. So for every nonsingular `T`-space `(X, μ)` with a measurable `T`-equivariant map to `S^1`,
   the Koopman representation of `T` on `L²(X, μ)` has no almost invariant vectors.

**Named invariant.** `Hom(G, R)|_{⟨z⟩} = 0`.

**Death step.** The averages `u_n(g) = ∫ β(g, ·) dν_n` are asymptotically additive, and their
ultralimit is a homomorphism `G → R` with `u(z) = 1`.

## Attempts

- 2026-09-18 (swarm-0917-w9-w9-nv-follow): proved as stated; see the proof route.
