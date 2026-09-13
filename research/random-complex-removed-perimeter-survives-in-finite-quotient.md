---
rg: 2
id: random-complex-removed-perimeter-survives-in-finite-quotient
kind: claim
title: A mid-range random complex has a bounded set of triangles one of whose perimeters survives in a finite quotient of the complex minus that set
distinct_from:
  random-complex-bounded-removal-detected-by-quotient: that also asks the complex minus T to be pure, connected and a 1/4-local spectral expander; this is the detection condition alone, which implies that claim through bounded-removal-detection-from-detection-alone because the other conditions hold for every bounded removal
  random-complex-missing-triangle-detected-by-quotient: that asks a uniformly random missing triangle to be detected in π_1 of the sampled complex; this lets a bounded set of the complex's own triangles be chosen after sampling
  random-complex-group-no-quotients-above-exp-pn: that forbids nontrivial finite quotients of π_1(Y) above exp(n^eta/8); this asks for a finite quotient of π_1(Y \ T), which need not factor through π_1(Y)
---

**OPEN.** For every `0 < η < 1/2` there is a fixed integer `t` with the
following property. Let `p = n^(-1+η)` and `Y ~ Y(n,p)`. A.a.s. there are
`T ⊂ Y(2)` with `|T| <= t` and `Δ ∈ T` such that the perimeter of `Δ` survives
in some finite quotient of `π_1(Y \ T)`.

Through `bounded-removal-detection-from-detection-alone` this is equivalent to
`random-complex-bounded-removal-detected-by-quotient`. The purity and expansion
conditions there hold a.a.s. for every bounded removal
(`random-complex-bounded-removals-stay-local-expanders`), so this node holds the
whole open content of that claim.

## Constraints on any witness

1. **Order.** By `random-complex-bounded-removals-have-no-quotients-below-exp-pn`,
   a.a.s. every detecting quotient, for every admissible `T`, has order above
   `exp(n^η/8)`.
2. **The perimeter is a nontrivial element for a random choice.**
   - **Chapman--Peled.** Algorithm 1 samples `Y' ~ Y(n,p)` and a uniformly random
     missing triangle `Δ`, and puts `Z = Y' ∪ {Δ}`. The probability of
     `(Z,Δ) = (z,δ)` depends only on `|z|`, so given `Z`, `Δ` is uniform on
     `Z(2)`.
   - **Transfer.** The total variation distance between `Z` and `Y(n,p)` tends
     to `0` (`random-complex-mid-range-pair-properties`), so the pair `(Z,Δ)` is
     close in total variation to (a `Y(n,p)` sample, a uniform triangle of it).
   - **Conclusion.** Item 1 of that import says `∂Δ != 1` in `π_1(Z \ Δ) = π_1(Y')`.
     So for `Y ~ Y(n,p)` and a uniformly random `Δ ∈ Y(2)`, a.a.s. the perimeter of
     `Δ` is nontrivial in `π_1(Y \ Δ)`.

   For `t = 1` the claim is therefore a profinite detection statement about a
   nontrivial element.
3. **Kazhdan.** `Y \ T` is a `1/4`-local spectral expander for every bounded `T`.
   By Żuk's spectral criterion (not re-read here), `π_1(Y \ T)` has property (T).
   So it has no nontrivial amalgam or HNN splitting, and its finite quotients form
   expander families.

## Attempts

1. **Linear representations over finite fields: no mechanism.** A detecting
   representation into `GL_d(F_q)` has image of order at most `q^(d^2)`. By
   constraint 1 it needs `d^2 log q > n^η/8`. No representation of `π_1(Y \ T)`
   of dimension of order `n` is known: the cochain spaces of `K_n` carry no action
   of `π_1`, and the random complex has no symmetry to supply one.
2. **Covers assembled from cells: no mechanism.** A finite quotient is a connected
   finite cover. Labelled covers are counted by the first moment.
   - **Entropy barrier.** That count stops at order `exp(pn/3)`.
   - **Divergence.** Above `exp((1+ε)pn)` it diverges on free-edge events of
     vanishing probability (`random-complex-group-no-quotients-above-exp-pn`,
     Attempts). Removing `T` only makes those events likelier.
   - **Second moment.** A second-moment proof of existence would need the count
     truncated to a good event to be large and concentrated. The truncated count
     is undetermined, as on that node.
3. **One-relator-type structure: no mechanism.** `π_1(Y)` is the quotient of
   `π_1(Y \ T)` by the normal closure of at most `t` perimeters. By constraint 3,
   `π_1(Y \ T)` does not split, so amalgam and HNN constructions of finite
   quotients are unavailable. A detecting `ψ` makes
   `ψ(π_1(Y \ T)) / ⟨⟨ψ(∂T)⟩⟩` a finite quotient of `π_1(Y)`, which constrains
   nothing, since its order is unbounded.
4. **Choosing `T` after sampling: no gain.** Constraints 1 and 3 hold uniformly
   in `T`, so the freedom to pick `T` escapes neither the order bound nor
   rigidity.

## Exact gap

For some bounded `T ⊂ Y(2)`, a finite quotient of `π_1(Y \ T)` of order above
`exp(n^η/8)` in which a removed perimeter survives. No nontrivial finite
quotient of order above `exp(n^η/8)` is known for these random Kazhdan groups,
with or without the removal.
