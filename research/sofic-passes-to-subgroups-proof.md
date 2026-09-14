---
rg: 2
id: sofic-passes-to-subgroups-proof
kind: route
title: Pull a sofic approximation back along the injection
target: sofic-passes-to-subgroups
requires: []
artifacts:
  - GroupApproximation/Sofic/SoficTransfer.lean
---

Let `f : H -> G` be injective and let `G` be sofic. Fix a finite `F <= H` and
`epsilon > 0`. Soficity of `G` applied to the finite set `f(F)` and the same
`epsilon` supplies a finite model `M` with an almost-multiplicative,
almost-separating map on `f(F)`.

Define the model for `H` on the same carrier by `x |-> M.map (f x)`.

* *Almost multiplicative.* For `g, k` in `F`, both `f(g)` and `f(k)` lie in
  `f(F)`, and `f(gk) = f(g) f(k)`, so the estimate for `M` at the pair
  `(f(g), f(k))` is the estimate required at `(g, k)`.
* *Almost separating.* For distinct `g, k` in `F`, injectivity of `f` gives
  `f(g) != f(k)`, so the separation estimate for `M` applies.

This is exactly the `SoficApproximation.comap` construction, and the theorem
is `isSofic_of_injective` in
`GroupApproximation/Sofic/SoficTransfer.lean`; the isomorphism form
`isSofic_mulEquiv_iff` follows by applying it in both directions. The
contrapositive `(SPS1)` is immediate. `∎`

The statement is kernel-checked in the development, so this route records a
formalized import rather than a new argument.
