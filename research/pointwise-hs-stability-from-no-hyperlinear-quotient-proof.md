---
rg: 2
id: pointwise-hs-stability-from-no-hyperlinear-quotient-proof
kind: route
title: Read the almost-representation in the tracial matrix ultraproduct
target: pointwise-hs-stability-from-no-hyperlinear-quotient
requires: []
artifacts:
  - GroupApproximation/Stability/MixedApproximation.lean
---

Fix maps `phi_n : G -> U(d_n)` with
`‖phi_n(gh)-phi_n(g)phi_n(h)‖_(2,d_n) -> 0` for every fixed `g,h`, and
suppose every hyperlinear quotient of `G` is trivial.

Let `𝒰` be an ultrafilter on `N` refining the cofinite filter and let
`M = prod_𝒰 M_(d_n)(C)` carry the ultraproduct trace.  The null subgroup of
`prod_n U(d_n)` consisting of sequences with `‖u_n-1‖_2 -> 0` along `𝒰` is
normal, and the vanishing defects put every
`(phi_n(g)phi_n(h))^(-1)phi_n(gh)` inside it.  Hence
`rho(g) = [(phi_n(g))_n]` is a group homomorphism `G -> U(M)`.

The target belongs to the class: `U(M)` is by definition a group of
unitaries of a tracial matrix ultraproduct, so it is hyperlinear, via the
identity embedding.  This is the exact analogue of
`normMatrixCoronaUnitary_isOperatorMF` in the operator-norm slot, and it is
the one step not yet present in Lean.  Hyperlinearity passes to subgroups,
so `rho(G)` is a hyperlinear quotient of `G`, hence trivial: `rho = 1`.

Triviality of `rho` gives `‖phi_n(g)-1‖_(2,d_n) -> 0` along `𝒰` for each
`g`.  To upgrade this to convergence along the cofinite filter, use the bad
set argument already formalized in the Hamming slot
(`HasNoNontrivialMixedQuotient.hammingAlmostRepresentation_trivial`,
`GroupApproximation/Stability/MixedApproximation.lean:260`): if the
conclusion failed for some `g` and some `eps>0`, the set of `n` with
`‖phi_n(g)-1‖_(2,d_n) >= eps` would be infinite; choose `𝒰` through it and
through the cofinite filter, and the two displayed statements contradict
each other at a single `n`.  Since the ultrafilter is chosen only after the
hypothetical bad set, no compatibility between different `g` is needed.

Therefore every normalized-HS almost representation of `G` is
asymptotically trivial, and the constant trivial representations witness
pointwise HS stability.

The converse direction is not claimed here and is false in general as
stated -- pointwise stability witnessed by *some* representations does not
force the witnesses to be trivial.  It does hold for minimally almost
periodic `G`, where the only genuine finite-dimensional representation is
trivial; that is the case used for `U` in
`leavitt-steinberg-hs-stability-fork`.
