---
rg: 2
id: sl3-generator-system-has-no-universal-lp
kind: claim
title: The canonical SL3 generator operator system has no universal lifting property
invalidates:
  - sl3-hnn-capture-via-universal-generator-lp
distinct_from:
  sl3-large-prime-hnn-matrix-range-capture: that asks only for asymptotic ucp lifts of trace-preserving star homomorphisms selected by one HNN presentation; this refutes the much stronger lifting property for every ucp map into every C-star quotient.
  property-t-alone-cannot-correct-tracial-choi-lifts: that uses a Kazhdan group without factorization to refute a property-T-only correction principle; this is specific to SL_3(Z), which has factorization, and uses the independently known failure of LLP of its full group C-star algebra.
  maslov-generator-complete-order-model-is-llp-strength: that gives the parallel enough-unitaries fence for a twisted symplectic generator system; this applies the same operator-system theorem to the untwisted SL3 lattice system used by the large-prime route.
---

Let `S=S^(-1)` be any finite unitary generating set of
`Lambda=SL_3(Z)` and

```text
E_S=span{1,u_s:s in S} subset C^*(Lambda).                        (SLP1)
```

Then `E_S` does not have the operator-system lifting property.

Indeed, its displayed unitaries generate `C^*(Lambda)`, so `E_S` contains
enough unitaries and its C-star envelope is `C^*(Lambda)`.  The
enough-unitaries theorem for operator systems says that LP of `E_S` would
imply LLP of its C-star envelope.  Ioana--Spaas--Wiersma, Corollary B
(`arXiv:2006.01874`), prove that `C^*(SL_n(Z))` fails LLP for every `n>=3`.
Thus LP of `(SLP1)` is impossible.

This does not refute a tracially selected lift.  LP quantifies over every
ucp map from `E_S` into every quotient, whereas
`sl3-large-prime-hnn-matrix-range-capture` concerns only the coordinate
representatives of a trace-preserving star homomorphism into a tracial
matrix ultraproduct which extends to the fixed arithmetic HNN group.  The
extra selection is exactly where a positive proof must live.

Proof: `sl3-generator-no-universal-lp-proof`.

