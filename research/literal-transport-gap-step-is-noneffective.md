---
rg: 2
id: literal-transport-gap-step-is-noneffective
kind: claim
title: The current literal transport path has a non-effective spectral-gap gate
distinct_from:
  effective-transport-modulus: This identifies the exact missing gate in the current proof; it does not assert that no effective modulus exists.
  uniform-finite-mf-obstruction: That compactness theorem proves existence of a finite threshold; this claim audits why it does not compute one.
artifacts:
  - GroupApproximation/Sofic/WeakMFVectorGNS.lean
  - GroupApproximation/Sofic/KazhdanCornerCompression.lean
  - GroupApproximation/Sofic/ManuscriptKazhdanTransport.lean
  - GroupApproximation/Sofic/LiteralBasePropertyTBridge.lean
  - GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean
---

**ESTABLISHED BY SOURCE AUDIT.** The current finite-stage transport path does
not expose a numerical function from the forty-one relator defects to the
spectral cutoff used in Kazhdan transport.

The first missing modulus is
`WeakMFVectorGNS.hermitianAverage_eventually_no_intermediate_eigenvalues`.
Its conclusion is an unspecified `exists N`; its proof assumes failure,
reindexes a bad eigenvector sequence, passes to `Hyperreal` standard parts,
and applies the exact Kazhdan pair only after taking that limit. The module
docstring explicitly identifies this declaration as non-effective and states
that removing the limit requires a group-algebra sum-of-squares certificate.

`KazhdanCornerCompression.hermitianAverage_eventually_top_spectral_residual`
calls that theorem directly. Everything printed after this call is
quantitative, but only after the unknown stage `N`; therefore unfolding
`KazhdanAsymptoticCommutant.transport` or
`ManuscriptKazhdanTransport.finiteStageKazhdanTransport` cannot produce a
relator threshold.

The rational sum-of-squares certificate in
`LiteralP13HodgeCertificate.lean` is a certificate for the six-generator P13
rotation source. Transport, however, uses the full affine base. The base gets
property (T) in `LiteralBasePropertyTBridge.lean` by an exact fixed-subspace
projection and a circumcenter of the entire translation orbit. That argument
produces the honest tolerance recorded in
`literal-base-explicit-kazhdan-pair`, but it is not a finite group-ring
sum-of-squares identity and has no relator-error ledger. In an approximate
tuple, the arbitrary rotation conjugators in the two-conjugate translation
normal form have unbounded word length, so naive telescoping does not give a
uniform small orbit bound.

Thus even the exact `219*delta` P13 substitution estimate stops before the
needed robust affine gap. The smallest sufficient new input is either

1. a finite rational sum-of-squares certificate for the literal affine base,
   together with free-word replay areas, or
2. an explicit finite-stage relative-property-`(T)` theorem for the affine
   relations that outputs the same spectral cutoff residual as a numerical
   function of the twenty base-relator defects.

After that gate, a separate finite ledger is still required for compressor
transport, central spectral-corner restriction, and the marked-word estimate.
Accordingly no explicit positive defect threshold for
`effective-transport-modulus` is justified by the current declarations.

No `invalidates` entry is attached: current main has no route targeting
`effective-transport-modulus`; this node records the obstruction without
inventing a dead route.
