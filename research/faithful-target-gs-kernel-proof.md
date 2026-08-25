---
rg: 2
id: faithful-target-gs-kernel-proof
kind: route
title: Identify the quotient kernel by faithfulness of the pulled-back unique trace
target: faithful-monotracial-target-is-canonical-reduced-sector
requires:
  - finitely-generated-monotracial-nonce-cstar-exists
  - unique-trace-signed-corner-quotient-forces-nonhyperlinear
---

Let `sigma` be the faithful trace of `D`.  Since `Phi` is unital and onto,
`sigma Phi` is a tracial state of `A`; uniqueness gives

```text
sigma Phi=tau.                                        (FKI1)
```

For every `a in A`,

```text
a in ker(Phi)
 iff Phi(a* a)=0
 iff sigma(Phi(a* a))=0
 iff tau(a* a)=0.                                    (FKI2)
```

The second equivalence uses faithfulness of `sigma`.  This proves `(FMT1)`.
The quotient of `A` by the right side of `(FMT1)` is precisely the norm-closed
GNS image of `(A,tau)`, so `D` is isomorphic to that image.

For `A=qC*(Gamma)q` and the normalized canonical corner trace, the GNS image
is `q_r C*_r(Gamma)q_r`.  If `q` is a finite central-character projection,
the usual central-fibre decomposition identifies this corner with the
corresponding reduced twisted group algebra, up to finite matrix
amplification.  The simple monotracial algebra constructed in
`finitely-generated-monotracial-nonce-cstar-exists` has faithful trace because
the trace kernel is a closed two-sided ideal and the algebra is simple.
