---
rg: 2
id: faithful-monotracial-target-is-canonical-reduced-sector
kind: claim
title: A faithful monotracial target collapses a character-rigid envelope map to the canonical reduced sector
distinct_from:
  unique-trace-signed-corner-quotient-forces-nonhyperlinear: that identifies the quotient and source only after GNS completion for an arbitrary tracial target; this uses faithfulness of the target trace to identify the C-star kernel itself.
  central-character-rigid-sector-forbids-relator-quotients: that proves the group kernel of a tracial quotient representation is trivial modulo the selected center; this proves the stronger analytic ideal equality for a faithful monotracial target.
  finitely-generated-monotracial-nonce-cstar-exists: that constructs the abstract target algebra; this shows exactly what a generating character-rigid group representation into that target would already have to accomplish.
---

**ESTABLISHED.**  Let `A` be a unital C-star algebra with unique tracial
state `tau`, and let

```text
Phi:A -> D
```

be a unital surjective star homomorphism.  If `D` has a faithful tracial
state `sigma`, then

```text
ker(Phi)={a in A:tau(a* a)=0}.                         (FMT1)
```

Consequently `Phi` identifies `D` with the C-star GNS image of `(A,tau)`,
not merely with its von Neumann GNS completion.

Apply this to a central character sector.  Let `Gamma` be countable, let
`q in C[Gamma]` be a nonzero central projection, and suppose the normalized
canonical trace `tau_q` is the unique trace of

```text
A_q=q C*(Gamma) q.
```

Then any unital generating sector representation in a simple monotracial
C-star algebra `D`, equivalently any unital surjection

```text
Phi:A_q -> D,                                         (FMT2)
```

forces

```text
D isomorphic to q_r C*_r(Gamma) q_r.                 (FMT3)
```

Here `q_r` is the image of `q` in the reduced group algebra.  In the finite
central-character case the right side is the corresponding reduced twisted
group C-star algebra (up to the standard finite matrix amplification).

In particular, take the finitely generated simple monotracial non-CE algebra
from `finitely-generated-monotracial-nonce-cstar-exists`.  Constructing the
generating representation requested by
`character-rigid-signed-bcs-quotient` would not be a soft envelope or quotient
step: it would prove that this already non-CE algebra is literally a reduced
central sector of the proposed group.  Its canonical reduced sector trace
would then be non-CE, so the group (or the associated finite central
extension) would already be nonhyperlinear.

Thus abstract monotracialization removes the target trace-simplex problem,
but supplies no extra analytic quotient freedom.  For faithful targets the
remaining character-rigid envelope problem is exactly a reduced twisted-group
algebra realization theorem.

The proof is `faithful-target-gs-kernel-proof`.
