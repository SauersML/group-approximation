---
rg: 2
id: finite-local-schur-extension-preserves-forbidden-mass
kind: claim
title: Finite context-local Schur extension preserves forbidden mass exactly
distinct_from:
  context-local-schur-packet-marked-extension: that extends an arbitrary representation after infinite amplification to prove exact completeness; this gives a finite amplification for finite-dimensional inputs and tracks normalized forbidden mass.
  hs-schur-packet-gap-amplification: that asks for factor-two amplification after preprocess-power-compose; this proves that the Schur packet/composition layer by itself has an exact no-amplification model.
---

**ESTABLISHED.**  Let a finite BCS word system have finitely many contexts
`c`, with commuting selector involutions and predicates `f_c`.  Attach to
each context its finite Schur--Clifford packet `A_c<=B_c` from
`predicate-rank-gate-doubles-restriction-multiplicity`, but impose no
cross-context relations on the new packet generators.

Every exact finite-dimensional representation `pi` of the selector word
system has a finite amplification

```text
pi tensor I_L                                             (FSE1)
```

which extends to an exact representation of every context packet
simultaneously.  Moreover all normalized selector spectral weights are
unchanged.  Hence if

```text
q=sum_c mu_c tau(F_c)                                    (FSE2)
```

is any weighted total of forbidden selector atoms before extension, the
same quantity after exact packet extension satisfies

```text
q'=q.                                                    (FSE3)
```

All local packet multiplication, rank-gate, and contextwise selector
coupling relators have zero defect in this model.

Consequently no estimate

```text
q'>=min(2q,alpha)-C sqrt(E)                              (FSE4)
```

can follow from context-local Schur packet rows alone, for any `alpha>0`,
when `E` is their relator energy.  Indeed take one satisfiable finite
predicate having both an allowed and a forbidden classical assignment, and
take a rational direct sum of the two scalar selector representations.  It
has any prescribed sufficiently small rational `0<q<alpha/2`.  Apply the
finite extension above.  Then `E=0` and `q'=q<2q`, contradicting `(FSE4)`.

Thus the Schur rank packet is a **readout** of already synchronized forbidden
mass, not a gap amplifier.  Every factor-two gain in
`hs-schur-packet-gap-amplification` must come from new cross-context
preprocess/powering/answer-reduction rows.  Those rows must rule out the exact
local extension `(FSE1)` by charging incompatibility between the separately
valid context corrections.

This isolates the true frontier: a perfect-complete tracial quantum-PCP
synchronization lemma on the shared selectors.  Fixed packet exactification,
rank jumps, and local Schur composition do not supply any part of the
doubling inequality.

