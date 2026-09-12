---
rg: 2
id: agent-aggregate-escape-global-schur-square-is-affine-wall
kind: claim
title: Globally killing the payload-root square imposes an affine selector wall, not one forbidden atom
distinct_from:
  schur-flip-square-exposes-payload-root-word: that exposes a word whose square has the desired value after compression to one forbidden simple; this computes what happens if one tries to turn that corner identity into a global zero-support relator.
  controlled-central-phase-finite-group-barrier: that gives the abstract finite-group obstruction to a nonlinear controlled phase; this identifies the exact affine commutator introduced by the tempting global square relation.
  agent-aggregate-escape-rfd-support-orientation-firewall: that rules out RFD support-orientation cells representation-theoretically; this rules out the most direct non-RFD-looking Schur-square quotient already at the selector syntax level.
---

**ESTABLISHED SHORTCUT FENCE.**  Fix one forbidden selector assignment and
the Schur flip-square data used in
`schur-flip-square-exposes-payload-root-word`.  Thus `P,Q` are fixed packet
words, `u,v` are commuting involutive implementers, and

```text
uPu=KP,       uQu=Q,       vPv=P,       vQv=KQ.
```

For

```text
d=P Q u v                                               (GS1)
```

one has the **global group-word identity**

```text
d^2=(P Q)^2=[P,Q]                                      (GS2)
```

(with the commutator convention adjusted harmlessly by inversion).  Hence
the apparently payload-sensitive extra relator

```text
d^2=1                                                   (GS3)
```

is simply the packet relation `[P,Q]=1`.

The Schur packet is class two.  Its visible selectors and the central sign
generate an elementary-abelian central subgroup `D`, and the commutator of
two fixed packet words is one fixed element of `D`.  Therefore on a joint
selector character `chi`, `(GS3)` is one affine parity equation

```text
chi([P,Q])=1.                                           (GS4)
```

The corrected words were chosen so that the forbidden assignment under
consideration lies on the opposite wall, where `[P,Q]=K`; this proves the
compressed identity `A_a d^2=K A_a`.  But the same fixed commutator generally
has the bad value on every selector character in an affine coset.  It cannot
single out `a` unless the selector dimension is one or the desired predicate
is already affine.

Consequently `(GS3)` would indeed force

```text
T A_a=0,                  T=(1-K)/2,                   (GS5)
```

but it also kills all negative-sign spectral sectors on the same affine
wall.  An exact perfect BCS representation extends across `(GS3)` only when
its context spectral support already avoids that entire wall.  Adding one
such relation for each forbidden atom asks that every surviving context
support lie in an intersection of affine parity constraints.  This is the
perfect-completeness linear/group-readable BCS gate, not a solution of it.

The proper Reynolds corner does not alter this calculation.  Compressing
`(GS2)` to the Reynolds atom makes the extra affine sectors invisible in the
local ledger, but an ordinary relator is global and still enforces `(GS4)` on
them.  Thus the proper-corner cell can safely use the root word to orient a
return and pay a companion exit; it cannot be converted to the one-row
support estimate `(ACO4)` by imposing its square globally.

DERIVATION
agent-aggregate-escape-global-schur-square-is-affine-wall via agent-aggregate-escape-global-schur-square-proof

