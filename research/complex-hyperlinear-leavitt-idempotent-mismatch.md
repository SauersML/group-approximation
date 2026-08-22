---
rg: 2
id: complex-hyperlinear-leavitt-idempotent-mismatch
kind: claim
title: The binary Leavitt corner idempotent stays distance two from idempotency in every complex hyperlinear model
distinct_from:
  leavitt-corner-idempotent-unital-surjection: That constructs the idempotent in the characteristic-two group algebra and maps its corner onto the Leavitt algebra; this proves that the same two group elements do not form an idempotent over the complex scalars used by hyperlinearity.
  augmentation-blocks-unital-leavitt-family: That forbids a unital Leavitt family in an integral group ring by augmentation; this is the exact scalar-characteristic mismatch in complex tracial representations of the Leavitt unit group.
  leavitt-multiplicative-trace-floor: That gives a positive matrix gap after four coefficient contractions have already been decoded; this says why multiplicative group microstates alone do not provide those contractions.
  trace-blindness-sharpness: That gives a general II1-factor counterexample to detecting one-sided compression by a conjugation-invariant trace quantity; this computes the failure of the specific order-three Leavitt corner element before any compression argument begins.
---

Let `R=L_(F_2)(1,2)`, `G=R^x`, and let `g in G` be the explicit order-three
unit from `leavitt-corner-idempotent-unital-surjection`.  The element

```text
e_2=[g]+[g^2] in F_2[G]
```

is an idempotent and its evaluation in `R` is `1`.  But the formally identical
complex group-algebra element

```text
a=u_g+u_(g^2) in C[G]
```

satisfies the exact identity

```text
a^2-a=2*1.                                                   (CHL1)
```

Consequently, in every unital representation into a complex finite tracial
algebra,

```text
||a^2-a||_2=2,
```

and the same defect tends to `2` for any asymptotic unitary model in which
`u_g^3 -> 1`.  Thus neither a hyperlinear embedding nor its matrix
microstates turn the characteristic-two corner into a projection, even
approximately.

The genuine complex spectral projection

```text
p=(2-u_g-u_(g^2))/3
```

has trace `2/3` under the regular character, but it carries no evaluation map
to `R` and no binary Leavitt relation.  The module identity `R ~= R (+) R`
therefore cannot be read from this finite spectral corner.  Even the exact
self-similar subgroup `delta(G) x S_3 <= G` only makes the `S_3` spectral
corners commute with a second regular copy of `G`; compression to either
corner preserves the canonical trace of that copy and imposes no equivalence
between the two corner projections.  Any direct
non-hyperlinearity proof must first decode additive/coefficient multiplication
on a positive-trace corner (the open Leavitt coefficient-decoder step); the
multiplicative unit-group relations and canonical trace alone do not do it.
