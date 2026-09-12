---
rg: 2
id: label-only-dressing-cannot-ungauge-a-whitehead-bridge
kind: claim
title: Label-only source and range dressings cannot remove a Whitehead selector gauge
artifacts:
  - research/whitehead-gauge-survives-label-dressing-proof.md
distinct_from:
  literal-whiteheads-give-gauged-moving-bridge-table: that identifies the actual full-Gram moving Whitehead bridges and their selector gauge; this proves that composing those bridges with independently authenticated coefficient normalizers cannot remove that gauge.
  fano-semidir-bridges-are-wrong-subgroup-or-gauged: that separates pure coefficient and actor-moving words by finite-semidir support; this is the representation-level tensor calculation for arbitrary label-only dressings on either side of an already authenticated bridge.
  el20-six-moving-coefficient-square-bridges: that asks for a genuinely ungauged subgroup-moving occurrence; this rules out obtaining one by dressing the known Whitehead bridge with any number of already ungauged source/range normalizers.
---

**ESTABLISHED SCOPED NO-GO.**  Let one full-Gram bridge between two packet
charts be typed, after identifying source and range with `L tensor M`, as

```text
J=M_J tensor D,
```

where `M_J` is the prescribed label transport and `D` is the selector
multiplicity unitary.  Let every source or range dressing used in a composite
be independently authenticated as label-only:

```text
A_r=N_r tensor 1,              B_s=P_s tensor 1.
```

Then every alternating composite containing exactly one occurrence of `J`
is again typed

```text
N tensor D.                                                   (LDG1)
```

In particular, if the target ungauged typing fixes that label product as
`N tensor 1`, its normalized Hilbert--Schmidt discrepancy is exactly

```text
||N tensor D-N tensor 1||_2=||D-1||_2.                       (LDG2)
```

The same conclusion holds with `o_2(1)` chart errors, up to their sum.  Thus
the literal moving Whitehead from
`literal-whiteheads-give-gauged-moving-bridge-table` cannot be converted into
the bridge required by `el20-six-moving-coefficient-square-bridges` by
precomposing or postcomposing it with pure Fano roots, signed-Hecke
normalizers, canonical Leavitt compressions which preserve the relevant
chart, or any other occurrences already typed as identity on multiplicity.

This does not rule out a composite containing a second genuinely gauged
mixed/opposite-root occurrence whose multiplicity action cancels `D` while
the total label action still moves the signed-Hecke source once.  It proves
that such a second occurrence is necessary; label-only dressing is not a
new route.

No Property `(T)`, Kazhdan input, matrix approximation theorem, or literature
result is used.

DERIVATION
whitehead-gauge-survives-label-dressing-proof
