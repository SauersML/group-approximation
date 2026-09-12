---
rg: 2
id: binary-jacobson-opnorm-pi-selector-proof
kind: route
title: Apply the sparse standard-polynomial gap to the raw-cycle selected return
target: binary-jacobson-steinberg-head-root-is-mf-invisible
requires:
  - binary-jacobson-steinberg-cover-is-elementary
  - binary-jacobson-head-sector-has-native-two-qubit-packet
  - binary-jacobson-raw-cycle-selects-common-pi-intertwiner
  - opnorm-common-intertwiner-pi-gap-is-sparse-terminal
---

**VALID IMPLICATION; INVALIDATED AS A REDUCTION.**  The argument below is
correct after all words are evaluated in the fixed rank-five presentation.
However,
`binary-jacobson-typed-pi-selector-is-still-target-equivalent` proves that
its selector prerequisite, with its current existential sequential
quantifiers, is equivalent to this route's target.  The route therefore
does not provide an independent path to head MF-invisibility and is
invalidated pending an explicitly calibrated, independently nonvacuous
occurrence formula.

Assume a norm-corona representation retains the head.  Choose coordinate
lifts of the fixed Jacobson presentation and round the head involution.  On
an infinite subsequence its negative cut is nonzero.

Apply `binary-jacobson-raw-cycle-selects-common-pi-intertwiner`.  The source
tuple lies in `M_2 tensor I`, so Amitsur--Levitzki gives

```text
s_4(C_1,C_2,C_3,C_4)=0.                                (1)
```

The corrected literal target tuple is the native two-qubit packet.  Hence

```text
||s_4(D_1,D_2,D_3,D_4)||_op=8.                         (2)
```

The common return satisfies `(JPI1)`.  Use
`opnorm-common-intertwiner-pi-gap-is-sparse-terminal` with `m=4` and
`kappa=8`; it gives

```text
8(1-o(1)) <= 4! o(1),                                  (3)
```

a contradiction.  Therefore every norm-corona representation kills the
head.  The Steinberg/elementary identification transfers the conclusion to
the stated target.
