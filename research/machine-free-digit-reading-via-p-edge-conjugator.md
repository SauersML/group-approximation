---
rg: 2
id: machine-free-digit-reading-via-p-edge-conjugator
kind: route
title: Attach the final digit-reading p-edge through its corona conjugator
target: machine-free-digit-reading-group-is-mf
requires:
  - machine-free-digit-reading-base-is-regular-mf
  - digit-reading-p-edge-corona-conjugator
  - twisted-hnn-mf-permanence-with-corona-conjugator
---

The presentation `Gamma^K` is the HNN extension of the p-free base `Gamma'`
whose stable letter `p` identifies

```text
<t,a_1,...,a_s>  ->  <td,a_1,...,a_s>,
t |-> td,                  a_i |-> a_i.
```

The first prerequisite supplies a regular operator-MF realization of the
base.  The second supplies, in one matrix-corona embedding of that
realization, the unitary implementing the displayed edge isomorphism.
`twisted-hnn-mf-permanence-with-corona-conjugator` then gives a regular
operator-MF realization of the HNN extension.  Therefore `Gamma^K` is
operator-MF.
