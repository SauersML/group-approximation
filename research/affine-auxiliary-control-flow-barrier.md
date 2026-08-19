---
rg: 2
id: affine-auxiliary-control-flow-barrier
kind: claim
title: Existential affine auxiliaries cannot encode nonlinear control-flow relations
distinct_from:
  one-hot-selector-parity-barrier: that rules out parity equations directly on three-or-more visible one-hot selector bits; this stronger CSP closure result also rules out hiding the nonlinearity behind arbitrarily many classical affine auxiliary bits.
---

Let `R subset F_2^m` be a relation on visible control bits. Suppose `R` is
defined by existentially quantifying auxiliary bits from a finite system of
affine parity equations:

```text
x in R  <=>  exists y in F_2^k : A x + B y = c.
```

Then `R` is an affine subset of `F_2^m`.

Consequently no parity-only compiler over commuting classical control bits,
even with arbitrarily many hidden affine auxiliaries, can exactly encode either

```text
{e_1,...,e_m}                 for m >= 3,
```

or the binary path-activation relation

```text
t = a AND b.
```

Thus replacing a multiway readable branch by a binary decision DAG does not by
itself evade the selector obstruction: as soon as the compiler must remember
that a deeper path is active exactly when two prior branch conditions hold, the
required visible relation is non-affine. Any successful exact LCS compiler must
obtain this nonlinearity from genuinely noncommutative/operator structure,
verifier-specific redundancy, or a gadget language richer than existential
affine control bits.
