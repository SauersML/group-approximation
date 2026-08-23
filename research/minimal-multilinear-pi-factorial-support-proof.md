---
rg: 2
id: minimal-multilinear-pi-factorial-support-proof
kind: route
title: Apply minimal-identity uniqueness and the prefix-free Fock Gram table
target: minimal-multilinear-pi-has-full-factorial-support
requires:
  - one-sided-amitsur-oracle-has-bounded-fock-model
---

The minimal-identity theorem quoted in the target gives `(MFS2)` immediately,
and counting the `m!` nonzero coefficients gives `(MFS3)`.

For the operator normalization, use the prefix-free words from
`one-sided-amitsur-oracle-has-bounded-fock-model`.  If `V_sigma` denotes the
left creation operator associated to the concatenated word indexed by
`sigma`, prefix incomparability gives

```text
V_sigma^* V_tau=delta_(sigma,tau) I.
```

Hence

```text
f(W)^*f(W)
 =sum_(sigma,tau) conjugate(c_sigma)c_tau V_sigma^*V_tau
 =sum_sigma |c_sigma|^2 I
 =N|c|^2 I,
```

which is `(MFS4)`.  Unit Fock norm then gives `(MFS5)`.  Since every direct
coefficientwise telescope has total absolute coefficient mass `||c_.||_1`,
its normalized bound has factor `sqrt(N)`.  Uniqueness shows this is shared by
every nonzero degree-minimal multilinear identity, rather than being an
artifact of a particular formula for the standard polynomial.

