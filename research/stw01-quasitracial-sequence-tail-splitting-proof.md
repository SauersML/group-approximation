---
rg: 2
id: stw01-quasitracial-sequence-tail-splitting-proof
kind: route
title: Make the asymptotic cut an exact central projection in the quasitracial sequence quotient
target: stw01-asymptotic-quasitracial-cuts-promote-linearity
requires: []
artifacts:
  - research/artifacts/stw01-asymptotic-quasitracial-cut-audit-2026-08-30.md
---

Fix a free ultrafilter `omega`.  On `ell_infinity(A)` define the coordinate
ultralimit bounded `2`-quasitrace

```text
tau_omega((x_n))=lim_(n->omega) tau(x_n),
```

together with its coordinatewise `M_2` extension.  Its square-null set

```text
N_omega={x:tau_omega(x*x)=0}
```

is a closed two-sided ideal.  Let

```text
C=ell_infinity(A)/N_omega,
```

write `hat_tau_omega` for the induced quasitrace, and let
`iota:A->C` be the constant-sequence homomorphism.

Let `q` be the class of `(e_n)`.  Condition `(AQC1)` says `q=q^2`, while
positivity of the `e_n` gives `q=q*`.  Condition `(AQC2)` says

```text
[q,iota(a)]=0                           (a in A).
```

Thus `q` is a projection central relative to the constant copy of `A`.
The two maps

```text
theta_0(a)=q iota(a),
theta_1(a)=(1-q)iota(a)
```

are star homomorphisms from `A` into the two orthogonal corners of `C`.

The tail functional

```text
sigma=hat_tau_omega o theta_1
```

is therefore a bounded `2`-quasitrace on `A`.  If `i in I`, then

```text
||(1-e_n)i|| -> 0,
```

so `theta_1(i)=0`.  Hence `theta_1`, and therefore `sigma`, factors through
`A/I`.  The quotient hypothesis makes `sigma` a trace.

It remains to show that the head functional is linear.  For `a in A`,
projection centrality gives

```text
hat_tau_omega(q iota(a))
 =hat_tau_omega(q iota(a)q)
 =lim_(n->omega) tau(e_n a e_n).                         (AQS1)
```

For each `n`, the map

```text
a |-> tau(e_n a e_n)
```

is linear: its arguments lie in `Her_A(e_n)`, and the restriction of `tau`
to that hereditary algebra is a trace by hypothesis.  The scalar
ultralimit in `(AQS1)` is consequently a linear functional; call it `rho`.

For self-adjoint `a`, the two elements `q iota(a)` and
`(1-q)iota(a)` are orthogonal commuting self-adjoints.  Quasitrace
additivity in `C` gives the exact defect decomposition

```text
tau(a)=rho(a)+sigma(a).                                    (AQS2)
```

Both terms on the right are linear.  Therefore `tau` is additive on all
self-adjoint pairs and hence is a trace.

The escape alternative is the contrapositive: if `tau` is nontracial, at
least one of `(AQC1)` and `(AQC2)` fails.  Since their terms are
nonnegative, failure of convergence to zero is exactly a positive limsup.

**Trust boundary.**  The sequence quotient is formed from the square-null
ideal of the coordinate ultralimit quasitrace, not from a presumed norm
ultrapower trace.  Centrality is asserted only relative to `iota(A)`, which
is exactly what makes `theta_0` and `theta_1` homomorphisms.  The ambient
`tau` is never descended to `A/I`; only the tail `sigma` is.
