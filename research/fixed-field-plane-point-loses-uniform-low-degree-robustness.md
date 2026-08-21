---
rg: 2
id: fixed-field-plane-point-loses-uniform-low-degree-robustness
kind: claim
title: Fixing the field does not make the Natarajan--Vidick plane-point test a uniform finite template
distinct_from:
  quantum-low-degree-is-a-non-equality-pauli-synchronizer: that imports the positive same-Hilbert soundness theorem; this audits the parameter specialization needed by a finite-template occurrence compiler.
---

ESTABLISHED.  In the Natarajan--Vidick quantum low-degree test let `h^m>=n` and
`d=hm`.  The soundness error in their Theorem 3.2 contains a polynomial in
`d/q`.  Hence a uniform nonzero robustness modulus requires `d/q` bounded
by a sufficiently small absolute constant.  Since `m->infinity` is needed
to encode unbounded `n`, no fixed field size `q` can satisfy this condition
for fixed positive `h`.

This dependence also reflects the underlying code geometry.  The tensor
Reed--Solomon evaluation code of individual degree at most `h<q` in `m`
variables has relative distance

```text
((q-h)/q)^m.                                                    (FF1)
```

For fixed `q,h>0` this tends to zero.  Thus the fixed-field point-plane
encoding does not have a constant relative-distance reservoir from which the
published uniform agreement estimate could follow.

The standard robust choice instead takes

```text
m = Theta(log(n)/log log(n)),
h = Theta(log(n)),
d = Theta(log(n)^2/log log(n)),
q = Omega(d).                                                   (FF2)
```

Accordingly both the field alphabet and the answer packet grow.  Before
composition a plane answer ranges over degree-`d` bivariate polynomials; the
composed theorem still has answer length

```text
O(log(q) log(d)^2).                                             (FF3)
```

It is therefore incorrect to cite arXiv:1801.03821 as already supplying a
fixed-field, constant-answer-alphabet occurrence game with uniform
robustness.  A further constant-alphabet agreement/PCP composition is a
load-bearing step.
