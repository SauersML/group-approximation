---
rg: 2
id: atlas-a4-root-ellipse-exact-tracial-escape
kind: claim
title: The exact packet-collision zero set has root-ellipse value seventy-three in a finite factor
distinct_from:
  atlas-reference-packet-root-ellipse-countermodel: that is a finite-dimensional packet-only point at the same scalar value, but its collision word is nontrivial; the present model kills collision 19243 exactly and necessarily lives outside the matrix conclusion being sought.
  atlas-a4-four-cycle-dirichlet-compiler: that records the same quotient-trace construction only through the linear Dirichlet value E_T=4; this computes the nonlinear root ellipse exactly and applies it directly to the proposed 3/128 ceiling.
---

Put

```text
Gamma_A4=(A8*A8)/<<thirty A4 packet words,q_19243>>.
```

There is a finite tracial factor `(M,tau)` and a unitary `U in M` which gives
an exact regular A4 context network such that every packet word and
`q_19243` is exactly one, but

```text
Re tau(V_U(t))=0
```

for each of the four transvections

```text
t in {t01,t12,t23,t30}.
```

Consequently all four root deficits are one:

```text
x_01=x_12=x_23=x_30=1,
S=2x_01+2x_23+4x_30=8,
S^2+S x_12+x_12^2=73.                                (A4-TR-ELLIPSE)
```

Thus the exact packet-plus-collision relations do not imply the proposed
root-energy ceiling in the class of finite tracial von Neumann algebras.  In
particular no cyclic sum-of-squares certificate, trace-polynomial inequality,
or dimension-free argument valid in every finite tracial algebra can prove
`atlas-a4-root-energy-ellipse-ceiling`.

The remaining distinction is genuinely matrix-specific: proving the A4
ceiling means proving that this exact quotient trace is not Connes embeddable,
not optimizing a scalar consequence of the exact relations.

