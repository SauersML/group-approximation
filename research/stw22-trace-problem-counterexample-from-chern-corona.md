---
rg: 2
id: stw22-trace-problem-counterexample-from-chern-corona
kind: route
title: Put simultaneous Chern zeros in a 2-null corona and compactify coordinate states
target: stw22-nuclear-typei-trace-problem-counterexample
requires:
  - stw22-chern-l2-small-unbounded-commutator-width
artifacts:
  - research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md
---

For the blocks `D_s` and elements `h_s` from the prerequisite, set

```text
B = direct_sum_(s>=1) D_s,
A = unitization(B).
```

This is separable, unital, nuclear and type I. Its uniform tracial
completion is

```text
M = C 1 + J,
J = {(x_s) in product_s D_s:
     sup_s ||x_s|| < infinity and ||x_s||_(2,T(D_s)) -> 0}.
```

Indeed a uniform-`2` Cauchy bounded sequence converges in each fixed block
(the norm and normalized `2`-norm are equivalent there), and the tail
condition is exactly what is left from approximating by the `c_0` sum.
Conversely truncation proves every element of `C1+J` lies in the completion.

Let `I=direct_sum_s D_s`, viewed as the norm-`c_0` ideal.  The sequence
`h=(h_s)` belongs to `J`, because its uniform `2`-norm tends to zero
blockwise.

The one-sided Chern width estimate from the prerequisite is not, by itself,
a positive-state construction: after only the lower-left columns vanish, the
trivial-line vector state evaluates a self-commutator as `-b b^*`.  Strengthen
the same Chern argument by joining both the lower-left columns of the chosen
elements and those of their adjoints.  This is a section of
`L_s^{+(2 s ell)}`, whose top Chern class is nonzero when `s>=2 ell`.  At a
common zero both off-diagonal blocks vanish, so the trivial-line fibre vector
state `omega_s` satisfies

```text
omega_s(h_s)=1,
omega_s(z_j^*z_j-z_jz_j^*)=0            for j=1,...,ell. (TC-1)
```

For any finite family of product elements and any prescribed tail, choose
such a later coordinate and pull `omega_s` back to the bounded product.  A
finite family from `I` is simultaneously small there because its coordinate
norms tend to zero.

The state space of the bounded product is compact.  Impose all closed
constraints `omega(h)=1`, all self-commutator constraints, and, for every
`a in I` and integer `r>=1`, `|omega(a)|<=1/r`.  The late-coordinate states
give the finite intersection property, so compactness produces a state `rho`
satisfying every constraint.  Polarization makes `rho` tracial, and the
`1/r` constraints give `rho|_I=0`.  Therefore `rho` descends to the norm
corona and restricts to a tracial state on `M=C1+J` with

```text
rho(h)=1,
rho(lambda 1+a)=lambda                  for a in I.      (TC-2)
```

Thus its restriction to `A` is exactly the scalar quotient trace
`tau_infinity(lambda 1+a)=lambda`.

For `N>=1`, let `h^(N)` be the tail sequence equal to zero for `s<N` and to
`h_s` for `s>=N`. Then `h-h^(N) in I`, so

```text
rho(h^(N)) = 1
```

for every `N`, while

```text
||h^(N)||_(2,T(A)) = sup_(s>=N) sqrt(2/(s+1)) -> 0.
```

Therefore `rho` is not uniform-`2`-norm continuous. It is a second
extension of `tau_infinity` to `M`, proving `(XXII-NEG)`.
