---
rg: 2
id: stw22-trace-problem-counterexample-from-chern-corona
kind: route
title: Put the Chern obstructions in a 2-null corona and separate by Cuntz-Pedersen traces
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

Let `I=direct_sum_s D_s`, viewed as the norm-`c_0` ideal in `M`, and put
`H=M/I`. The sequence `h=(h_s)` belongs to `J`, because its uniform
`2`-norm tends to zero blockwise, but `||h_s||=1`, so its class
`hbar=h+I` is nonzero and `||hbar||=1`.

Fix a finite number `ell` and lift arbitrary `y_1,...,y_ell in H` to
`m_j=lambda_j 1+z_j` with `z_j in J`. Scalars disappear from
self-commutators. For a bounded sequence `x=(x_s)`, quotienting by the
`c_0` ideal gives

```text
||x+I|| = limsup_s ||x_s||.
```

Every tail index `s>=ell` therefore satisfies the Chern estimate from the
prerequisite, and hence

```text
|| hbar - sum_(j=1)^ell (y_j^*y_j-y_j y_j^*) || >= 1.   (TC-1)
```

Thus `hbar` is not in the norm-closed selfadjoint commutator subspace.
By the Cuntz--Pedersen trace-separation theorem (equivalently Hahn--Banach
followed by polarization), there is a nonzero bounded hermitian tracial
functional on `H` detecting `hbar`. The positive and negative parts of a
hermitian trace are again traces (use uniqueness of Jordan decomposition
and invariance under inner automorphisms), so after normalization there is
`sigma in T(H)` with `sigma(hbar)!=0`.

Let `pi:M->H` be the quotient map. Then `sigma*pi` is a tracial state on
`M`. Since `A=C1+I`, its restriction to `A` is exactly the scalar quotient
trace `tau_infinity(lambda 1+a)=lambda`.

For `N>=1`, let `h^(N)` be the tail sequence equal to zero for `s<N` and to
`h_s` for `s>=N`. Then `pi(h^(N))=hbar`, so

```text
(sigma*pi)(h^(N)) = sigma(hbar) != 0
```

for every `N`, while

```text
||h^(N)||_(2,T(A)) = sup_(s>=N) sqrt(2/(s+1)) -> 0.
```

Therefore `sigma*pi` is not uniform-`2`-norm continuous. It is a second
extension of `tau_infinity` to `M`, proving `(XXII-NEG)`.
