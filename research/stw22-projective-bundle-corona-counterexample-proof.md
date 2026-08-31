---
rg: 2
id: stw22-projective-bundle-corona-counterexample-proof
kind: route
title: Combine vanishing rank fraction with unbounded Chern commutator width
target: stw22-nuclear-type-i-counterexample-trace-problem
requires: []
artifacts:
  - research/artifacts/stw22-trace-problem-counterexample-audit-2026-08-31.md
---

For `s>=1`, put `N_s=s^2`, let `L_s -> CP^(N_s)` be the tautological line
bundle, and set

```text
E_s = 1 + L_s^{+s},
D_s = Gamma(End(E_s)).
```

Let `p_s` be the projection onto the trivial summand and `q_s` the projection
onto the first copy of `L_s`; put `h_s=p_s-q_s`.  Every fibre of `D_s` is
`M_(s+1)`, so every trace on `D_s` vanishes on `h_s`, while

```text
||h_s|| = 1,
||h_s||_(2,T(D_s))^2 = 2/(s+1).                     (XXII-1)
```

The load-bearing estimate is

```text
inf_{z_1,...,z_ell in D_s}
 ||h_s - sum_(j<=ell) [z_j^*,z_j]|| >= 1
 whenever ell <= s.                                  (XXII-2)
```

Indeed, write `E_s=1 + L_s^{+s}` and

```text
z_j = [ a_j  b_j ]
      [ c_j  d_j ].
```

The tuple `(c_1,...,c_ell)` is a section of `L_s^{+(s ell)}`.  Since
`s ell <= s^2`, its top Chern class is

```text
c_(s ell)(L_s^{+(s ell)}) = c_1(L_s)^(s ell) != 0
```

in `H^(2 s ell)(CP^(s^2);Z)`.  Hence the tuple vanishes at some point `x`.
At that point the compression to the trivial line satisfies

```text
p_s [z_j^*,z_j](x) p_s = - b_j(x)b_j(x)^* <= 0,
```

whereas `p_s h_s(x) p_s=p_s(x)`.  This proves (XXII-2).

Now let

```text
B = direct_sum_s D_s,          A = unitization(B).
```

Then `A` is separable, unital, nuclear and type I.  Its extreme trace space is

```text
K = (disjoint_union_s CP^(s^2)) union {infinity},
```

the one-point compactification, and `T(A)=Prob(K)`.

Write `||.||_(2,s)` for the supremal normalized fibre `2`-norm on `D_s` and
put

```text
J = {(x_s) in product_s D_s : sup_s ||x_s|| < infinity,
                              ||x_s||_(2,s) -> 0}.
```

Direct truncation and coordinatewise completeness give the exact uniform
tracial completion

```text
M = overline(A)^{T(A)} = C 1 + J.                    (XXII-3)
```

The original ideal `B=direct_sum_s D_s` sits in `J`.  Set `H=M/B`.  By
(XXII-1), `h=(h_s)` belongs to `J`, while `||h_s||=1`, so its class `hbar` in
`H` is nonzero.  For every finite family `y_1,...,y_ell in H`, choose lifts
`lambda_j 1+z_j` with `z_j in J`.  Scalar parts cancel in self-commutators,
and the quotient norm is the tail limsup, hence (XXII-2) gives

```text
||hbar - sum_(j<=ell)[y_j^*,y_j]||
 = limsup_s ||h_s - sum_(j<=ell)[z_(j,s)^*,z_(j,s)]||
 >= 1.                                                (XXII-4)
```

Thus `hbar` is not in the Cuntz--Pedersen trace-zero subspace of `H`, the norm
closure of finite sums of self-commutators.  The Cuntz--Pedersen duality
between this quotient of `H_sa` and bounded self-adjoint tracial functionals
therefore yields a bounded trace detecting `hbar`.  Taking a Jordan component
and normalizing gives `sigma in T(H)` with `sigma(hbar) != 0`.

Pull `sigma` back along `M -> H`.  The resulting trace `sigma_tilde` kills
`B`, so on `A=C1+B` it is exactly the trace `tau_infinity` at the point at
infinity.  But `sigma_tilde(h) != 0`, whereas the uniform-`2`-continuous
extension of `tau_infinity` vanishes on `J`.  More explicitly, the tail
representatives

```text
h^(n)=(0,...,0,h_n,h_(n+1),...)
```

all have the same image `hbar` in `H`, so

```text
sigma_tilde(h^(n)) = sigma(hbar) != 0,
||h^(n)||_(2,T(A)) = sup_(s>=n) sqrt(2/(s+1)) -> 0.
```

Hence `sigma_tilde` is not uniform-`2`-norm continuous and the canonical
embedding `T(A) -> T(M)` is proper.  This refutes Problem XXII.
