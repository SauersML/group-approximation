---
rg: 2
id: stw22-projective-bundle-corona-counterexample-proof
kind: route
title: Combine vanishing rank fraction with simultaneous Chern zeros and state compactness
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

The load-bearing Chern estimate is simultaneous.  Write
`E_s=1 + L_s^{+s}` and

```text
z_j = [ a_j  b_j ]
      [ c_j  d_j ].
```

Apply the Chern argument to the lower-left columns of `z_j` and `z_j^*`,
namely

```text
c_1,...,c_ell,b_1^*,...,b_ell^*.
```

Their join is a section of `L_s^{+(2 s ell)}`.  Whenever `s>=2 ell`, its top
Chern class is `c_1(L_s)^(2 s ell)!=0`, because `2 s ell<=s^2`.  Hence there
is a point `x` where both `b_j(x)=0` and `c_j(x)=0` for every `j`.  The vector
state on the trivial line at this fibre satisfies

```text
omega_(s,x)(h_s)=1,
omega_(s,x)(z_j z_k)=omega_(s,x)(z_j)omega_(s,x)(z_k)
                                           for every j,k.  (XXII-2)
```

Indeed, the trivial line reduces every `z_j(x)`, so the compressed scalar of
a product is the product of the compressed scalars.  This simultaneous-zero
estimate produces finite packets of an eventual character, not merely a
trace.

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

The original ideal `B=direct_sum_s D_s` sits in `J`, and `h=(h_s)` belongs to
`J` by (XXII-1).  Work first on the bounded product `P=product_s D_s`.  For
every finite family `z_1,...,z_ell in P` and every lower bound `S`, choose
`s>=max(S,2 ell)` and apply (XXII-2) to the coordinate family
`z_(1,s),...,z_(ell,s)`.  Pulling the resulting fibre vector state back along
the `s`-th coordinate evaluation gives a state `omega` on `P` with

```text
omega(h)=1,
omega(z_j z_k)=omega(z_j)omega(z_k)     for every j,k.  (XXII-4)
```

It also makes any prescribed finite family from `B` arbitrarily small:
choose `s` farther out, where those norm-null sequences have small
coordinates.

Now use compactness of the state space of `P`.  For finitely many
multiplicativity constraints, finitely many `a in B`, and an integer `r>=1`,
impose the closed conditions

```text
omega(h)=1,
omega(xy)=omega(x)omega(y),
|omega(a)|<=1/r.
```

For each finite collection, include every left and right factor in the Chern
packet before choosing the late coordinate.  The conditions are weak-star
closed (the product is in `C`), so the late-coordinate construction proves
the finite intersection property.  Compactness gives a state `rho`
satisfying all such conditions simultaneously.  Thus `rho` is multiplicative
on `P`, while the constraints for every `r` give `rho|_B=0`.  It descends to
a character of the corona `P/B`, and its restriction to `M=C1+J` is a
character, hence a tracial state, `sigma_tilde` with

```text
sigma_tilde(h)=1,
sigma_tilde(lambda 1+b)=lambda          (b in B).       (XXII-5)
```

Hence its restriction to `A=C1+B` is exactly the trace `tau_infinity` at the
point at infinity, whereas the uniform-`2`-continuous extension of
`tau_infinity` vanishes on `J`.  More explicitly, the tail representatives

```text
h^(n)=(0,...,0,h_n,h_(n+1),...)
```

have `h-h^(n) in B`, so

```text
sigma_tilde(h^(n)) = 1,
||h^(n)||_(2,T(A)) = sup_(s>=n) sqrt(2/(s+1)) -> 0.
```

Hence `sigma_tilde` is not uniform-`2`-norm continuous and the canonical
embedding `T(A) -> T(M)` is proper.  This refutes Problem XXII.
