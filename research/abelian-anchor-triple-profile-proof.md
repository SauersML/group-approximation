---
rg: 2
id: abelian-anchor-triple-profile-proof
kind: route
title: Use a quadratic root-block norm profile and a positive-density character cut
target: one-abelian-anchor-and-label-expansion-round-a-normalizer
requires:
  - abelian-root-average-placement-rounds-its-normalizer
---

Write `B_(x,y)=||P_x V P_y||_F^2/m` and set

```text
f(x,y,z)=sqrt(B_(x,y)B_(x,z)/q)       for y!=z.
```

The row sums of `B` are one, so `(ARP2)` gives

```text
||f||_2^2=q^(-1)sum_x(1-sum_y B_(x,y)^2)=L(V).          (ATP1)
```

Conjugation by `D_s` permutes the block norms of `V`. The reverse triangle
inequality on each block therefore implies

```text
q^(-1)sum_(x,y)|sqrt(B_(x,y))-sqrt((s.B)_(x,y))|^2
 <= ||V-D_s V D_s^*||_2^2.
```

For each row, its square-root vector has Euclidean norm one. The map
`b -> b tensor b` has Lipschitz constant two on the unit sphere, by
`b tensor b-c tensor c=(b-c) tensor b+c tensor(b-c)`. Summing over rows
and then discarding the diagonal pairs `y=z` gives

```text
||f-s.f||_2 <= 2||[V,D_s]||_2.
```

Thus `(AEX1)` yields `||f-Pi f||_2<=2e/sqrt(kappa)`. This uses only
individual block covariances, not a representation formed by the `D_s`.

Let `chi(x)=exp(2 pi i h_0(x)/p)` and take

```text
C={(x,y,z) in Omega:chi(y)!=chi(z)}.
```

On every simultaneous `GL_n(F_p)` orbit, the map `(x,y,z)->y-z` is
equivariant onto all nonzero vectors and has equal-size fibers. Exactly
`p^(n-1)(p-1)` nonzero vectors have nonzero `h_0` value. Hence `C`
occupies proportion `theta` of each orbit.

The conditional-expectation formula in the preceding route gives the
exact anchor identity

```text
a^2=1-q^(-1)sum_x|sum_y B_(x,y)chi(y)|^2
   =(2q)^(-1)sum_(x,y,z)B_(x,y)B_(x,z)|chi(y)-chi(z)|^2.
```

Distinct `p`th roots have distance at least `gamma_p`, so
`||1_C f||_2<=sqrt(2)a/gamma_p`. Since `Pi f` is orbitwise constant,

```text
||Pi f||_2=theta^(-1/2)||1_C Pi f||_2
 <= theta^(-1/2)(sqrt(2)a/gamma_p+||f-Pi f||_2).
```

Add `||f-Pi f||_2`, use `(ATP1)`, and obtain `(AEX2)`. Applying `(ARP1)`
proves `(AEX3)`. No multiplication law, spectral gap, or scalar restriction
on the atom-dependent multiplicity twists was used.
