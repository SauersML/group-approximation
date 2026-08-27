---
rg: 2
id: tensor-independent-child-carrier-gap-proof
kind: route
title: Orthogonality of the two centered conditional-expectation ranges
target: tensor-independent-child-carrier-gap
requires: []
---

Let `E_A,E_B` be the trace-preserving conditional expectations and put

```text
y = F-c 1,
a = E_A(F)-c 1 = E_A(y),
b = E_B(F)-c 1 = E_B(y).
```

The centered spaces `L2(A) minus C1` and `L2(B) minus C1` are orthogonal.
Indeed, for centered `a_0 in A` and `b_0 in B`, trace independence gives

```text
< a_0,b_0 > = tau(a_0^* b_0)
            = tau(a_0^*) tau(b_0) = 0.
```

Thus `a` and `b` are orthogonal projections of the same vector `y` onto two
orthogonal closed subspaces.  Bessel therefore gives

```text
||a||_2^2 + ||b||_2^2 <= ||y||_2^2.
```

Because conditional expectation is the orthogonal projection in `L2`,

```text
dist_2(F,A)^2 = ||F-E_A(F)||_2^2
              = ||y||_2^2-||a||_2^2,

dist_2(F,B)^2 = ||y||_2^2-||b||_2^2.
```

Adding and using Bessel yields

```text
dist_2(F,A)^2+dist_2(F,B)^2 >= ||y||_2^2.
```

Finally `F` is a projection, so

```text
||F-c1||_2^2 = tau(F)-tau(F)^2 = c(1-c).
```

This proves the claim.  In `M_N tensor M_N`, the two tensor factors satisfy
trace independence exactly, so the stated rectangular-escape consequence is
immediate.  The same proof is stable under `o(1)` violations of independence:
all that changes is the Bessel inequality by the corresponding angle/error
term, while the fixed carrier variance `c(1-c)` stays bounded away from zero.
