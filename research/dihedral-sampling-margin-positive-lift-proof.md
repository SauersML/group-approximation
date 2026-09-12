---
rg: 2
id: dihedral-sampling-margin-positive-lift-proof
kind: route
title: Compare the continuous minimum with the nearest rotation sample
target: dihedral-sampling-margin-makes-positive-lift-trivial
requires:
  - moving-dihedral-quotients-force-linear-positive-lift-extent
  - sl2z-central-split-inherits-operator-fejer-riesz
---

Write the rotation evaluation of (DSM1) as

```text
p(theta)=sum_(k=-d)^d P_k exp(i k theta).               (DSP1)
```

In the left regular representation of `H_N`, the unitary `q_N(w)` has
all `N`th roots of unity in its spectrum. Therefore (DSM2) implies

```text
p(2 pi j/N)>=mu I_E,       0<=j<N.                     (DSP2)
```

Let

```text
m=min_(theta in R) lambda_min(p(theta)).
```

Finite dimensionality and continuity give a point `theta_0` and a unit
vector `xi in E` with

```text
<p(theta_0)xi,xi>=m.
```

The scalar function

```text
f(theta)=<p(theta)xi,xi>
```

has a global minimum at `theta_0`: for every `theta`,

```text
f(theta)>=lambda_min(p(theta))>=m=f(theta_0).          (DSP3)
```

Hence `f'(theta_0)=0`. Differentiating (DSP1) twice gives

```text
||p''(theta)||
 <=sum_k k^2 ||P_k||
 =K_2(p).                                               (DSP4)
```

Choose a sample point `theta_j=2 pi j/N` at circular distance at most
`pi/N` from `theta_0`. Taylor's theorem, (DSP3)--(DSP4), and (DSP2) give

```text
mu
 <=f(theta_j)
 <=f(theta_0)+(1/2)K_2(p)(pi/N)^2
 =m+pi^2 K_2(p)/(2N^2).                                (DSP5)
```

Rearranging proves

```text
m>=mu-pi^2 K_2(p)/(2N^2).                              (DSP6)
```

This is the pointwise operator inequality (DSM3) for every point of the
circle.

The rotation subgroup `<w>` of `C2*C2` is infinite cyclic. Its full
group C-star algebra embeds order-isomorphically into `C*(W)`; equivalently,
representations of the subgroup can be induced to `W`. Thus positivity of
the matrix-valued function (DSP1) on the entire circle is exactly
positivity of this element after placing it in `B(E) tensor C*(W)`.
Condition (DSM4) therefore makes the original representative a positive
lift.

Finally, `u_w^k` is a reduced word of syllable length `2|k|`, so the
extent of `p` is at most `2d`. Theorem B of
Jindal--Klep--McCullough applied to `W=C2*C2` gives a sum of hermitian
squares whose factors have extent at most

```text
floor((2d)/2)+1=d+1.
```

This proves all assertions.
