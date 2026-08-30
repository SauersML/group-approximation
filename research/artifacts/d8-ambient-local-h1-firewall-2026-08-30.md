# D8 ambient/local H1 firewall (2026-08-30)

## Result

A cocycle can be arbitrarily short and ambiently trivial while remaining
nontrivial in the short-edge coefficient group; every ambient trivializer can
stay a fixed geometric distance from the identity.

## Algebraic model

Take

```text
B=D8=<r,s | r^4=s^2=1, srs=r^(-1)>,
A=<r^2,s> ~= C2 x C2,
Q=C2=<q>,    alpha_q=Ad(s),
z(q)=r^2.
```

The action on `A` is trivial, so `[z] != 1` in `H^1(Q,A)`.  However

```text
z(q)=r^(-1) alpha_q(r),
```

so `[z]=1` in `H^1(Q,B)`.

The complete set of ambient trivializers is

```text
{r,r^3,rs,r^3s}.
```

## Four-point spherical realization

Use `r=(0 1 2 3)`, `s=(1 3)` and

```text
x_0=cos(theta)e_1+sin(theta)e_3,
x_2=cos(theta)e_1-sin(theta)e_3,
x_1=cos(theta)e_2+sin(theta)e_4,
x_3=cos(theta)e_2-sin(theta)e_4.
```

Every element of `A` has displacement at most `2 sin(theta)`.  Every
ambient trivializer exchanges the two orthogonal clusters and has displacement
`sqrt(2)`.

## Graph consequence

The argument in `torsor-h1-vanishing-gives-spherical-gauge` establishes only
ambient compatibility of the permutation-table defects.  It does not establish
triviality of their class in the short-edge coefficient system, which is the
premise required by `short-edge-gauge-torsor-h1-vanishes`.

This example is not an actual regular-character multiplication-table
counterexample.  It proves that the current consumer route is missing a
special regular-table local-cohomology theorem.
