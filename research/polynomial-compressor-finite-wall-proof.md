---
rg: 2
id: polynomial-compressor-finite-wall-proof
kind: route
title: Evaluate the polynomial compressor on three Boolean points and count regular commutants
target: polynomial-compressor-has-explicit-finite-quotient-wall
requires:
  - circulated-criterion-condition-iii-locus
artifacts:
  - experiments/polynomial_compressor_finite_wall.py
---

On monomials, the ring map sends

```text
x^i y^j -> x^(i+j)y^j,
```

so it is injective. Entrywise application is therefore injective on the
matrix group. Property `(T)` is the established Ershov--Jaikin input for this
same group and compressor.

The three quotient points are exactly the solutions of
`x^2=x,y^2=y,xy=0`. A polynomial with evaluation triple `(a,b,c)` is sent by
`y->xy` to `(a,b,a)`: the first two points have `y=0`, while `(0,1)` is sent
to `(0,0)`. Elementary groups commute with finite products, giving `(PFW2)`.
The order formula

```text
|SL_3(F_2)|=|GL_3(F_2)|=(8-1)(8-2)(8-4)=168
```

gives the index.

Finally, restricting `lambda_B` to `A` gives `[B:A]` copies of the regular
`A`-module. The commutant of `r` regular copies of `A` has dimension
`r^2|A|=r|B|`, whereas the `B` commutant has dimension `|B|`. Since
`A<=B`, the latter commutant is contained in the former, so their Reynolds
projection difference has the rank and normalized density in `(PFW3)--(PFW4)`.
