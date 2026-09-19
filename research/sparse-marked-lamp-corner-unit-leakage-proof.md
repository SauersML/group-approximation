---
rg: 2
id: sparse-marked-lamp-corner-unit-leakage-proof
kind: route
title: Delete one escaping marker from each of three quotient fibers
target: sparse-marked-lamp-corner-has-unit-relative-leakage
requires: []
---

Write the free group as `A=F(a,b)` and let

```text
q : A -> C_3,
q(a)=1,
q(b)=0.
```

For `y in C_3` put `F_y=q^(-1)(y)`.  Choose integers `N_n -> infinity` and

```text
r_(y,n)=b^(N_n) a^y,
E_(y,n)=F_y symmetric_difference {r_(y,n)}
       =F_y minus {r_(y,n)}.                                  (SLC4)
```

The second equality holds because `q(r_(y,n))=y`.  Let `chi_(y,n)` be the
lamp character whose support is `E_(y,n)`:

```text
chi_(y,n)(m)=(-1)^(|supp(m) intersect E_(y,n)|).
```

Take `d_n >= 3` with `d_n -> infinity`, let `P_(y,n)` be three mutually
orthogonal rank-one projections in `M_(d_n)`, and define

```text
rho_n(m)|_(P_(y,n)) = chi_(y,n)(m),
rho_n(m)|_(1-sum_y P_(y,n)) = 1.                               (SLC5)
```

This is an exact representation of the entire lamp group.  Define the exact
actor representation by

```text
U_n(g) P_(y,n) U_n(g)^* = P_(y+q(g),n)
```

and let it be the identity on the spectator corner.

## Pointwise covariance

For fixed `g in A`, the two supports

```text
g^(-1) E_(y,n)
and
E_(y-q(g),n)
```

have the same quotient fiber and differ only at the two possible markers
`g^(-1)r_(y,n)` and `r_(y-q(g),n)`.  Both words leave every fixed finite
subset of `A` as `N_n -> infinity`.  Therefore, for every fixed finitely
supported lamp `m`, the two characters agree on `m` for all large `n`.
Reading `(SLC5)` on each of the three active lines proves `(SLC1)`; it is
automatic on the spectator corner.

With the convention

```text
(m,g)(m',h)=(m+g.m',gh),
```

the maps `sigma_n(m,g)=rho_n(m)U_n(g)` are consequently pointwise
operator-norm asymptotic homomorphisms.  Notice that the errors are not merely
small: every fixed multiplication identity is exact from some coordinate
onward.

## The fixed sparse mark

The marker words eventually avoid `{e,a}`.  The two-point support of
`w=m_e m_a` meets `F_0` and `F_1` once each and misses `F_2`.  Hence

```text
chi_(0,n)(w)=chi_(1,n)(w)=-1,
chi_(2,n)(w)=1,
```

and therefore

```text
p_n=(1-rho_n(w))/2=P_(0,n)+P_(1,n).                            (SLC6)
```

Its rank is two at every coordinate.  Thus its corona class has norm one and
is nonzero, although its normalized traces tend to zero; equivalently its
integer rank germ is the nonzero constant germ `(2,2,...)`.  Equation
`rho_n(w)=1-2p_n` gives operator-norm distance two from the identity.

## Trivial stabilizers and the gap

Every `E_(y,n)` has trivial left stabilizer.  Indeed, if
`g E_(y,n)=E_(y,n)` and `q(g)=0`, then the common fiber `F_y` is fixed and
equality of the deleted singletons gives `g r_(y,n)=r_(y,n)`, hence `g=e` by
freeness of left translation.  If `q(g) != 0`, the two sides differ on two
distinct infinite quotient fibers outside at most two singleton points, so
they cannot be equal.

For completeness, the positive constant in `(SLC2)` needs no external
rigidity input.  Identify each character orbit with the four-regular Cayley
tree of `F(a,b)`.  Orient that tree toward one fixed end, so every vertex has
one incoming and three outgoing edges.  Applying

```text
2 |uv| <= (1/sqrt(3)) |u|^2 + sqrt(3) |v|^2
```

along the oriented edges gives operator norm at most `2 sqrt(3)` for the
adjacency sum `lambda(a)+lambda(a^(-1))+lambda(b)+lambda(b^(-1)`.  Expanding
the four squared differences yields `(SLC2)`.

## Maximal relative leakage

For a generator `s`, the prescribed translate of `chi_(y,n)` is supported on

```text
s E_(y,n)=F_(y+q(s)) minus {s r_(y,n)}.                         (SLC7)
```

The actor unitary instead carries `P_(y,n)` onto the atom supported on

```text
E_(y+q(s),n)=F_(y+q(s)) minus {r_(y+q(s),n)}.                  (SLC8)
```

These characters are distinct.  For `s=b^(+/-1)` this follows from
`b^(+/-1)r_(y,n) != r_(y,n)`.  For `s=a^(+/-1)` it follows from reduced free
group normal forms:

```text
a^(+/-1) b^(N_n) a^y != b^(N_n) a^(y+/-1 mod 3).
```

Moreover `(SLC7)` cannot equal an atom with any other quotient-fiber index.
Thus the target projection `P_(s chi_(y,n))` is zero in the finite joint PVM,
whereas `U_n(s)P_(y,n)U_n(s)^*=P_(y+q(s),n)`.  Each active rank-one atom leaks
its entire normalized trace.  Summing over `y=0,1` and using `(SLC6)` proves
`(SLC3)`.

The three full characters have trivial stabilizer, but their pointwise corona
limits forget the escaping deleted singleton and retain only the three fiber
characters.  That loss of the full label is exactly why the corona covariance
can be exact while the coordinatewise, corner-normalized character leakage
stays one.
