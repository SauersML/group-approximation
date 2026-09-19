---
rg: 2
id: stw63-free-product-mixing-kills-implementer-clusters
kind: route
title: Use Haar-power mixing to kill every free-factor intertwiner and every conjugator cluster point
target: stw63-canonical-free-product-implementers-escape-weakly
requires: []
artifacts:
  - research/artifacts/stw63-z-embedding-audit-2026-08-30.md
---

We first prove that the free factors have no nonzero bounded intertwiner:

```text
{x in M : x a = alpha(a)x for every a in M_0}={0}.       (WFE3)
```

Choose a Haar unitary `h in M_0`; then `k=alpha(h)` is a Haar unitary in
`M_1`.  If `x` belongs to the set in `(WFE3)`, then

```text
x h^m = k^m x                                             (m in Z).  (WFE4)
```

Approximate `x` in `2`-norm by a finite linear combination `y` of reduced
free-product words.  The reduced-word rules give

```text
tau(h^(-m) y* k^m y) -> 0.                               (WFE5)
```

Indeed, after expanding `y`, every summand is an alternating word.  Except
for possible cancellations at its two ends it is immediately centered by
freeness.  The remaining end cancellations are scalar coefficients of
`h^m` or `k^m` against fixed `L^2` letters, and tend to zero because the
powers of a Haar unitary form an orthonormal sequence in `L^2`.
Consequently

```text
||y h^m-k^m y||_2^2
 =2||y||_2^2-2 Re tau(h^(-m)y*k^m y)
 -> 2||y||_2^2.                                          (WFE6)
```

On the other hand `(WFE4)` gives, for every `m`,

```text
||y h^m-k^m y||_2 <= 2||x-y||_2.                         (WFE7)
```

If `x` were nonzero, choose `y` so close to `x` that
`sqrt(2)||y||_2>2||x-y||_2`.  Equations `(WFE6)` and `(WFE7)` contradict
one another.  This proves `(WFE3)`.

Now let `(u_n)` satisfy `(WFE1)`.  Equivalently,

```text
||u_n theta(i_0(z))-theta(i_1(z))u_n|| -> 0             (z in Z). (WFE8)
```

The unit ball of `M` is ultraweakly compact.  If `x` is an ultraweak cluster
point of `(u_n)`, `(WFE8)` gives

```text
x theta(i_0(z))=theta(i_1(z))x                           (z in Z).
```

The two copies of `Z` are strongly dense in `M_0,M_1`, and multiplication by
the fixed bounded element `x` is strongly continuous on bounded sets.
Therefore `x a=alpha(a)x` for every `a in M_0`.  By `(WFE3)`, `x=0`.
Every ultraweak cluster point is thus zero; compactness implies `(WFE2)`.

An exact conjugating unitary would itself be a nonzero element of `(WFE3)`,
so exact conjugacy is impossible.

For the quantitative statement, fix `varphi in M_*` and `delta>0`.  If no
finite set and tolerance worked, use a nested sequence of finite sets with
dense union in the unit ball of `Z` and tolerance `1/n` to choose unitaries
`u_n` whose conjugacy errors tend to zero pointwise while
`|varphi(u_n)|>=delta`.  The already proved ultraweak convergence
`u_n->0` contradicts normality of `varphi`.

**Norm boundary.**  Ultraweak escape does not give a point-norm lower bound:
the unitary group has zero in its ultraweak closure, and finite-factor
uniqueness produces implementing sequences in `M` which necessarily have
exactly this escape behavior.  No inference about the full-free-product
orbit distance `Delta` is made.
