---
rg: 2
id: finite-packet-cannot-realize-absorbing-contraction
kind: claim
title: A finite packet cannot realize a complete absorbing contraction chain
distinct_from:
  finite-depth-contractive-computation-ladder: that proves a positive energy floor once the contraction hypotheses are available; this evaluates their zero-error form on the negative regular summand of a finite packet.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that gives the complete stationary vector for arbitrary restriction graphs; this is the direct constant-depth consequence for a proposed controlled nested reset chain.
  single-context-v4-exit-capacity-is-already-nonhyperlinearity: that treats approximate capacity in an infinite ambient group; this rules out obtaining the exact finite-depth input from one finite group table.
---

Let `H` be a finite group with a nontrivial central involution `J`.  Suppose a
proposed depth-`m` packet assigns nonnegative quantities `a_0,...,a_m` to
every finite-dimensional representation on which `J=-I`, and fixed constants
`a_*>0`, `A<infinity`, and `0<lambda<1` satisfy

```text
a_0>=a_*,             a_n<=lambda a_(n+1),             a_m<=A. (FPC1)
```

If `lambda^m A<a_*`, no such finite packet exists.

Indeed the negative central summand of the left regular representation,

```text
Q_J l2(H),              Q_J=(1-J)/2,                         (FPC2)
```

is a nonzero finite-dimensional representation of `H` on which `J=-I`.
Iterating `(FPC1)` on it gives

```text
a_*<=a_0<=lambda^m a_m<=lambda^m A<a_*,                       (FPC3)
```

a contradiction.

Consequently a two-level controlled block model and its local character
table may verify one ray calculation, but repeating it to the absorbing depth
cannot remain a universally sound theorem about representations of one fixed
finite group.  Any complete constant-depth Schur lift must use relations in
an infinite ambient group whose **joint approximate** finite-dimensional
models obey a nonlocal density inequality.  Producing that inequality is the
nonhyperlinearity mechanism; it is not reducible to finite character
enumeration.

