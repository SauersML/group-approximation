---
rg: 2
id: p3-exact-iwahori-endpoints-refute-arbitrary-baseline-alignment
kind: claim
title: Exact mod-three Iwahori endpoints refute arbitrary-baseline T-commutant alignment
distinct_from:
  same-core-involution-cubic-gauge-coercivity: that theorem collapses a gauge already commuting with the retained parabolic; this gives two exact endpoints over the same core whose relative gauge does not commute with it.
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: odd-congruence pairs remain uniformly repairable because one may choose the nearby endpoint; this refutes only the stronger strategy of comparing with an arbitrary preselected exact endpoint.
  relative-first-triangle-rounding-has-an-odd-root-branch-firewall: that is an asymptotic square-root loss caused by changing the core; this is a zero-defect finite quotient on one identical square-free core.
---

There is one square-free exact BS core `(R,T)` and two exact extending
involutions `X_0,X` such that

```text
X_i^2=1,       X_i R X_i=R^(-1),
(X_iT)^3=1,    (X_iT^2R)^3=1                         (P3A1)
```

for `i=0,1`, but the relative gauge

```text
c=X X_0
```

does not commute with `T`.  The example occurs in `PSL_2(F_3)` and remains
a positive-density zero-defect example in every amplification of its
regular representation.

Consequently there is no universal estimate of the form

```text
||[XX_0,T]||_2
 <= C * (the presentation defects of X and X_0)        (P3A2)
```

for two arbitrary exact endpoints over one common core.  In particular,
the second cubic does **not** by itself promote the automatically
`R`-central relative gauge into `{T}'`, even when both cubics and both
inversion rows hold exactly.

This does not refute the Iwahori repair theorem.  An exact input can choose
itself as the repaired endpoint, and
`odd-congruence-iwahori-pairs-have-uniform-linear-repair` already handles
authenticated odd-congruence pairs.  It does sharpen the basin target:
authentication must choose an endpoint in the input's correct endpoint
component (or minimize over all exact endpoints).  Finding merely one
canonical extender of a nearby `(R,T)` core and then invoking a universal
commutant-promotion inequality is false.

The degeneracy is sharply localized at field level.
`prime-field-iwahori-weyl-endpoint-is-unique-away-from-three` proves that on
the standard `PSL_2(k)` core in characteristic greater than three, inversion
puts every candidate in the Weyl normalizer coset and the first cubic makes
that Weyl element unique.  At characteristic three the dilation `h(2)` is
scalar in the projective group, which is exactly why the counterexample is
possible.
