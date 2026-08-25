---
rg: 2
id: finite-invariant-partition-only-reduces-irs-to-fiber-irs
kind: claim
title: A finite invariant partition reduces a non-CE stabilizer character to a finite-index fiber IRS, not automatically to a group
distinct_from:
  atomic-noncohyperlinear-irs-forces-nonhyperlinear: that assumes the subgroup-valued stabilizer map itself has an atom and obtains a regular quotient character; this assumes only a finite orbit of an auxiliary readable partition and generally retains a nontrivial fiber IRS.
  bcv-halt-readable-finite-orbit-does-not-transfer-to-gap-irs: that audits where BCV supplies finite readable orbits; this computes exactly what such an orbit would yield even if it were proved for the perfect gap witness.
  finite-depth-readable-groupoid-closes-iff-full-orbit-is-finite: that characterizes closure of the finite readable diagonal; this identifies the tracial algebra remaining in one object corner after closure.
---

Let a countable group `Gamma` act pmp on `(X,mu)`, and let

```text
phi(g)=mu(Fix_X(g))
```

be its stabilizer character.  Suppose `D subset L^infinity(X)` is a finite
dimensional `Gamma`-invariant Boolean algebra.  If `phi` is not Connes
embeddable, then one orbit of positive-measure atoms of `D` has the following
property.  For an atom `Y` in that orbit, put

```text
Delta={g in Gamma:gY=Y},
psi(h)=mu(Y intersect Fix_X(h))/mu(Y),  h in Delta.       (FIP1)
```

Then `[Gamma:Delta]<infinity`, `psi` is the stabilizer character of the
restricted pmp action `Delta curvearrowright (Y,mu_Y)`, and `psi` is not
Connes embeddable.  The character of `Gamma` on the invariant union of the
orbit is exactly the normalized finite-index induction of `psi`.

Consequently a finite orbit of the readable algebra in a ZPC-IRS model is a
valid finite-index reduction, but it is not by itself a regularization.  It
produces another non-co-hyperlinear IRS on the finite-index stabilizer
`Delta`.  It produces a non-hyperlinear group only with the additional fiber
condition

```text
psi=1_K for some K normal in Delta,                       (FIP2)
```

equivalently, the restricted action of `Delta/K` on `Y` is essentially free.
Then `L(Delta/K)` is the GNS algebra of `psi` and is non-CE.

This separates two notions that can look identical in a finite groupoid
picture.  An atom of the IRS measure is terminal by
`atomic-noncohyperlinear-irs-forces-nonhyperlinear`; an atom of a normalized
readable diagonal is merely a base set on which the isotropy group can still
have a genuinely random stabilizer.  Compressing to that object corner keeps
the bad trace, but generally keeps it as an IRS trace rather than the
canonical trace of the isotropy group.

For the perfect ZPC gap, the witness may be chosen ergodic: perfect value and
all ZPC structural equations are probability-one conditions, so they hold on
almost every ergodic component, while quantum soundness excludes a CE
component of value one.  Hence, if a finite full readable translate algebra
were proved for that witness, its positive atoms would form one transitive
orbit and `(FIP1)` would apply directly.  A further fiber-freeness or
normal-Dirac theorem would still be necessary.
