---
rg: 2
id: agent-stw77-zero-type-i-weak-closure-obstruction-proof
kind: route
title: Use the canonical UHF core inside the Cuntz algebra
target: agent-stw77-zero-type-i-weak-closure-obstruction
requires: []
---

Let `B=O_2`, let `A=F_2` be its canonical gauge-fixed UHF algebra of type
`2^infinity`, and let `phi:F_2->O_2` be the inclusion.

Because `F_2` is AF, `id_(F_2)` has nuclear dimension zero.  Composing its
finite-dimensional approximations with `phi` shows

```text
dim_nuc(phi)=0.
```

The algebra `O_2` is simple and strongly purely infinite, so every nonzero
positive element of `phi(F_2)` is properly infinite in `O_2`.  Hence this
map satisfies all the hypotheses of the zero-color STW77 problem.

Let `omega` be the canonical gauge KMS state on `O_2`.  Its restriction to
`F_2` is the unique trace `tau` of the UHF algebra.  Therefore, in the GNS
representation `pi_omega`,

```text
pi_omega(phi(F_2))'' = R,
```

the hyperfinite type-II_1 factor.  In particular the weak closure generated
by the range is not type I, and its unit is finite.  Thus the image of the
unit, although properly infinite in `O_2`, is not properly infinite in
`pi_omega(F_2)''`.

The standard Cuntz-KMS factor computation gives
`pi_omega(O_2)''` as the hyperfinite type-III_(1/2) factor.  Hence the
ambient weak closure is not type I either.  Equivalently, `O_2**` cannot be
type I, since it has this non-type-I normal quotient.

For a convenient recorded source for both weak closures, see Conti--Lechner,
[*Yang--Baxter endomorphisms*](https://arxiv.org/abs/1909.04127), Section
2.2: for `O_d` the canonical KMS completion is type `III_(1/d)` and the
completion of its UHF core is type `II_1`.

This single zero-dimensional proper-image inclusion therefore blocks direct
application of the type-I theorem to either the bidual or these canonical
KMS weak closures.  It does not say that every representation of `O_2` has
non-type-I closure: a faithful irreducible representation has weak closure
`B(H)`, but absorption there still does not return central isometries to
`O_2` in norm.  The example does not challenge the STW77 conclusion:
the inclusion lands in `O_2` and is already O-infinity-stable.  It isolates
only the missing descent step from von Neumann absorption back to the
original norm-closed target.
