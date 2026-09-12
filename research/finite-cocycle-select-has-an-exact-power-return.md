---
rg: 2
id: finite-cocycle-select-has-an-exact-power-return
kind: claim
title: The finite-cocycle SELECT controller has an exact second-power return
distinct_from:
  finite-cocycle-select-forces-one-common-lcu-gauge: that synchronizes every coordinate orientation to one right gauge and therefore preserves one compressed zero or Hilbert--Schmidt norm test; this proves that the same construction does not preserve compressed powers.
  fixed-depth-strict-contractions-have-dilution-escape: that constructs arbitrary finite moment matches after paying small head density; this gives an exact hostile representation of the proposed positive-density finite-cocycle controller itself.
  canonical-positive-density-no-return-dilation-tail: that asks for one game-coupled colligation with no return through a prescribed depth; this rules out using finite-cocycle SELECT as that colligation without an additional tail relation.
---

**ESTABLISHED BOUNDARY.**  A common right gauge is harmless for one LCU
compression, but it is not harmless for compressed powers.  Already for
`K=C_2={1,s}`, the exact finite-cocycle SELECT relations admit a marked
natural-packet representation in which

```text
qCq=0,                    qC^2q=q.                    (FPR1)
```

Consequently

```text
qC^2q != (qCq)^2.                                  (FPR2)
```

The failure has full normalized Hilbert--Schmidt mass in the selected
corner, so it cannot disappear under packet exactification or amplification.
In particular, the relations proving
`finite-cocycle-select-forces-one-common-lcu-gauge` do not imply even the
`n=2` case of the coherent-power condition in
`canonical-positive-density-no-return-dilation-tail`.

There is a stronger projection-or-return dichotomy.  Because
`g |-> w_g` is a representation of the finite group `K`, its uniform average

```text
P=|K|^(-1)sum_(g in K)w_g
```

is the orthogonal projection onto the invariant vectors.  Hence the selected
first compression `qCq=PA` has operator norm either zero or one; it can never
be a nonzero strict contraction.  In the zero branch, specialize the free
common gauge to `A=I` and let `r` be the exponent of `K`.  Then every diagonal
block `w_x` has `r`-th power one, so

```text
qCq=0,                    qC^r q=q.                    (FPR2K)
```

Thus finite-cocycle SELECT can groupify a one-shot projection/zero test, as
claimed, but its own homomorphism law prevents it from being the strict
contraction or the no-return tail used by the power-capacity route.

More generally, let `chi:K -> U(1)` be a nontrivial character of finite order
`r`, and use the scalar payload representation `w_x=chi(x)I` and the allowed
common gauge `A=I`.  On the natural packet,

```text
C=diag(chi(x)I : x in K),
qCq=|K|^(-1) sum_x chi(x)=0,
qC^r q=q.                                             (FPR3)
```

Thus every such finite character controller has an exact return at its
character order.  A power-return construction must couple the exit to a new
nonperiodic, game-dependent tail and constrain its multiplicity action.  A
finite transitive controller orbit and its common-gauge theorem alone cannot
provide that coupling.

## Scope

This is not a no-go for every ordinary-group colligation.  It isolates the
precise extra datum one would need to escape: relations that prevent the
allowed `A=I` finite-image specialization `(FPR2K)` while retaining the HALT
perfect carrier, and a game-dependent word list which is not reduced to a
finite-group average projection.  Such relations cannot be consequences
only of the finite lamp packet, shift covariance, and the cocycle law,
because `(FPR2K)` and `(FPR3)` are exact representations of all of them.
