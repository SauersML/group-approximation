---
rg: 2
id: packet-covariant-kernel-gauge
kind: claim
title: Packet covariance leaves free-compressor gauges with vanishing kernel-fixed adjoint density
distinct_from:
  shared-bcs-carrier-localizes-free-compressor-quotient: that asks for a positive-density carrier on which the free kernel disappears and the named parent/child packet actions are recovered; this proves the sharp Schur normal form and gives canonical finite matrix gauges in which the kernel-fixed adjoint density tends to zero.
  hyperlinear-fiber-cannot-orient-btb-return: that gives a general spectator-amplification no-go conditional on an active multiplicity presentation having microstates; this computes the active presentation for the proposed packet-covariant free generators and supplies an explicit residually finite regular sequence with exact fixed-space density.
  packet-kazhdan-commutant-placement-decouples: that puts the whole predicate packet on an independent tensor factor from a compressor; this allows every free generator to implement exactly the same named packet automorphism as its prescribed finite quotient image and proves that the remaining gauge still defeats kernel localization.
---

**ESTABLISHED SCHUR-GAUGE COUNTERMODEL AND SHARP BOUNDARY.**  Let

```text
theta:F_r ->> B
```

be an epimorphism from a finitely generated free group onto a fixed finite
packet, put `N=ker(theta)`, and write `b_i=theta(x_i)`.  On one irreducible
packet type `pi:B->U(V)`, suppose actor matrices `X_i` have the proposed
named covariance

```text
X_i pi(b) X_i^*=pi(b_i b b_i^(-1))       (b in B).      (PCG1)
```

Then Schur's lemma gives the exact form

```text
X_i=pi(b_i) tensor W_i,                  W_i in U(M).    (PCG2)
```

The robust version is dimension-free: average
`pi(b_i)^*X_i` over `pi(B)`, then take its polar part in the commutant.  If
the covariance defects in `(PCG1)` are at most `epsilon`, the distance to a
matrix of the form `(PCG2)` is at most `3epsilon`.

For every word `w in F_r`, `(PCG2)` gives

```text
X(w)=pi(theta(w)) tensor W(w).                           (PCG3)
```

Hence on the free quotient kernel,

```text
X(n)=1_V tensor W(n)                    (n in N).        (PCG4)
```

Named packet covariance has therefore killed only the outer automorphism;
it has not killed even the adjoint action of the multiplicity representation.

This freedom has canonical exact finite models with no positive-density
kernel-fixed adjoint sector.  Choose residual-finite quotients

```text
q_k:F_r -> Q_k
```

which are injective on growing balls.  Since `N` is infinite and finite
index, they can be chosen so that

```text
|q_k(N)| -> infinity.                                   (PCG5)
```

Take `W_k=lambda_(Q_k) o q_k`.  These are canonical group microstates for
`F_r`.  Restricted to `H_k=q_k(N)`,

```text
lambda_(Q_k)|_(H_k)
  is [Q_k:H_k] copies of lambda_(H_k).
```

Consequently

```text
dim Fix_(Ad W_k(N)) / |Q_k|^2
 =dim(lambda_(Q_k)(H_k)')/|Q_k|^2
 =1/|H_k| -> 0.                                        (PCG6)
```

Take the direct sum of the relevant Schur blocks inside a canonical finite
regular structural-packet model carrying the forbidden type, and tensor its
multiplicity spaces with the regular `W_k` factor.  The forbidden mass and
the outer Reynolds gap remain fixed, all named covariance equations are
exact, and canonical word moments are preserved: an actor word with nontrivial
image in `Q_k` has zero regular trace, while an actor word trivial in `Q_k`
retains the canonical outer trace.  But every adjoint projection on
which the whole kernel acts trivially lies in

```text
End(V) tensor Fix_(Ad W_k(N)),                          (PCG7)
```

so its normalized adjoint density is at most `1/|H_k|`.  Intersecting with
the predicate Reynolds difference can only reduce that density.  Thus the
quadratic outer gap from
`predicate-rank-jump-forces-adjoint-reynolds-gap` does not localize the free
kernel, even though each generator implements the correct named `B_f`
automorphism.

## What additional cross-context rows would have to prove

Substitute the finite outer packet matrices into any further finite list of
actor, context, or covariance relators.  The remaining equations on the
`W_i` form a finite **active multiplicity presentation**.  If that
presentation has canonical finite-dimensional models in which the image of
`N` has commutant density tending to zero, the same tensor construction
proves the localization estimate false.  In particular this applies whenever
the active group is residually finite and the image of `N` is infinite: its
finite regular quotients reproduce `(PCG6)`.

Therefore a successful finite contextual attachment must establish the
dimension-uniform law

```text
dim Comm(W(N))/dim(W)^2 >= c>0                          (PCG8)
```

on the predicate-selected type in **every** sufficiently accurate canonical
active model, together with invariance of that commutant sector under the
free generators.  Equivalently it must force a positive fraction of the
multiplicity adjoint action to factor through the finite quotient.  Packet
covariance, property `(T)`, finite-group exactification, and canonical scalar
moments do not imply `(PCG8)`; the sequence `(PCG5)--(PCG6)` satisfies all of
them that live on the outer packet.

Ordinary unphased relations whose outer specialization is the identity
still admit the trivial multiplicity solution, but that observation is not
enough: direct sums with the regular gauges above retain the vanishing-density
branch.  Projective/type-dependent rows could in principle exclude these
gauges.  To finish the program they must be vacuous on every allowed BCS type,
activate `(PCG8)` only on forbidden types, and retain the exact perfect
tracial model.  Producing such a row is exactly the payload-conditioned
finite fixed-space theorem in
`agent-free-compressor-payload-kernel-fixed-sector`; if its active
presentation instead has a dimension-uniform no-microstate floor, it already
imports the nonhyperlinear obstruction being sought.

Thus the proposed Schur-form refinement is useful but does not bridge the
gap: it identifies the multiplicity action exactly, and the first new theorem
must control its **adjoint commutant density**, not merely its operator norm,
packet automorphism, or scalar trace.

DERIVATION
packet-covariant-kernel-gauge-proof
