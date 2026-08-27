---
rg: 2
id: nand-sheet-swap-cannot-be-a-pure-central-phase
kind: claim
title: A NAND sheet swap scalarizes only with the separator sign attached
distinct_from:
  s4-nand-cycle-holonomy-is-one-s2-bit: that computes the projection-level swap holonomy; this tests its two-fold Schur lift and identifies the exact signed word implemented by the swap.
  boolean-predicate-central-phase-word: that asks for a predicate value encoded as a scalar projective phase; this proves that the minimal NAND swap produces a separator-dependent phase rather than a pure central word.
  central-pinning-forbids-nonlinear-predicates: that gives a general character-theoretic affine obstruction; this is the exact three-atom spectral calculation for the proposed S2 holonomy lift.
---

Let `q` be a corner unit and let `S,R` be commuting self-adjoint involutions
whose joint atoms have NAND support

```text
e_(+,+), e_(+,-), e_(-,+) nonzero,       e_(-,-)=0.    (NSS1)
```

Let `H` be a corner unitary which commutes with `S`, swaps the first two
atoms in `(NSS1)`, and preserves the third.  If `J` denotes the central sign
`-q`, then the exact lifted word is

```text
H R H^* = -S R = J S R.                                (NSS2)
```

It cannot be the pure phase relation

```text
H R H^* = J R                                           (NSS3)
```

unless the third NAND atom `e_(-,+)` is zero.  Thus scalarizing the `S_2`
cycle bit necessarily carries the separator sign `S`; removing `S` destroys
the nonaffine three-point support.

The identity `(NSS2)` has an exact finite signed-permutation realization.
On the ordered atom basis `(+,+),(+,-),(-,+)`, take

```text
S=diag(+,+,-),       R=diag(+,-,+),
J=-I_3,              H=(12).                            (NSS4)
```

These matrices lie in the finite signed permutation group
`(C_2)^3 semidirect S_3`, whose defining representation is irreducible.
Hence the Schur lift is phase-safe locally but has a finite-dimensional model;
it creates no nonhyperlinear mark.

In particular, two identical lifted swaps do not isolate `J`: multiplying
their signed words cancels both factors,

```text
(J S)^2=q.                                               (NSS5)
```

Using only one copy retains `JS`, not `J`.  Any successful central-phase
compiler from the NAND holonomy bit must therefore introduce an additional
operation which cancels the separator `S` without also cancelling `J`, while
remaining exact on the third atom.  The bare two-fold Schur/Clifford lift
cannot do so.

