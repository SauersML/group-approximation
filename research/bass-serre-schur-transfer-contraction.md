---
rg: 2
id: bass-serre-schur-transfer-contraction
kind: claim
title: An infinite free-amalgam Schur network contracts every nonstationary packet type
distinct_from:
  schur-marked-character-transfer-gap: that proves contraction only after projecting to four central characters; this requires the complete induction/restriction type operator and quantitative leakage payment.
  finite-graph-of-groups-representation-types-are-integer-flows: that gives stationary positive flows on a finite type graph; this uses an infinite Bass--Serre tree and requires uniform contraction off the one permitted scalar ray.
artifacts:
  - research/artifacts/trace-promotion-renormalization-program-2026-08-20.md
---

Choose an infinite iterated free amalgam of the fixed Schur packet/reset stages
over their finite multiplicity wires.  On the Hilbert space of complete
weighted packet types, let `T_n` be the normalized induction/restriction
transfer at stage `n`, after removing the scalar stationary ray identified by
`symmetrized-reset-collapses-schur-flow-to-one-ray`.

Prove uniform constants `rho<1` and `C<infinity` such that

```text
||T_n xi||_2 <= rho ||xi||_2,                              (BST1)
```

and every failure of the exact transfer equations contributes at most
`C sqrt(E)` to the corresponding type discrepancy with bounded overlap.
Mass escaping to infinity must either make the marked carrier tend to zero or
pay this leakage.  The exact non-CE tracial model must extend along the same
wires.

The finite falsification interface is explicit: build the full type matrices
for one packet/reset stage and compute the largest singular value on the
stationary complement.  A value `>=1` for every admissible wiring kills this
route.  The exact `1/5` central-character value is evidence, not a substitute
for that full computation.

Even a positive answer to `(BST1)` is insufficient for the original plain
amalgam proposal. `stationary-type-mass-reused-on-infinite-amalgams` proves
that the surviving scalar ray is reused on one fixed Hilbert space at every
tree vertex and therefore is not an `ell^2` mass distribution. A useful
version of this claim must additionally force orthogonal range copies or a
proper-corner loss on that scalar ray; transverse spectral contraction alone
cannot yield the multiplicity return theorem.

## Attempts

- Averaging the ten mark-preserving involutive packet charts gives the exact
  transverse central-character norm `1/5`.
- The next computation lifts this average through the complete restriction
  matrices of `translation-symmetrized-full-schur-reset`. Hidden irreducible
  multiplicities may still support a norm-one vector.
- Reject a wiring if its full singular value off the scalar ray is `>=1`.
  Truncating the tree before separating boundary escape tests the wrong
  operator.
