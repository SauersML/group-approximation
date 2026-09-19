---
rg: 2
id: grading-zero-corner-does-not-orient-controlled-payload
kind: claim
title: Grading anticommutation block-encodes zero but not a controlled payload
distinct_from:
  central-corner-block-is-not-a-group-word: that proves the additive controlled block is not a word in the abelian control and payload; this audits the proposed LCU workaround using a new actor and a grading-enforced zero corner.
  controlled-reflection-cell-has-free-orientation: that classifies one minimal controller; this identifies exactly how its free orientation contaminates every LCU corner and why an extra grading only produces another zero block.
  block-encoded-acceptance-still-needs-corner-return: that compresses a fixed verifier product into one unitary corner; this treats arbitrary polynomial fingerprints and the attempted existential controlled-word compiler.
---

**ESTABLISHED BOUNDARY.**  A finite Pauli ancilla can impose a zero corner by
ordinary group relations.  On the `J=-1` sector, if `Z^2=W^*W=1` and

```text
Z W Z = J W,              q=(1-Z)/2,                   (GAB1)
```

then direct expansion gives `qWq=0`.  This is compatible with the regular
trace: `W` swaps the two equal-trace `Z` sectors.  Thus the zero block needed
inside a block encoding is not itself the obstruction.

The nonzero controlled payload is different.  For a payload involution `U`,
the desired gate is

```text
C_U=(1-q)+qU.                                             (GAB2)
```

It is an additive group-algebra element, not a word.  The ordinary
covariance presentation with a control flip `X` determines only the relative
action of the two `Z` blocks.  On the marked Pauli sector every solution has

```text
C = diag(A, A U),                                        (GAB3)
```

where `A` is an arbitrary multiplicity involution commuting with `U`.  The
intended controlled gate is only the orientation `A=I`.  Therefore an LCU
circuit built from such existential controlled gates encodes an
orientation-decorated polynomial, not the prescribed `p(U)`.

Adding another grading relation cannot set `A=I`: anticommuting with that
grading makes `A` off-diagonal and hence gives another vanishing compression;
commuting leaves its two orientations.  Selecting one orientation by a
finite signed packet is a legitimate **new** possibility, but it requires a
positive selected corner and a sectorwise equality/return theorem.  It is
not supplied by LCU.  If that theorem is asserted tracially and functorially
for every representation, the unwanted signed selector atoms survive in the
twisted regular corner by
`twisted-regular-predicate-projections-have-positive-trace`.  Hence the
selection must be a genuinely finite-matrix-only decoder or a separately
authenticated type with a quantitative return.

So finite ancillas and LCU remove additive syntax only after controlled-word
orientation has already been solved.  They do not provide an existential
escape from the coherent-oracle or Fock-carrier fences.  The exact remaining
gate is:

```text
row-square/HS exactify one selected controller orientation
+ return its positive corner to the fixed mark.           (GAB4)
```

## Attempts

- Grading anticommutation proves `(GAB1)` exactly, but zero carries no
  fingerprint information.
- Covariance groupifies a Clifford controlled gate, but only up to the
  multiplicity actor `A` in `(GAB3)`.
- A second anticommuting control balances or swaps the actor sectors; it does
  not choose the identity actor.
- Directly postulating `(GAB2)` is the original additive signed-corner
  compiler, not an ordinary group-word relation.
- `finite-cocycle-select-forces-one-common-lcu-gauge` is a genuine escape for
  a transitive finite cocycle list: shift covariance synchronizes all actors
  to one harmless right gauge.  Its cocycle law and its remaining
  `1/|K|`-corner return explain why this does not orient arbitrary LCU lists.
