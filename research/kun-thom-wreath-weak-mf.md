---
rg: 2
id: kun-thom-wreath-weak-mf
kind: claim
title: Weak MF status of the Kun--Thom commuting-lamp wreath
distinct_from:
  symmetric-double-weak-mf: That settles the free-lamp amalgam, where Shulman's C-star amalgam theorem applies; this is the commuting-lamp wreath product, which is not an amalgam and to which that theorem does not apply.
  hyperlinear-wreath-model: That asks for a normalized-Hilbert--Schmidt (tracial) model of the same group; this asks only for an operator-norm one, which is a strictly weaker requirement and is a different open question.
  kun-thom-clifford-extension-not-weak-mf: That is the Clifford central extension of this group, and it is settled negatively; whether the property descends to this central quotient is exactly what is unknown.
artifacts:
  - notes/NOTEPAD.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Is the Kun--Thom commuting-lamp wreath

```text
W = (directSum_(G/Gamma) C_2) semidirect G
```

weak MF, i.e. MF in the operator-norm norm-matrix-corona sense?

**Open.** The corpus is explicit that this is not settled, and warns against
the natural mis-inference from the free-lamp case
(`notes/NOTEPAD.md:30421-30423`):

> Correction: weak MF of W is not banked. The symmetric-double proof applies
> to the free-lamp amalgam, not to the commuting-lamp wreath product. Thus
> this finite certificate is valid but stronger than the already-open weak-MF
> problem for W.

## Shared hinge with the marked-quotient cluster (cairn-quotient-mf, 2026-08-14)

This question and `commuting-lamp-quotient-mf` are the same question for two
different Kazhdan compressor pairs, and both are decided by
`corona-commutant-no-growth`: if the operator-norm relative commutant
`Theta(Gamma)' cap Q` never grows under the compressor, the lamp at the
compressed site commutes with `Theta(Gamma)`, so every corona representation
identifies two distinct lamps and none is injective.  Conversely
`marked-quotient-mf-forces-commutant-growth` proves the necessity direction by
the same one-lamp argument, which uses only the compression relation and
injectivity: weak MF of `W` *forces* the growth.  So the hinge is exact here
too, and a single theorem settles this claim together with both marked
quotient claims.

## Why the two settled neighbours do not decide it

`W` sits between two groups whose weak MF status *is* known, and inherits
neither answer:

- **Above it**, the Clifford lamp extension has `E_Cl/<z> = W`, and
  `kun-thom-clifford-extension-not-weak-mf` says `E_Cl` is not weak MF. Weak MF
  does not pass from a group to its central quotients in the direction needed,
  and the whole point of that theorem is that the obstruction lives on the sign
  `z`, which is exactly what is killed in passing to `W`. So the negative
  result upstairs is consistent with either answer here.
- **Beside it**, the free-lamp amalgam `G *_Gamma (Gamma x K)` is weak MF
  (`symmetric-double-weak-mf`), but by an argument that consumes the amalgam
  structure — Shulman's theorem is about `A *_C A` — and `W` has no such
  decomposition.

## What either answer would buy

A positive answer gives another weak-MF nonsofic group, strengthening the
separation already obtained from the free-lamp family, and would be the
cleanest possible entry in `nonsofic-mechanism-mf-classification`: the same
group nonsofic and weak MF, with the two lamp types on opposite sides.

A negative answer is the more interesting one. It would make `W` a second
non-MF group by a mechanism with no finite normal subgroup and no central
mark, which is exactly the shape
`torsion-free-finitely-presented-non-mf` needs and which the finite-normal
criterion cannot reach.

Note that neither answer bears directly on `hyperlinear-wreath-model`:
operator-norm models carry no trace, so weak MF of `W` would not make it
hyperlinear (`mf-implies-hyperlinear` is itself open, and
`weak-mf-embedding-not-reusable` shows a given weak-MF embedding can never be
re-metrized into a hyperlinear one).
