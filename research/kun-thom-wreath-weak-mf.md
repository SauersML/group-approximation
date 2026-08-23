---
rg: 2
id: kun-thom-wreath-weak-mf
kind: claim
title: Weak MF status of the Kun--Thom commuting-lamp wreath
distinct_from:
  symmetric-double-weak-mf: That settles the free-lamp amalgam positively; this is the commuting-lamp wreath over the same compression mechanism, and its answer is negative.
  hyperlinear-wreath-model: That asks for a normalized-Hilbert--Schmidt model of the same group; non-MF does not by itself decide hyperlinearity.
  kun-thom-clifford-extension-not-weak-mf: That is the Clifford central extension and is also non-weak-MF, but its central-sign obstruction does not descend formally; the present claim is now proved directly in the commuting-lamp quotient.
artifacts:
  - notes/NOTEPAD.md
  - research/artifacts/kun-thom-2608-06222-verified.md
  - research/artifacts/radical-renormalization-2026-08-23.md
---

**Resolved negatively 2026-08-23.**  The Kun--Thom commuting-lamp wreath

```text
W = (directSum_(G/Gamma) C_2) semidirect G
```

is **not weak MF** in the operator-norm norm-matrix-corona sense.

## Proof

Kun--Thom's hypotheses say that `Gamma<G` is infranormal but not normal and
that both groups are Kazhdan.  The elementary established claim
`infranormal-nonnormal-has-infinite-compression-orbit` supplies a strict
compressor

```text
s Gamma s^-1 < Gamma.
```

Let `k` be the nontrivial lamp at the site `s Gamma`.

* `k` is an involution.
* `Stab_G(s Gamma)=s Gamma s^-1`, so the compressed copy centralizes `k`.
* The `Gamma`-conjugates of `k` are coordinate lamps and therefore commute.

Thus `compression-torsion-collapse` says that every norm-matrix-corona
representation identifies `k` with every lamp in its `Gamma`-orbit.  Choose
`gamma in Gamma \ s Gamma s^-1`; strictness gives
`gamma s Gamma != s Gamma`.  Hence the nontrivial two-lamp element

```text
k_(gamma s Gamma) k_(s Gamma)
```

is killed by every corona representation.  No such representation is
injective, so `W` is not weak MF.

Equivalently, this is the first-fibre kernel of the canonical compressor
self-cover `r_s(g Gamma)=g s^-1 Gamma` from
`coset-compression-renormalization`.

## Consequence for the lamp-type classification

Together with the already established neighbours, the one-sided-compression
nonsofic examples split as follows:

```text
free lamps       -> weak MF,
commuting C_2    -> not weak MF,
Clifford lamps   -> not weak MF.
```

So the common Kazhdan/compression geometry does not determine the operator-norm
answer; the lamp relations do.  This closes the existing route
`nonsofic-mf-classification-by-lamp-type`.

This resolution is new relative to the supplied Cairn graph.  It is not a
literature-priority claim; Kun--Thom's current preprint proves nonsoficity and
does not state this operator-norm MF conclusion.
