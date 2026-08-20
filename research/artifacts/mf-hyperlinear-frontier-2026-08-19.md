# MF implies hyperlinear: audited frontier on 2026-08-19

This note records what the current Lean/Cairn development proves about the
weak Carrión--Dadarlat--Eckhardt MF convention and what remains open.

## Kernel-checked positive fragment

`GroupApproximation/Sofic/KazhdanCorner.lean` proves

```text
hasNontrivialHyperlinearQuotient_of_kazhdan_weakMF
isHyperlinear_of_simple_kazhdan_weakMF
```

so every nontrivial property-(T) weak-MF group has a nontrivial hyperlinear
quotient, and every nontrivial simple property-(T) weak-MF group is
hyperlinear.  Cairn records this as `kazhdan-mf-hyperlinear-fragment`.

## Why this does not prove the general implication

For a nonsimple Kazhdan group the corner quotient may have a nontrivial kernel.
A generic Kazhdan-envelope construction does not repair this: known routes use
quotients, while weak MF is not quotient-closed.  The invalid shortcut is
recorded in `docs/FALSE_KAZHDAN_CORNER.md`.

## Exact remaining frontier

Two live routes remain.

1. `mf-trace-gap-defect-ratio-models`: select operator-norm models for which
   multiplicative defect `epsilon_n` and trace gap `kappa_n` satisfy

   ```text
   epsilon_n^2 / kappa_n -> 0.
   ```

2. `mf-invariant-corner-visibility`: make each MF-visible element
   macroscopically visible on an invariant corner and renormalize by that
   corner's rank.

Operator separation alone gives only a rank-one trace gap, of order `1/d`.
Identity-block padding proves that no argument can simply reuse an arbitrary
MF embedding coordinate by coordinate.

## Universal amplification does not remove the gap

`docs/FALSE_FERMIONIC_AMPLIFICATION.md` proves the complementary obstruction:
continuous unitary post-processing that turns rank-one operator visibility
into macroscopic normalized Hilbert--Schmidt visibility necessarily pays a
`sqrt(d)`-scale Lipschitz cost.  That is the same scale appearing in corner
renormalization.

Therefore `mf-implies-hyperlinear` remains OPEN.  The repository has a strong
property-(T) fragment and a precise two-route frontier, but no theorem crossing
either remaining hinge.
