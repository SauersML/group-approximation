---
rg: 2
id: unbalanced-pair-sum-overlay-has-scalar-syndrome-escape
kind: claim
title: Unbalanced pair-sum faces dilute a constant-distance scalar syndrome
distinct_from:
  quadratic-redundant-check-overlay-gives-uniform-face-gap: that computes an adjoint gap for exact shared representations; this gives approximate scalar tuples which violate the original parity layer after it has vanishing sampling weight.
  positive-rate-tanner-tests-have-contextual-models: that uses noncommuting contextual representations at positive rate; this escape is one-dimensional and commuting.
  central-clifford-parity-sectors-round-uniformly: that assumes every original parity row holds exactly; this violates all original rows while satisfying every pair-sum row.
---

ESTABLISHED.  Let `H` have `M=Theta(L)` distinct nonzero rows, every column
of weight at most `D`, and suppose there is `z in F_2^L` with

```text
H z = 1_M.                                                   (UPS1)
```

Use every original row once and every unordered pair-sum row `h_a+h_b`
once, and normalize defect uniformly over these `Theta(M^2)` faces.  The
scalar reflections

```text
Q_i=(-1)^(z_i) I                                             (UPS2)
```

commute, satisfy every pair-sum parity face exactly, and violate every
original parity face by the scalar `-I`.  Their average squared face defect
is therefore `O(M/M^2)=O(1/M)`.

They nevertheless remain a constant average distance from every exact code
character.  If `c in ker H`, then `H(z+c)=1_M`.  Since changing one
coordinate affects at most `D` syndrome entries,

```text
wt(z+c) >= M/D.                                              (UPS3)
```

Thus the normalized Hamming distance from `z` to `ker H` is at least
`M/(DL)=Omega(1)`, and the average squared normalized-HS movement from
`(Q_i)` to any exact scalar code tuple is at least `4M/(DL)`.

Condition `(UPS1)` occurs in the most elementary bounded-degree case: if
every check row has odd weight, take `z=1_L`.  Hence it is not excluded by
bounded row width, bounded column degree, positive code distance, or LTC
soundness.

The necessary normalization repair is to repeat every original row
`Theta(M)` times, or equivalently give the original parity layer constant
sampling weight.  This adds only `Theta(M^2)` bounded faces and
`Theta(M)` occurrences per logical coordinate, so the existing quadratic
repetition still makes occurrence degree bounded.  All synchronization and
basin-capture statements using the pair-sum overlay must use this balanced
version (or impose and exploit a separate affine-syndrome-distance
hypothesis); the unbalanced version is false already in dimension one.

