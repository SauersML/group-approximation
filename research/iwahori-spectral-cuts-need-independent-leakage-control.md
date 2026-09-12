---
rg: 2
id: iwahori-spectral-cuts-need-independent-leakage-control
kind: claim
title: Small Iwahori defect does not force smaller relative leakage of a fixed spectral cut
distinct_from:
  commuting-iwahori-pairs-have-quadratic-rank-repair: that exactifies the reducing common residual support when all generators commute; this gives noncommuting exact vertices whose specified positive-threshold residual cut has nonzero leakage relative to their vanishing defect.
  dilution-obstructs-flat-quadratic-iwahori-repair: that forces concentrated correction on a diluted incompatible character; this tests a spectral support selector near an explicit three-dimensional compatible endpoint and still admits a linear-cost smooth repair.
  iwahori-spectral-residual-gate-has-polynomial-step: that contracts under two explicit residual hypotheses; this shows that small HS defect alone does not make a raw high residual-energy cut have leakage of smaller order than the defect.
  iwahori-support-erasure-has-linear-commutator-leakage: that contracts under a supplied retained-residual and commutator budget; this gives raw fixed-threshold cuts which fail its small-constant commutator budget despite vanishing HS defect.
artifacts:
  - research/artifacts/iwahori-spectral-threshold-leakage-counterexample-2026-09-08.md
---

For every sufficiently small fixed energy threshold `theta>0`, there
are positive-central exact modular vertex pairs `q_n` in dimension
`n` with Iwahori Hilbert tuple defect `e_n->0` such that

```text
P_n=1_((theta,infinity))(sum_j R_j(q_n)^* R_j(q_n))
```

has rank one and

```text
liminf_n max_U ||(I-P_n) U P_n||_(2,n)/e_n > 0,
```

where `U` ranges over the four vertex generators. The corresponding
commutator-leakage ratio is also bounded away from zero. Hence no
universal `o(e)` leakage estimate for this cut follows from small
normalized-HS defect, even though `rank(P_n)/n<=e_n^2/theta`.

More precisely, the construction has

```text
||[P_n,B_1(q_n)]||_(2,n)/e_n
  ~ sqrt(11/12)/sqrt(theta)             as theta -> 0,
```

with the ratio independent of `n` for each fixed threshold. If
`e_max=max_j ||R_j(q_n)||_2`, then `e_max<=e_n`. Therefore for
every sufficiently small fixed positive threshold the cut fails
the support-erasure budget

```text
h+4L kappa_2<=e_max/2,
kappa_2=max_U ||[U,P_n]||_2,
h=max_j ||(I-P_n) R_j(q_n)(I-P_n)||_2,
```

already because `4L kappa_2>e_n/2>=e_max/2`; here the Iwahori
word-length constant is `L=6`. This asserts failure of that sufficient
condition for the specified cut, not failure of every erasure output.

The construction perturbs one torsion generator in an explicit
three-dimensional `A_4` compatible endpoint and then dilutes by trivial
summands while holding its amplitude and threshold fixed. Its full
three-dimensional residual support is reducing. Enlarging to that
block permits repair, and undoing the one conjugation already gives
an exact same-dimensional endpoint at generator cost at most
`e_n/sqrt(2)`. Thus this claim does not refute a combined surgery and
smooth correction method, or assert a defect of the full common support.

DERIVATION
iwahori-a4-spectral-cut-leakage-proof
