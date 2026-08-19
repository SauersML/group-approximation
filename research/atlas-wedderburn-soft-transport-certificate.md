---
rg: 2
id: atlas-wedderburn-soft-transport-certificate
kind: claim
title: Finite atlas microstates admit a positive-dual transport cost paid only by relator defect
artifacts:
  - experiments/weighted_hall_interdiction.py
distinct_from:
  atlas-wedderburn-hall-deficient-support-certificate: that asks up front for one hard zero-one support graph; this target permits adaptive nonnegative costs as a search parametrization, although soft-transport-thresholds-to-hall-subsequence shows that a successful asymptotic soft certificate still contains a hard deficient graph on a subsequence.
  universal-atlas-ideal-cannot-force-hall-deficit: that rules out fixed universal algebraic support zeros; this target permits the cost certificate to be selected from finite-multiplicity spectral/rank data and need not survive in the exact factor model.
  fixed-atlas-transport-cost-cannot-separate: that rules out a fixed positive-dual soft cost just as strongly; this target requires the cost itself to be selected from the finite microstate.
  soft-transport-thresholds-to-hall-subsequence: that is the generic threshold theorem explaining the asymptotic relation between this soft formulation and hard Hall support; this is the atlas-specific missing certificate.
---

Use the minimal regular-`A_8` Wedderburn projections `p_v` on the first chart
and `q_u` on the second chart, with their fixed rational trace weights
`alpha_v,beta_u`.  There are constants

```text
C>0, c>0, gamma>0
```

independent of external multiplicity with the following property.

For every finite multiplicity `k` and every relative chart unitary `U` whose
canonical atlas packet has normalized-Hilbert--Schmidt defect `delta`, one can
select nonnegative costs

```text
0 <= c_(u,v) <= 1
```

and real dual potentials `x_v,y_u` such that

```text
x_v+y_u <= c_(u,v)                                    (AST1)
```

for every pair and

```text
sum_v alpha_v x_v + sum_u beta_u y_u >= gamma,        (AST2)
```

while the actual relative-unitary block energies pay only

```text
sum_(u,v) c_(u,v) ||q_u U p_v||_2^2
 <= C delta^c.                                         (AST3)
```

The costs and potentials may depend on the finite coefficient data of `U` and
on `k`; only the constants and the selection rule must be uniform.  This is
not optional: `fixed-atlas-transport-cost-cannot-separate` proves that one
fixed cost matrix with positive dual value cannot be controlled to zero by any
universal exact-atlas estimate.

By `unitary-block-energy-transport`, `(AST1)` and `(AST2)` force the left side
of `(AST3)` to be at least `gamma` for every unitary.  Hence no sequence can
have `delta -> 0`.

## What softening does and does not buy

`soft-transport-thresholds-to-hall-subsequence` shows that the soft target is
**not asymptotically weaker** on this fixed Fourier alphabet.  Along any
hypothetical sequence satisfying `(AST1)--(AST3)` with `delta -> 0`, threshold
at `gamma/2`.  The cheap-edge graph cannot carry the fixed marginals, while
the actual block mass on the complementary expensive edges tends to zero.
There are finitely many graphs, so one deficient graph repeats on a
subsequence.  Thus every successful soft proof already contains the hard
finite-support phenomenon after thresholding.

What the soft formulation *does* buy is optimization: one can search over
continuous quadratic energies and dual pressures before committing to which
finite blocks will ultimately be declared negligible.  It does not remove the
need for a genuinely finite-coordinate selection step.

## Attempts

- **Hard Hall is a special case.**  If the current
  `atlas-wedderburn-hall-deficient-support-certificate` is proved, take cost
  one on forbidden blocks and zero on allowed blocks.  Its deficient cut gives
  potentials of dual value `gamma`.
- **Do not stop at a fixed twirled quadratic form.** Averaging packet defects
  over fixed chart symmetries may diagonalize useful finite Fourier energies,
  but if the resulting cost matrix is fixed and has positive transport dual
  value, `fixed-atlas-transport-cost-cannot-separate` says it cannot vanish in
  the exact model.  Twirling is only an upstream feature extractor.
- **Finite spectral selection is the gate.** Threshold singular directions of
  the twirled finite coefficient forms and define `c_(u,v)` from which
  directions are actually low-energy in that finite microstate.  The threshold
  or rank-based tie break may depend on `k`; `soft-transport-thresholds-to-hall-subsequence`
  then converts a successful vanishing-cost sequence back into a fixed hard
  deficient graph automatically.
- **Optimize before proving.**  The zero-one restriction can be explored with
  `weighted_hall_interdiction.py`; for soft rational costs, search the
  transportation dual directly and aim symbolic/analytic work at the blocks
  with positive dual pressure.