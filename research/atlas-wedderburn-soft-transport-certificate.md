---
rg: 2
id: atlas-wedderburn-soft-transport-certificate
kind: claim
title: Finite atlas microstates admit a positive-dual transport cost paid only by relator defect
artifacts:
  - experiments/weighted_hall_interdiction.py
distinct_from:
  atlas-wedderburn-hall-deficient-support-certificate: that asks for a hard zero-one support graph; this target permits arbitrary soft nonnegative costs on Fourier blocks and is therefore strictly more permissive.
  universal-atlas-ideal-cannot-force-hall-deficit: that rules out fixed universal algebraic support zeros; this target permits the cost certificate to be selected from finite-multiplicity spectral/rank data and need not survive in the exact factor model.
  fixed-atlas-transport-cost-cannot-separate: that rules out a fixed positive-dual soft cost just as strongly; this target requires the cost itself to be selected from the finite microstate.
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
- **Finite spectral selection.**  Threshold singular directions of the
  twirled finite coefficient forms and define `c_(u,v)` from which directions
  are actually low-energy in that finite microstate.  A vanishing threshold
  or rank-based tie break is allowed to depend on `k`; this is precisely the
  non-universal step the factor-model audit demands.
- **Optimize before proving.**  The zero-one restriction can be explored with
  `weighted_hall_interdiction.py`; for soft rational costs, search the
  transportation dual directly and aim symbolic/analytic work at the blocks
  with positive dual pressure.
