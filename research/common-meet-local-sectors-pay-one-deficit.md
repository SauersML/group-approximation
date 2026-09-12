---
rg: 2
id: common-meet-local-sectors-pay-one-deficit
kind: claim
title: A shared local-sector meet pays its canonical deficit only once
distinct_from:
  high-density-local-sectors-force-one-bcs-gram: that upper-bounds the meet deficit by the sum of individual deficits; this retains the actual meet and can be strictly stronger for correlated or shared sectors.
  canonical-high-density-local-sector-groupifier: that asks for an ordinary-group realization of the sectors and their local rows; this supplies the sharper analytic target but not its groupification.
---

**ESTABLISHED SHARP MEET FORM.**  In the notation of
`high-density-local-sectors-force-one-bcs-gram`, put

```text
p=meet_c q_c,                 beta=tr(1-p).                    (CMD1)
```

Then the stronger inequality

```text
Delta(1-beta)
 <= sum_c mu_c epsilon_c^2
    +(1/2)sum_(c,x)mu_(c,x)kappa_(c,x)^2
    +beta                                                     (CMD2)
```

holds.  In particular, exact local rows force

```text
beta >= Delta/(1+Delta).                                     (CMD3)
```

Thus if all contexts use one common projection `q`, its deficit
`1-tr(q)` is paid once, not once per context.  More generally it suffices
that the canonical microstates determine the actual meet with

```text
1-tr(meet_c q_c)<Delta/(1+Delta).                            (CMD4)
```

This is a strictly weaker sufficient target than `(CHD1)` in
`canonical-high-density-local-sector-groupifier`.

The gain is analytic, not automatic groupification.  A common forbidden
atom, or another authenticated overlap of the accepting sectors, could beat
the sum-of-deficits barrier.  Merely knowing each sector's Plancherel mass
does not determine `(CMD4)`, by
`plancherel-marginals-do-not-control-sector-meet`.

