---
rg: 2
id: faithful-sofic-action-atlas-has-free-loeb-actor
kind: claim
title: Every sofic atlas of a faithful set action has a free Loeb actor
artifacts:
  - research/artifacts/sl3-relative-invariant-transfer-irs-firewall-2026-08-23.md
distinct_from:
  sofic-coset-atlas-linearizes-to-exact-quasiregular-coboundary: that extracts the quasi-regular Hilbert packet and fences Garland cohomology; this computes the point-stabilizer law of the underlying Loeb permutation action and fences higher-rank IRS rigidity.
  coset-bernoulli-action-is-essentially-free: that proves essential freeness of a generalized Bernoulli action by independence of coordinates; this proves freeness of the Loeb action canonically attached to any GKEP atlas of any faithful set action.
  gkp-sofic-action-toolkit: that records the general permanence and ultraproduct formulations from GKEP; this is a direct consequence of their equivariant, distance-one atlas embedding with an IRS-rigidity application not stated there.
---

Let a countable group `G` act faithfully on a countable set `X`.  In every
Gao--Kunnawalkam Elayavalli--Patchell ultraproduct model of a sofic action,
the associated pmp action of `G` on the Loeb root space is essentially free.
Equivalently, its stabilizer IRS is

```text
delta_{ {e} }.                                             (FLA1)
```

For the arithmetic action

```text
SL_3(Z[1/2]) action SL_3(Z[1/2])/SL_3(Z),                  (FLA2)
```

the action is faithful: the core of `SL_3(Z)` is trivial.  Hence, if `(FLA2)`
is sofic, the resulting Loeb model has the ordinary free IRS.  Higher-rank
IRS/Stuck--Zimmer rigidity therefore cannot obstruct its existence; the IRS
it sees is already the allowed regular one.

This is independent of the failure of relative invariant transfer.  The
same free pmp action can have a Koopman vector `xi_C` fixed by `C` but moved
orthogonally by `A`, because vector stabilizers are not point stabilizers.
Thus neither point-stabilizer rigidity nor character rigidity upgrades
`Fix_C=Fix_A` on the permutation-ultraproduct representation.

