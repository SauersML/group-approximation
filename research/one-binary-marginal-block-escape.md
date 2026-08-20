---
rg: 2
id: one-binary-marginal-block-escape
kind: claim
title: One balanced binary marginal admits an explicit finite-support escape of its coordinate refinement
artifacts:
  - experiments/signed_hecke_one_marginal_escape.py
  - experiments/signed_hecke_one_marginal_escape.json
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  piecewise-group-transport-gives-corner-unitaries: that constructs a corner unitary from prescribed source and range projections; this gives a closed formula in a finitely presented direct-product group and proves that its conjugated context atoms genuinely leave the finite root block while one chosen marginal remains fixed.
  root-block-piecewise-transport-cannot-host-nonce-bcs: that excludes atlases whose context projections remain in the root block; this constructs the first exact local escape from that obstruction.
---

Let `K` be finite, let `qC[K]q isomorphic to M_D(C)` be a simple algebraic
corner with `D>=4`, and choose matrix units `(E_(ij))` in that corner.  Put
`e_i=E_(ii)`.  Let

```text
d=sum_i epsilon_i e_i,             epsilon_i in {+1,-1}, (OBM1)
```

be a diagonal corner involution.  After duplicating all coordinates once if
necessary, choose distinct `r,s` with `epsilon_r=epsilon_s`.  Let `u` be the
Hadamard rotation on the `(r,s)` plane and the identity elsewhere, so

```text
[u,d]=0,              f_i=u e_i u^*.                     (OBM2)
```

Take `Gamma=K times F_D`, where `F_D=<h_1,...,h_D>` is free, and define

```text
W=sum_i h_i e_i in q C[Gamma] q.                         (OBM3)
```

Then `W` is an algebraic corner unitary, `[W,d]=0`, and

```text
P_i=W f_i W^*,             sum_i P_i=q,
sum_i epsilon_i P_i=d.                                    (OBM4)
```

The two refined coordinate projections `P_r,P_s` do not lie in the root
algebra `qC[K]q`.
Indeed their expansions have nonzero coefficients at the reduced free words
`h_r h_s^(-1)` and `h_s h_r^(-1)`.  Thus `(OBM3)` gives an exact finite-word
placement of the coordinate-refined diagonal algebra outside the finite root block while
leaving one prescribed shared binary marginal unchanged.

For a BCS context, group the coordinate atoms into its assignment
projections.  If `r,s` belong to distinct supported assignments with the same
value of the preserved variable, then those two coarse assignment projections
also leave the root block.  If they are duplicate coordinates of one
assignment, the off-diagonal terms cancel in their coarse sum; only the
irrelevant refinement escapes.  Thus genuine context escape additionally
requires that the preserved marginal not separate the supported assignments.

If `d` is scalar, the same construction uses any two coordinates.  Hence,
after harmless common amplification, every balanced binary overlap admits
this refined one-edge cell.  Amplification alone cannot create two distinct
assignments in one sign fiber.
