---
rg: 2
id: mihailova-coset-wreath-sofic-action-boundary
kind: claim
title: The isolated Mihailova wreath is hyperlinear under action soficity, but its free restriction cannot test the quotient
distinct_from:
  mihailova-envelope-forces-one-sl3-coset-wreath: that reduces a successful mixed non-CE envelope to one vertical wreath; this audits the only published permanence hypothesis for that wreath and proves why restriction to the Mihailova free subgroup cannot refute it.
  coordinate-action-not-sofic: that uses Kun--Thom rigidity to refute one arithmetic coset action; this concerns the different stabilizer N=ker(F_m->Q), for which restriction to F_m is automatically sofic even when Q is finitely presented and nonsofic.
  gkp-sofic-action-toolkit: that records the general restriction, orbit, and free-actor theorems; this applies them to the isolated SL3 action and includes the GKP Connes-embedding consequence.
artifacts:
  - research/artifacts/gkp-2401-04945-verified.md
---

Use the data of `mihailova-envelope-forces-one-sl3-coset-wreath`:

```text
E=F_m < L=SL_3(Z),    pi:E->Q,    N=ker(pi),
X=L/N,                W_N=(direct_sum_X C_2) rtimes L.       (GSB1)
```

The precise GKP boundary is as follows.

1. If the set action `L curvearrowright X` is sofic, then `W_N` is
   hyperlinear.  This is Gao--Kunnawalkam Elayavalli--Patchell Theorem 3.8,
   with the Connes-embeddable lamp algebra `L(C_2)` and the residually finite,
   hence hyperlinear, actor `L`.
2. Restricting to `E` cannot disprove the hypothesis.  The orbit of `N in X`
   is `E/N`, and the restricted transitive action `E curvearrowright E/N` is
   sofic for **every** subgroup `N<E`, because every action of a free group on
   a countable set is sofic (GKP Theorem 2.19).
3. This remains true when `Q=E/N` is finitely presented, property `(T)`, and
   nonsofic.  The same set is the regular `Q`-set, whose `Q`-action is not
   sofic, but it is a sofic `E`-set.  Thus soficity of a set action does not
   descend after factoring its actor by the action kernel; finite normal
   generation of `N` (the extra information supplied by finite presentation
   of `Q`) does not repair that false descent.
4. A property-`(T)` stabilizer cannot be substituted into this Mihailova
   input.  By Nielsen--Schreier, `N` is free.  A free group with property
   `(T)` is finite (property `(T)` plus the Haagerup property), and a finite
   subgroup of the torsion-free group `E` is trivial.  Then `Q=E`, eliminating
   the nonsofic/nonhyperlinear quotient input.

Consequently the published permanence theorem gives a sharp one-way test:
proving `L curvearrowright L/N` sofic refutes the Mihailova nonhyperlinearity
route, while proving it nonsofic would still not prove `W_N` nonhyperlinear.
Neither finite presentation nor property `(T)` of `Q` strengthens the free
restriction into a quotient detector.  The unresolved datum is genuinely the
ambient `SL_3(Z)` action (or directly the Connes embeddability of its Bernoulli
crossed product), not the orbit seen by `E`.

