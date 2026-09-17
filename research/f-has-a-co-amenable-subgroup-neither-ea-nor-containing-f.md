---
rg: 2
id: f-has-a-co-amenable-subgroup-neither-ea-nor-containing-f
kind: claim
title: Thompson's group F has a co-amenable subgroup that is neither elementary amenable nor contains a copy of F
distinct_from:
  some-subgroup-of-thompson-f-is-neither-ea-nor-contains-f: that asks for any Brin–Sapir counterexample; this also demands that the counterexample be co-amenable, which by the sandwich claim proves F sofic.
  jones-subgroup-is-co-amenable-in-thompson-f: that asks co-amenability of Jones' subgroup, which contains F; this asks for a co-amenable subgroup with no copy of F.
  thompson-f-mean-free-actions-dense-configurations-or-unconfined: that splits mean-free amenable actions into shapes (I) and (II); this asks for a transitive shape (II) witness with a Brin–Sapir exotic stabilizer.
---

**OPEN.** There is a subgroup `K ≤ F` such that:
- `K` has no subgroup isomorphic to `F`;
- `K` is not elementary amenable;
- `F/K` carries an `F`-invariant mean.

This is prerequisite P1 of `thompson-f-amenable-via-exotic-co-amenable-subgroup`.
- It is implied by `thompson-f-is-amenable` together with
  `some-subgroup-of-thompson-f-is-neither-ea-nor-contains-f`, since every subgroup of an amenable group is
  co-amenable.
- It implies `some-subgroup-of-thompson-f-is-neither-ea-nor-contains-f`.
- It implies `thompson-f-is-sofic`, by item 5 of
  `f-sandwich-splits-collapse-unless-kernel-is-brin-sapir-exotic`.

**Forced profile of a witness** (item 5 of the sandwich claim, ESTABLISHED):
- every invariant mean on `F/K` is mean-free: `m(Fix(g)) = 0` for `g ≠ e`;
- `m(Moved(c)) = 1`;
- `K` is not confined;
- the conjugates of `K` converge to `{e}` in mean;
- `K` is not normal. A nontrivial normal subgroup contains `F`
  (`nontrivial-normal-subgroups-of-thompson-f-contain-a-copy-of-f`), and the trivial subgroup is elementary
  amenable.

## Attempts

- **Profile attack (swarm-0917-w5-f-decomp, 2026-09-17).** The aim was to kill P1 by showing that F-free
  co-amenable subgroups do not exist.
  - *Established.* The stabilizer IRS of any invariant mean on `F/K` is `t·δ_e + (1−t)·μ_0`, with `μ_0` on
    subgroups containing `F'`. If `1 − t > 0`, a finite generating set of a copy of `F` in `F'` lies in a
    conjugate of `K`, so `K` contains `F`. Hence `t = 1`, and the mean is mean-free. Confined stabilizers force
    `t = 0` (`thompson-f-mean-free-actions-dense-configurations-or-unconfined`, item 3), so `K` is unconfined.
  - *Not a kill.* Mean-freeness with unconfined stabilizers is exactly shape (II), and shape (II) holds if `F`
    is amenable (item 5 there). So this profile cannot contradict P1 without proving
    `thompson-f-is-not-amenable`.
  - *Where it dies.* At the co-amenability step. The known mean-free obstructions refute only confined or
    bounded-configuration stabilizers. An unconfined, F-free, non-normal `K` is beyond every obstruction in
    the graph, and the F-free subgroups of `F` that the graph classifies are elementary amenable
    (`two-one-bump-pl-maps-unequal-supports-ea-or-contain-f`, `f-has-ea-subgroups-of-every-class-below-epsilon-zero`),
    so there is no candidate to test.
  - *Payoff.* P1 is at least as hard as refuting Brin–Sapir and proving `F` sofic together. By items 2–3 of the
    sandwich claim, any weaker "co-amenable subgroup" hypothesis collapses to amenability of `F`.
