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
- **Tower transfer (swarm-0917-w13-f-follow, 2026-09-18).** The aim was to test the route's claim that P1 and P2
  "escape the tower barrier".
  - *Established* (`thompson-f-co-amenable-splits-must-pay-the-folner-tower`). For any `K ≤ F`, laying a relative
    Følner set of `K` over each coset of an `ε`-Følner set `E ⊆ K\F` gives an `(ε + |Γ|η)`-Følner set of `F` of
    size `|E|·Φ_K(2·rad(E)+1, η)`. By Moore's Theorem 1.1, the coset profile `S_K`, which counts size plus
    distance from `K`, and the relative Følner function `Φ_K` cannot both be elementary.
  - *Consequence for P1.* Any witness that P2 makes amenable pays Moore's tower. It pays either in the Følner sets
    of `F/K`, through their size or their distance from the base coset, or in Følner sets of `K` measured
    against `F`-length. If `F/K` has polynomial growth, the tower lands on `K`.
  - *Where it dies.* This is not a kill of P1, which is qualitative. It kills the constructive class: an explicit
    `K` with elementary coset Følner sets, together with a bounded-depth, undistorted or otherwise
    elementary-Følner proof that `K` is amenable. That combination would build elementary Følner sets of `F` by
    Theorem 1.
- **Exact content of the route (swarm-0917-w20-w20-f-last1, 2026-09-20).** The aim was to compute what
  `P1 ∧ P2` actually asserts, as a last-mile check on whether this route can finish the goal.
  - *Established* (`f-exotic-co-amenable-route-is-amenability-plus-not-brin-sapir`). For every family `S` of
    subgroups, "some member is co-amenable" together with "every member is amenable" is equivalent to
    `A ∧ (S ≠ ∅)`. Consequences:
    - `P1 ∧ P2 ⟺ A ∧ ¬BS`;
    - given `A`, `P1 ⟺ ¬BS` and `P2` holds;
    - under the Brin–Sapir conjecture `P1` is false whatever `A` is.
  - *Correction.* The route node says each prerequisite is weaker than the target. That holds for `P2`,
    but not for `P1`: `A ⇒ P1` is equivalent to `A ⇒ ¬BS`, which is open. So the route is not known to be
    necessary for `A`. Over `A`, its only extra content is the refutation of Brin–Sapir.
  - *Where it dies.* At `P1`, whenever `BS` holds. That is the believed world (`zaremsky-2-03-brin-sapir-conjecture`
    is open, and Brin's Question 2 in Bleak–Brin–Moore, arXiv 1711.10998, is unresolved as of 2026-09).
    Every family variant (F-free, finitely generated, unconfined, and so on) dies the same way, by item 6
    of the new node.
  - *Payoff for the goal.* Together with item 4 of the sandwich claim, every open leaf toward
    `thompson-f-is-amenable` is either root-equivalent or proves `¬BS`. A Brin–Sapir-neutral decomposition
    has to leave co-amenable induction and twisted embeddings entirely.
