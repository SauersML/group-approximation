# Finitely generated simple groups and the surjunctivity permanence closure

Lane `w3-free-pos`, 2026-09-12. Supports `fg-simple-subgroups-of-local-embedding-free-closure-are-sofic`
and `permanence-closure-contains-fg-simple-nonsofic-group`.

## 0. Why this approach

Gottschalk's conjecture is equivalent to surjunctivity of every finitely generated simple group
(`gottschalk-via-finitely-generated-simple-groups`). Every landed positive method is a permanence
operation, collected in the closure `S*` of `gottschalk-counterexamples-lie-outside-the-permanence-closure`
(operations O1–O7). That node proves that no group of `S*` contains an infinite *finitely presented* simple
nonsofic group. The finite presentation is used in exactly one step, (O3), local embeddings.

So the positive question splits:

- **Can any permanence method reach a simple nonsofic host at all?** A finitely generated simple nonsofic
  group in `S*` would be the first simple nonsofic group known to be surjunctive: a decisive positive case
  on a nonsofic simple host, which no lane has aimed at.
- **Where must it come from?** Section 1 shows it must enter through (O3) and cannot be finitely presented.

## 1. Without local embeddings, simple subgroups stay sofic

Let `S*_0` be the smallest class containing every sofic group and closed under O1, O2, O4, O5, O6, O7 of the
evasion node (subgroups; groups whose finitely generated subgroups lie in the class; finitary split
extensions; graph folds; LEF-lamp graph wreaths; split extensions with finitely generated residually finite
kernel).

**Theorem 1.** Every finitely generated simple subgroup of a group in `S*_0` is sofic.

*Proof.* Let `Q` be infinite, finitely generated, simple and nonsofic, and suppose `Q <= W` with `W` in `S*_0`.
Induct over the stages of the closure. Sofic groups contain no such `Q`, since subgroups of sofic groups are
sofic.

- **O1.** `Q` lies in an earlier-stage group.
- **O2.** `Q` is finitely generated, so `Q` itself lies in the earlier stage.
- **O4.** `W = N semidirect G` with a finitary site structure and `G` earlier. `Q ∩ N` is normal in `Q`.
  - If `Q ∩ N = 1`, the quotient map embeds `Q` into `G`.
  - If `Q <= N`, pick `q ≠ 1` in `Q`. Detection (A1) gives a site projection `p_S : N -> N_S` onto a
    residually finite group with `p_S(q) ≠ 1`. Simplicity makes `p_S` injective on `Q`, so `Q` is residually
    finite, hence sofic. Contradiction.
- **O6.** The kernel is a graph product of LEF lamps, which is sofic. So `Q ∩ kernel = 1` and `Q` embeds into
  the earlier-stage base.
- **O7.** The kernel is residually finite. Same argument.
- **O5.** `f : W -> G` is injective on every vertex group, `G` earlier. `ker f` meets every conjugate of a
  vertex group trivially, so it acts freely on the Bass–Serre tree and is free. An infinite simple group is
  not free, so `Q ∩ ker f = 1` and `f` embeds `Q` into `G`.

Each case moves `Q` into an earlier stage or gives a contradiction, so `Q` never enters. QED

No finite presentation is used anywhere: the evasion node needs it only for (O3).

**Corollary 2.** Suppose an infinite finitely generated simple nonsofic group `Q` lies in `S*`. Then
`Q` is not finitely presented, and every stage-descent of `Q` ends in an (O3) step: `Q` is locally
embeddable into groups of an earlier stage without lying in any of them.

**Corollary 3 (payoff).** Conversely, any infinite finitely generated simple nonsofic group that is locally
embeddable into `S*` is surjunctive, by (O3) (`strict-pairs-transfer-to-table-realizations`). So the door
to a positive case on a simple nonsofic host is exactly:

> an infinite, finitely generated, not finitely presented, simple, nonsofic group every finite ball of
> which embeds as a partial multiplication table into a group of `S*`.

Since nonsoficity is witnessed on a finite ball, and partial embeddings carry that ball, such a group's
witness ball already sits in a nonsofic member of `S*` (Kun–Thom wreaths, doubles, graph wreaths).
