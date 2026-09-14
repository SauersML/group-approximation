---
rg: 2
id: deficiency-zero-kervaire-failure-yields-whitehead-counterexample
kind: claim
title: A Kervaire killing failure over a finitely presented group of deficiency zero is a finite counterexample to Whitehead's asphericity conjecture, and positive deficiency cannot fail at all
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that is the injectivity conjecture over all groups and all nonzero degrees; this is a theorem about what one killing failure over a presentation with no more relators than generators would produce.
  nonaspherical-subcomplex-of-contractible-2-complex-exists: that is the counterexample statement for Whitehead's conjecture; this shows that a deficiency-zero Kervaire failure would establish it, and asserts no failure exists.
  acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead: that turns a Bestvina--Brady kernel into a Whitehead-or-Eilenberg--Ganea dichotomy; this turns a Kervaire killing failure into a Whitehead counterexample outright, with no dichotomy.
  kl-counterexample-can-be-finitely-presented: that shrinks a counterexample to finite presentation data with no control on the number of relators; this concerns presentations whose relators do not outnumber their generators.
artifacts:
  - research/artifacts/ideas-bridges-2026-09-13.md
---

**ESTABLISHED** through `deficiency-zero-kervaire-failure-whitehead-proof`.
Unreviewed. No novelty is claimed: the argument is elementary and may be
folklore. No literature search was done beyond main.

Let `G` have a finite presentation `<x_1, ..., x_n | r_1, ..., r_m>` with
presentation 2-complex `K`. For `w in G * <t>` write
`G_w = (G * <t>)/<<w>>` and `deg_t(w)` for the exponent sum of `t`.

1. **Positive deficiency.** If `m < n`, then `H_1(G_w)` has rank at least
   `n - m`, so `G_w` is infinite for every `w`.
2. **Deficiency zero.** Suppose `G != 1`, `m <= n` and `G_w = 1`. Then:
   - (a) `m = n` and `deg_t(w) = +-1`;
   - (b) for any word `W` representing `w`, the presentation complex `L` of
     `<x_1, ..., x_n, t | r_1, ..., r_n, W>` is a finite contractible 2-complex
     containing `K` as a connected subcomplex;
   - (c) `pi_2(K) != 0`, and `G` has torsion. So `K <= L` witnesses
     `nonaspherical-subcomplex-of-contractible-2-complex-exists`, and the finite
     form of `whitehead-asphericity-conjecture` fails;
   - (d) `G` is neither hyperlinear nor MF.
3. **Normal-closure transfer.** Suppose `G != 1` and `G_w = 1`. Let `H` be a
   group with `G <= H`, `H = <<G>>`, and a finite presentation with at most as
   many relators as generators. Then `H_w = 1`, so item 2 applies to `H`.

**Consequence.** If the finite form of Whitehead's asphericity conjecture holds,
then `G_w != 1` for every nontrivial group `G` with a finite presentation of
nonnegative deficiency and every `w`. The graph records this as the route
`nonnegative-deficiency-kervaire-via-finite-whitehead`.

**Why it matters.** A single certified deficiency-zero killing failure settles
three roots at once:
- it refutes the unimodular Kervaire--Laudenbach conjecture;
- it refutes Whitehead's asphericity conjecture, in its finite form;
- it establishes `non-hyperlinear-group`, since by item 2(d) the coefficient
  group is a finitely presented group that is not hyperlinear.

So the Kervaire counterexample search can be restricted to deficiency-zero
presentations without losing either payoff.
