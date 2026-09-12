---
rg: 2
id: positive-rokhlin-entropy-makes-leavitt-units-surjunctive
kind: claim
title: If the binary Leavitt unit group has a free ergodic action of positive Rokhlin entropy, it is surjunctive
distinct_from:
  leavitt-unit-group-nonsurjunctive: that seeks an injective nonsurjective automaton over the group; this shows any such automaton forces every free ergodic action of the group to have zero Rokhlin entropy.
  sofic-radical-localizes-garden-of-eden-windows: that runs Gromov--Weiss counting along permutation models and is vacuous over this group; this uses Rokhlin entropy, which needs no models.
artifacts:
  - research/artifacts/rokhlin-entropy-self-copy-dichotomy-2026-09-12.md
---

Let `U = L_(F_2)(1,2)^x`. Then:

1. `h^Rok_sup(U)` is `0` or `infinity`;
2. POS(`U`), INF(`U`) and RBS(`U`) are equivalent;
3. if `U` admits one free ergodic p.m.p. action with positive Rokhlin entropy, then `U` is surjunctive and `K[U]` is directly finite for every field `K`.

**Contrapositive, for the counterexample lanes.** Suppose there is an injective nonsurjective cellular automaton over `U`, or a one-sided inverse in `K[U]` for some field `K`. Then every free ergodic p.m.p. action of `U` has Rokhlin entropy zero. This includes every Bernoulli shift, with finite or infinite base. `U` would then fail Seward's statement POS, and we know of no group proved to fail POS.

**Why `U` qualifies.** The maps `a -> s_0 a t_0 + s_1 t_1` and `b -> s_0 t_0 + s_1 b t_1` embed `U x U` in `U`. The `2^n` matrix units `s_u t_v`, with `|u| = |v| = n`, embed `GL_(2^n)(F_2)` in `U`. Proof: Section 2 of the artifact.

This does not prove that `U` is surjunctive. The entropy hypothesis is the open claim `leavitt-unit-group-has-positive-rokhlin-entropy-action`.
