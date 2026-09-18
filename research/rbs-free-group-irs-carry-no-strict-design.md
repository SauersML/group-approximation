---
rg: 2
id: rbs-free-group-irs-carry-no-strict-design
kind: claim
title: A free-group invariant random subgroup satisfying the Bowen–Chapman RBS entropy criterion carries no strict automaton design
distinct_from:
  co-sofic-free-group-irs-carry-no-strict-design: that covers only co-sofic IRS, by counting with a linear bound; this covers every RBS IRS, which includes the co-sofic ones and some non-co-sofic ones, with no bound.
  non-co-sofic-free-group-irs-carry-no-strict-design: that is the open hole for all non-co-sofic IRS; this settles the hole on the non-co-sofic IRS that satisfy RBS.
  bowen-chapman-rbs-irs-surjunctivity-toolkit: that imports surjunctivity for Bowen–Chapman's continuous automata on Dom(pi); this proves that a strict design yields such an automaton that is injective almost everywhere and not surjective.
artifacts:
  - research/artifacts/rbs-irs-strict-design-bridge-2026-09-18.md
---

**ESTABLISHED** by `rbs-irs-strict-design-bridge-proof`, which imports Bowen–Chapman Theorem 3.6. The bridge
step is elementary, and no novelty is claimed for it.

**Setting.** Designs, `eps_D` and `delta_D` are as in `research/artifacts/irs-surjunctivity-heretic-2026-09-17.md`,
Section 2. RBS is Bowen–Chapman Definition 3.5, quoted in `bowen-chapman-rbs-irs-surjunctivity-toolkit`.

**Theorem.** Let `pi` be an IRS of `F_r` that satisfies RBS. Then no design `D` has `eps_D(pi) = 0 < delta_D(pi)`.

**Consequences** (artifact Sections 2–3).
- *Co-sofic case.* Bowen–Chapman Corollary 5.4 gives a second, qualitative proof of
  `co-sofic-free-group-irs-carry-no-strict-design`.
- *Where a counterexample must live.* Any IRS refuting `non-co-sofic-free-group-irs-carry-no-strict-design`
  fails RBS. So its Bernoulli bundle has relative Rokhlin entropy below `log|Sigma|` for some finite `Sigma`.
  In every convex splitting of such an IRS, the witness lives on the non-RBS components.
- *Obstruction.* Proving the hole by "every IRS satisfies RBS" is dominated. At the atomic IRS `1_N` that
  hypothesis becomes maximal Bernoulli Rokhlin entropy for `F_r/N`. So it implies
  `bernoulli-rokhlin-entropy-maximal-for-every-group`, which gives the goal directly through
  `gottschalk-via-maximal-bernoulli-rokhlin-entropy`.
