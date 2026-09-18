---
rg: 2
id: co-sofic-free-group-irs-carry-no-strict-design
kind: claim
title: A co-sofic invariant random subgroup of F_m carries no strict automaton design, with a linear error bound whose constant uses balls of the 2m-regular tree
distinct_from:
  co-sofic-irs-carry-no-strict-design: that node states the same inequality with one symbol r for both the rank and R_tau + R_sigma, and its literal constant is refuted by both referee lenses; this states it with the rank m and rho = R_tau + R_sigma kept separate, and the constant uses balls of the 2m-regular tree, which the rank-m family of the lens 2 counterexample shows is necessary.
  weakly-sofic-groups-are-surjunctive: that is surjunctivity of a group through approximation of its Cayley graph; this is the unimodular-network version, where forward and reverse tables vary from site to site and a quantitative inequality between their error densities passes to weak-* limits of finite Schreier graphs.
  surjunctive-groups-are-uniformly-quantitatively-surjunctive: that is a uniform quantitative form over a surjunctive group; this bounds the reverse-bad density by a constant times the forward-bad density over every finite Schreier graph of a free group.
artifacts:
  - research/artifacts/co-sofic-irs-rank-corrected-counting-2026-09-17.md
  - research/artifacts/irs-surjunctivity-heretic-2026-09-17.md
---

**ESTABLISHED** by `co-sofic-free-group-irs-counting-proof` (elementary; no novelty claimed).

**Setting.**
- `m >= 1`, `Gamma = F_m`, `A` a finite alphabet.
- `D = (tau, sigma)` is a design of shape-dependent automata on Schreier graphs of `Gamma`, with radii
  `R_tau`, `R_sigma` (artifact `irs-surjunctivity-heretic-2026-09-17`, Section 2).
- `rho = R_tau + R_sigma`.
- A vertex is **forward-good** if `sigma tau x = x` there for every colouring, and **reverse-bad** if some
  colouring `p` of its `rho`-ball has `tau sigma p != p` there.
- For an IRS `mu`, `eps_D(mu)` is the probability that the root is not forward-good, and `delta_D(mu)`
  the probability that it is reverse-bad.
- `b_k` is the number of vertices in the radius-`k` ball of the `2m`-regular tree.
- `mu` is **co-sofic** if it is a weak-* limit of laws `mu_X` of `Stab(o)`, where `o` is uniform in a
  finite `Gamma`-set `X`.

**Theorem.** Every co-sofic IRS `mu` of `F_m` satisfies

    delta_D(mu) <= ( b_(R_tau) + b_(2 rho) |A|^(b_rho) ln|A| ) eps_D(mu).

In particular, no co-sofic IRS of a free group carries a strict design (`eps_D = 0 < delta_D`).

**Remarks.**
- The constant must depend on the rank. Referee lens 2's counterexample to
  `co-sofic-irs-carry-no-strict-design` generalises to every `F_m`, `m >= 2`, with `R_tau = 0`,
  `R_sigma = 1`, `|A| = 2` and `delta/eps = 2m - 1`. See artifact Section 4.
- This gives the co-sofic half of `free-group-irs-carry-no-strict-design` through route
  `irs-surjunctivity-via-rank-corrected-co-sofic-split`.
- For normal `N`, `delta_N` is co-sofic iff `F_m/N` is sofic. With
  `atomic-irs-strict-designs-are-nonsurjunctive-quotients` this recovers Gromov-Weiss for finitely
  generated sofic groups. That remark is not used.
