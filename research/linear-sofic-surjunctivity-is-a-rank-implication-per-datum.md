---
rg: 2
id: linear-sofic-surjunctivity-is-a-rank-implication-per-datum
kind: claim
title: For each strict datum, no linear sofic group realizes it iff one reverse word has rank forced small by small forward relator ranks in every matrix tuple
distinct_from:
  surjunctivity-of-a-local-class-is-reflection-kernel-membership: that identifies surjunctivity of a local class with reverse words in its reflection kernel; this computes the linear sofic kernel condition as an epsilon-delta rank implication over all invertible matrix tuples.
  strict-reverse-words-lie-in-bounded-width-profinite-closures: that is the weakly sofic rung, bounded conjugacy width in finite groups; this is the linear sofic rung, a rank implication in matrix groups, which bounded width implies with constant equal to the width.
  linear-sofic-group-algebra-is-stably-finite: that passes from linear soficity to stable finiteness of the group algebra, which only sees linear automata; this is the exact linear sofic condition for every strict datum, nonlinear rules included.
artifacts:
  - research/artifacts/linear-sofic-rung-rank-implication-2026-09-12.md
---

**ESTABLISHED** by `linear-sofic-rank-implication-per-datum-proof`.

Let `F` be a field and `D` a strict datum, with free group `F(D)`, forward relators `R_f(D)` and reverse words
`W_r(D)` as in `metric-ultraproduct-bounded-width-closure-2026-09-12.md`. The following are equivalent.
- `W_r(D)` meets the `F`-linear sofic reflection kernel `N_lin(F)(D)`.
- No `F`-linear sofic group realizes `D`.
- Some `w` in `W_r(D)` has this property: for every `eps > 0` there is `delta > 0` such that every tuple
  `rho: F(D) -> GL_n(F)`, of any dimension `n`, whose forward relators all satisfy `rk(rho(r) - 1) <= delta n`,
  also satisfies `rk(rho(w) - 1) <= eps n`.

**Consequence.** `linear-sofic-groups-are-surjunctive` holds iff, over every prime field, every strict datum has
such a reverse word. The rung is a statement about matrix tuples and group words only; the rules `mu` and `nu`
enter only through which data are strict.

**Neighbouring rungs.** Bounded conjugacy width of one reverse word (the weakly sofic rung) gives the stronger
linear control `rk(rho(w) - 1) <= C max_r rk(rho(r) - 1)`, with `C` the width. Whether the rank implication
implies linear control is open.

## Attempts

Established; artifact Section 1, Theorem 1.2.
