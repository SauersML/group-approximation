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
  - research/artifacts/gk-vf-positive-b-verification-2026-09-12.md
---

**ESTABLISHED** by `linear-sofic-rank-implication-per-datum-proof`. w4-vf-positive-b re-derived it
independently and it passed (Section 4 of its verification artifact).

Let `F` be a field and `D` a strict datum, with free group `F(D)`, forward relators `R_f(D)` and reverse words
`W_r(D)` as in `metric-ultraproduct-bounded-width-closure-2026-09-12.md`. The following are equivalent.
- `W_r(D)` meets the `F`-linear sofic reflection kernel `N_lin(F)(D)`.
- No `F`-linear sofic group realizes `D`.
- Some `w` in `W_r(D)` has this property: for every `eps > 0` there is `delta > 0` such that every tuple
  `rho: F(D) -> GL_n(F)`, of any dimension `n`, whose forward relators all satisfy `rk(rho(r) - 1) <= delta n`,
  also satisfies `rk(rho(w) - 1) <= eps n`.

**Consequence.** `linear-sofic-groups-are-surjunctive` holds iff, over every prime field, every strict datum has
such a reverse word. The rung is a statement about matrix tuples and group words only. The rules `mu` and `nu`
enter only through which data are strict.

**Neighbouring rungs.** Suppose one reverse word `w` has bounded conjugacy width `b` over the forward relators, which
is the weakly sofic rung. Then over every field it satisfies the stronger linear control
`rk(rho(w) - 1) <= b max_r rk(rho(r) - 1)`.
- **Over a finite field:** apply the rank length inside the finite group `rho(F(D))`.
- **Over any field:** specialize the finitely generated coefficient ring of the tuple at a maximal ideal that
  misses a maximal nonzero minor of `rho(w) - 1`.
  - The residue field is finite, the generators stay invertible, and the rank of `rho(w) - 1` is unchanged.
  - Relator ranks can only drop.
  - Sources: artifact Remark 1.4, and w4-vf-positive-b Section 4.1.4.

Whether the rank implication implies linear control is open.

## Attempts

Established; artifact Section 1, Theorem 1.2.
