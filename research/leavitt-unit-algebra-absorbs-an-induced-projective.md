---
rg: 2
id: leavitt-unit-algebra-absorbs-an-induced-projective
kind: claim
title: A free module over F_2 of the binary Leavitt unit group absorbs a nonzero module induced from a finite subgroup
refuted_by:
  - leavitt-unit-group-surjunctive
distinct_from:
  leavitt-unit-group-algebra-not-directly-finite: that asks for a one-sided inverse in F_2[U] itself; this asks for one in some matrix ring M_n(F_2[U]) whose defect module is induced from finite subgroups. Neither statement implies the other as written, and only this one also breaks Bernoulli classification over U.
  leavitt-module-dual-actions-are-self-squares-off-bernoulli: that is exact doubling over U through Leavitt modules, which never gives a Bernoulli factor; this is absorption inside the group algebra, where the absorbed factor is co-induced and becomes Bernoulli after one product.
---

**OPEN.** Let `L = L_(F_2)(1,2)` and `U = L^x`. There are `n >= 1`, finite subgroups `F_1, ..., F_r <= U`
and finite-dimensional `F_2[F_i]`-modules `Q_i`, not all zero, with

    F_2[U]^n ≅ F_2[U]^n ⊕ ⊕_i F_2[U] ⊗_(F_2[F_i]) Q_i.

The smallest shape is in Section 4 of `research/artifacts/bernoulli-negative-induced-absorption-2026-09-12.md`.
Take `c = e_(00,01) + e_(01,10) + e_(10,00) + e_(11,11)`, a unit of order 3, and ask for
`F_2[U]^n ≅ F_2[U]^n ⊕ F_2[U](c + c²)`. Equivalently, `I_n ⊕ 0 ~ I_n ⊕ (c + c²)` in `M_(n+1)(F_2[U])`.

**Payoff.** By `induced-projective-absorption-breaks-bernoulli-classification`, the Bernoulli shifts over `U`
with base entropies `n log 2` and `n log 2 + rho log 2`, where `rho = sum dim Q_i/|F_i|`, would be isomorphic.
In the smallest shape `rho = 2/3`. This would prove `some-group-has-isomorphic-bernoulli-shifts-of-different-entropy`,
over `U` and over every countable group containing `U`. The pair of entropies is not `log 2, log 3`, so it
does not answer Seward's specific question about the 2-shift and the 3-shift.

**Refutation.** If `U` is surjunctive, then `F_2[U]` is stably finite, and this fails.

## Attempts

- **Quotient.** In `L` every nonzero idempotent `e` satisfies `L ≅ L ⊕ Le`, since the monoid of
  projectives of `L` is `{0, [L]}`. So the relation holds with `n = 1` in the quotient `F_2[U] -> L`. The
  obstacle is lifting, the same obstacle as for `leavitt-unit-group-algebra-not-directly-finite`
  (`direct-finiteness-not-inherited-by-quotients`).
- **Filters proved** (artifact Section 3).
  - No `Q_i` has a trivial quotient, by augmentation. This excludes the permutation modules `F_2[U/F]`,
    in particular `F_2[U](1 + c + c²)`.
  - If every `|F_i|` is odd, then `rho = 0` in `F_2`. The value `rho = 2/3`, from `F_4`, passes.
  - Sofic quotients give no further filter, because `U` is simple (as recorded in
    `bernoulli-entropy-counterexample-constraints`).
- **Consequences it would force.**
  - `U` is not surjunctive.
  - `h^Rok_sup(U) = 0`, by `rokhlin-supremum-dichotomy-with-centralized-self-copies`.
  - The collapse subgroup `D(U)` is nonzero.
- **Not attempted yet.** Lift the Leavitt matrix units `s_u t_v` through the finite subgroups
  `GL_(2^k)(F_2) <= U`. For odd-order `F`, `F_2[F]` is semisimple and `e_c` is central in `F_2[<c>]`.
