---
rg: 2
id: stw01-ii1-awstar-factors-are-monotone-complete
kind: claim
title: Every type II_1 AW*-factor is monotone complete
distinct_from:
  stw01-quasitrace-crux-is-awstar-factor-w-star: that asks every II_1 AW*-factor to have a large W*-corner, which is equivalent to Problem I; this asks only for monotone completeness, which W*-factors have and which does not by itself force W*.
  stw01-kaplansky-2q-pedersen-retract-equivalence: that establishes the four-way equivalence for Problem I; this is the monotone-completeness half of a two-part decomposition of its first assertion.
artifacts:
  - research/artifacts/stw01-host-survey-2026-09-12.md
---

Every type `II_1` AW*-factor `M` is monotone complete: every norm-bounded
upward-directed family in `M_sa` has a least upper bound in `M_sa`.

This is Question 6.4 of Gow, arXiv:2601.04431v2. It is the type `II_1` factor case
of the monotone completeness conjecture (Arulseelan–Hanson arXiv:2609.10218,
Conjecture 1.3; Gow Conjecture 1.4). It is implied by Problem I, because W*-factors
are monotone complete. Together with `stw01-monotone-complete-ii1-awstar-factors-are-w-star`
it implies Problem I (`stw01-problem-i-via-monotone-complete-ii1-factors`).

Known context:
- commutative AW*-algebras are monotone complete;
- properly infinite AW*-algebras are monotone sequentially complete
  (Christensen–Pedersen 1984), which does not reach finite type;
- every AW*-algebra is normal (Saitô–Wright 1991 for factors, Arulseelan–Hanson
  2026 in general), a strictly weaker property about projections only;
- Arulseelan–Hanson Theorem B reduces the consistency of a counterexample to
  factors, but not to type `II_1` factors.

## Attempts

- **Use the dimension-function quasitrace as a normal functional.** A type `II_1`
  AW*-factor carries a unique normalized quasitrace, completely additive on
  orthogonal projections. Locating the supremum of a non-commuting increasing net
  `(x_i)` needs control of `tau(x_j - x_i)` by `tau(x_j) - tau(x_i)`, which is
  additivity, i.e. Problem I itself. Dies there.
- **Normality.** Normality gives the least upper bound only for directed families
  of projections. A bounded increasing net of self-adjoints has non-monotone
  spectral projections, so normality never applies to it. Dies.
- **MASA completeness** (Saitô–Wright characterization: every MASA of an
  AW*-algebra is monotone complete). A commuting net has a supremum inside a MASA,
  but a non-commuting increasing net lies in no MASA. Dies.
