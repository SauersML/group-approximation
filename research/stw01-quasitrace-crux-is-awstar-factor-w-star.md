---
rg: 2
id: stw01-quasitrace-crux-is-awstar-factor-w-star
kind: claim
title: 2Q is equivalent to every type II_1 AW*-factor having a large W*-corner
distinct_from:
  stw01-kaplansky-2q-pedersen-retract-equivalence: that lists four equivalents of 2Q including "every II_1 AW*-factor is W*"; this restates the target purely as possession of a large W*-corner, using that AW*-factor normality is automatic, and separates it from the weaker monotone-completeness conjecture.
  stw99-problem-i-quasitraces-are-traces: that asks whether 2Q holds; this only reformulates 2Q as an equivalent still-open corner statement and asserts neither side.
artifacts:
  - research/artifacts/stw01-awstar-normality-assessment-2026-09-12.md
---

The following are equivalent.

1. Every bounded 2-quasitrace on a unital C*-algebra is a trace (STW Problem I).
2. Every type `II_1` AW*-factor has a large W*-corner: a faithful projection
   `p` (central support `1`) with `pFp` a W*-algebra.

**Derivation.** Gow's four-way equivalence
(`stw01-kaplansky-2q-pedersen-retract-equivalence`, arXiv:2601.04431v2 Thm 4.11)
gives 1 ⟺ "every type `II_1` AW*-factor is a W*-factor". Berberian
[Ber83, Thm 3]: an AW*-algebra is W* iff it is normal and has a large W*-corner.
Every AW*-factor is normal (Saitô–Wright 1991, [SW91, Cor 4.7]; also
Arulseelan–Hanson arXiv:2609.10218 Cor 1.5, which removes normality for all
AW*-algebras). So a `II_1` AW*-factor is W* iff it has a large W*-corner, giving
1 ⟺ 2.

**Two further equivalent readings.**
- *Some nonzero W*-corner suffices.* In a factor every nonzero projection `p` is
  faithful. If `tau(p) >= 1/n`, then `M` is a corner of `M_n(pMp)`. So `M` is W*
  iff some nonzero corner `pMp` is W*.
- *A faithful CAP state suffices.* An AW*-algebra with a separating family of
  states completely additive on projections is W* (Gow arXiv:2601.04431v2,
  Corollary 3.10, after Pedersen Theorem 3.9.4, read with its proof). Conversely
  a `II_1` W*-factor has a faithful normal trace. So 2Q is equivalent to every
  type `II_1` AW*-factor admitting a faithful CAP state. Gow's introduction quotes
  Wright (J. London Math. Soc. (2) 12 (1975/76)) for the stronger form with a
  faithful state, not assumed normal. That hypothesis was not checked against
  Wright's paper.

The problem also splits into monotone completeness plus exclusion of wild `II_1`
factors: `stw01-problem-i-via-monotone-complete-ii1-factors`.

**This is a reformulation, not progress.** It asserts neither side. The corner
criterion for factors was already available from Berberian plus the 1991 factor
normality theorem, so Arulseelan–Hanson's Theorem A ("every AW*-algebra is
normal") does not advance Problem I: the reduction bottleneck is the II_1
*factor* case, where normality was never the missing ingredient.

**Strictly stronger than monotone completeness.** A W*-factor is monotone
complete, but the converse fails: wild monotone-complete factors that are not
W*-algebras exist. Hence 2Q is strictly stronger than the monotone-completeness
conjecture for II_1 AW*-factors (Arulseelan–Hanson Conjecture 1.3, factor case);
resolving that conjecture would not resolve 2Q without additionally supplying a
separating family of normal states, i.e. the large W*-corner. See
`research/artifacts/stw01-awstar-normality-assessment-2026-09-12.md`.

## Attempts

- **Feed A-H Theorem A into Gow.** Dead as an advance: at the II_1-factor
  bottleneck, normality is the 1991 Saitô–Wright theorem, so Theorem A's new
  content (non-factor AW*-algebras) never reaches the reduced problem. It yields
  only the corner reformulation above.
- **Reduce 2Q to monotone completeness of factors (A-H Conjecture 1.3 / Thm B).**
  Dead: monotone completeness is strictly weaker than W* for factors (wild
  monotone-complete non-W* factors), so this route drops the separating-normal-state
  content that 2Q needs.
