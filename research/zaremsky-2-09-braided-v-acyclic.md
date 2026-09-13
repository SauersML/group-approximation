---
rg: 2
id: zaremsky-2-09-braided-v-acyclic
kind: claim
title: "Zaremsky Problem 2.9 resolved: is the braided Thompson group bV acyclic?"
root: true
distinct_from:
  braided-thompson-group-bv-is-acyclic: that claim is the affirmative answer; this is the question, established by either answer
  braided-thompson-group-bv-has-nonzero-homology: that claim is the negative answer; this is the question, established by either answer
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 2, Problem 9, verbatim:
"Is braided V acyclic?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-2-09-by-yes` requires `braided-thompson-group-bv-is-acyclic`.
- **No**: `zaremsky-2-09-by-no` requires `braided-thompson-group-bv-has-nonzero-homology`.

Never write a `requires: []` route into this claim.

**Reading.** Braided V is the group `bV` (also written `BV`) found independently
by Brin ("The algebra of strand splitting I") and Dehornoy ("The group of
parenthesized braids"). Its elements are classes of triples `(T_-, β, T_+)`:
`T_±` are binary trees with `n` leaves, `β ∈ B_n`, and a triple is identified
with the triple obtained by adding a caret to a leaf of `T_+`, adding a caret to
the matching leaf of `T_-`, and cabling the corresponding strand of `β`.
Forgetting braids to permutations gives a surjection `bV → V`. "Acyclic" means
`H_k(bV; Z) = 0` for every `k ≥ 1`, for the discrete group `bV`.

**Status (bounded search, 2026-09-13).** No answer was found. Sources checked:
the list itself; the arXiv listings of M. Zaremsky and of X. Wu; Palmer–Wu,
arXiv:2510.16879 (labelled Thompson groups and twisted Brin–Thompson groups are
acyclic; braided groups are not treated); Skipper–Wu, arXiv:2106.08751
(homological stability for ribbon Higman–Thompson groups, no stable
computation). The status lane z-status-b also found nothing. General web
searches were exhausted before a full sweep, so the check is bounded.

**Context.**

- `V` is acyclic (Szymik–Wahl, arXiv:1411.5035; `thompson-v-is-integrally-acyclic`).
- `bV` is of type `F_∞` (Bux–Fluch–Marschler–Witzel–Zaremsky, arXiv:1210.2931).
- The quasimorphisms of `bV` (Fournier-Facio–Lodha–Zaremsky, arXiv:2204.05272)
  are bounded cohomology and do not obstruct acyclicity.

## Attempts

- 2026-09-13, degree one: `bV` is perfect (`braided-thompson-group-bv-is-perfect`).
- 2026-09-13, rational case: `H_n(bV; Q) = 0` for all `n ≥ 1`
  (`braided-thompson-group-bv-is-rationally-acyclic`, unreviewed). The kernel of
  `bV → V` has homology built from configuration modules of the Cantor set, and
  Palmer–Wu's acyclic labelled Thompson groups make those modules V-acyclic over
  `Q`. So any nonzero integral homology of `bV` is torsion.
- Integral reduction: "yes" follows from the single open claim
  `cantor-power-function-modules-are-v-acyclic`, that `C(C^j, Z)` is V-acyclic
  for all `j ≥ 1`, through the route
  `braided-thompson-group-bv-is-acyclic-from-cantor-modules`. The crux is
  2-torsion in the Lyndon–Hochschild–Serre spectral sequence of `C(C, Z^j) ⋊ V`.
- Szymik–Wahl route (open, not needed if the reduction closes): homological
  stability for the braided Higman–Thompson family plus the `E_2` group
  completion of the braided monoidal groupoid of `bV`. A heuristic coequalizer
  model of that completion is contractible, which also predicts "yes".
