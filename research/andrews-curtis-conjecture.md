---
rg: 2
id: andrews-curtis-conjecture
kind: claim
title: Every balanced presentation of the trivial group is Andrews–Curtis equivalent to the trivial presentation
distinct_from:
  stable-andrews-curtis-conjecture: that allows adding and removing a generator together with a trivial relator; this allows only the moves (AC1)–(AC3) in a fixed number of generators
artifacts:
  - research/artifacts/hl-andrews-curtis-status-2026-09-13.md
---

**OPEN.** Let ⟨x_1, …, x_n | r_1, …, r_n⟩ be a presentation of the trivial group.
The conjecture says it can be transformed into ⟨x_1, …, x_n | x_1, …, x_n⟩ by the
moves:
- (AC1) replace r_i by r_i r_j with i ≠ j;
- (AC2) replace r_i by r_i^{-1};
- (AC3) replace r_i by g r_i g^{-1}, where g is a generator or its inverse.

The move list is the one printed in Shehper et al., arXiv:2408.15332v2,
`sec/conjecture.tex`; see the artifact.

## Frontier (pins in the artifact)

- **Total length at most 13:** by
  `short-balanced-trivial-presentations-are-trivial-or-ak3`,
  every two-generator presentation of total relator length ≤ 13 is AC-trivial or
  AC-equivalent to AK(3) = ⟨x, y | x^3 = y^4, xyx = yxy⟩. So AK(3) is the unique
  minimal potential counterexample in rank 2.
- **Search negatives:** they are reported, but none is an AC-inequivalence
  proof.
  - Panteleev–Ushakov: no trivialization of AK(3) through relators of length up
    to 20, as reported by Shehper et al.
  - Carreras (arXiv:2607.23611) excludes bottleneck-≤26 corridors in the
    GS-substitution graph between AK(3) and two length-14 Miller–Schupp
    holdouts.
- **Stable version:** stable AC-triviality of AK(3) is itself OPEN
  (`ak3-is-stably-ac-trivial`). The 2024 argument rested on a misprinted
  presentation.

## Attempts

1. **Invariants (this lane, 2026-09-13).** Every standard homotopy or K-theoretic
   invariant is constant on balanced presentations of the trivial group. A
   separating invariant must be rank-sensitive, and none is known. This is an
   observation, not a theorem.
2. **Bounded exhaustive search (this lane).** A total-length-capped exhaustive AC
   search adds nothing beyond the per-relator length-20 negative unless the cap is
   around 30 or more. Not run.
