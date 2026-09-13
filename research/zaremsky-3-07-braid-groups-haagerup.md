---
rg: 2
id: zaremsky-3-07-braid-groups-haagerup
kind: claim
title: "Zaremsky Problem 3.7 resolved: do braid groups have the Haagerup property?"
root: true
distinct_from:
  every-braid-group-has-the-haagerup-property: that claim is the affirmative answer; this is the question, established by either answer
  some-braid-group-lacks-the-haagerup-property: that claim is the negative answer; this is the question, established by either answer
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3 ("Matrix groups,
braid groups, etc"), Problem 7, verbatim: "Do braid groups have the Haagerup
property?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-3-07-by-yes` requires `every-braid-group-has-the-haagerup-property`.
- **No**: `zaremsky-3-07-by-no` requires `some-braid-group-lacks-the-haagerup-property`.

Never write a `requires: []` route into this claim.

**Reading.** `B_n` is Artin's braid group on `n` strands. A countable discrete
group has the Haagerup property (is a-T-menable) when it admits a proper affine
isometric action on a real Hilbert space, equivalently a proper conditionally
negative definite function. "Braid groups have the Haagerup property" is read as
"`B_n` has it for every `n`". The standard inclusions `B_n ≤ B_{n+1}` are
injective and the property passes to subgroups, so a failure at one `n`
propagates to every larger `n`, and the affirmative answer is equivalent to the
property for all sufficiently large `n`.

**What is known.**

- `B_1 = 1` and `B_2 ≅ Z` have the property. So does `B_3`: its pure braid group
  `P_3 ≅ F_2 × Z` has index 6, and the property passes to finite-index
  overgroups.
- Property (T) fails for every `B_n` with `n ≥ 2` (the abelianization is `Z`),
  which says nothing about the Haagerup property.
- `B_4` has property RD (Barré–Pichot, arXiv:0809.0645, "The 4-string braid group
  B_4 has property RD and exponential mesoscopic rank").
- Status sweep `research/artifacts/zp-open-status-sections-2-4-2026-09-13-part2.md`
  (z-status-b, bounded search): OPEN. It reports that Charney's problem list on
  Artin groups records the Haagerup property of spherical Artin groups as open
  (from a search summary, not yet read verbatim).

## Attempts

- 2026-09-13 (z3-07-braid-haagerup): the region under this root records the
  reduction of `B_n` to the mapping class group of the `(n+1)`-punctured sphere,
  the absence of the two standard obstructions (nontrivial Kazhdan subgroups and
  Burger pairs `Z^2 ⋊ Γ` with `Γ ≤ SL_2(Z)` non-amenable), and `B_4` as the
  smallest undecided case, equivalently the point-pushing group
  `PMod(S_{0,5}) ≅ F_3 ⋊ F_2`. Details in the linked claims and artifacts.
