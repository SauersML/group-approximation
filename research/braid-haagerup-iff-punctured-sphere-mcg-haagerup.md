---
rg: 2
id: braid-haagerup-iff-punctured-sphere-mcg-haagerup
kind: claim
title: For n >= 3 the braid group B_n has the Haagerup property iff the mapping class group of the (n+1)-punctured sphere does
artifacts:
  - research/artifacts/zp-braid-haagerup-reductions-2026-09-13-part1.md
distinct_from:
  pure-braid-group-is-center-times-sphere-pure-mcg: that claim is a group isomorphism for P_n; this is the equivalence of the Haagerup property for B_n and Mod(S_{0,n+1}), which uses it together with closure properties
---

For every `n ≥ 3`: `B_n` has the Haagerup property ⟺ `B_n / Z(B_n)` has it ⟺ `P_n` has it ⟺
`PMod(S_{0,n+1})` has it ⟺ `Mod(S_{0,n+1})` has it.

Consequences:

- A failure for `B_n` gives a failure for every `B_{n'}` with `n' ≥ n`. Equivalently, the property for
  `Mod(S_{0,m+1})` implies it for `Mod(S_{0,m})`.
- Zaremsky Problem 3.7 is equivalent to asking whether `Mod(S_{0,m})` has the Haagerup property for every
  `m`, a genus-zero case of the open question for mapping class groups.
- The smallest undecided case is `B_4`, equivalently `PMod(S_{0,5}) ≅ F_3 ⋊ F_2` (point pushing; §6 of the
  artifact).

Theorem B of `research/artifacts/zp-braid-haagerup-reductions-2026-09-13-part1.md`.
