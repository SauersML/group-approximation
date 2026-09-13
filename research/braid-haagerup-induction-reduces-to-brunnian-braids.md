---
rg: 2
id: braid-haagerup-induction-reduces-to-brunnian-braids
kind: claim
title: If B_{n-1} has the Haagerup property, then B_n has it iff P_n has a cnd function proper on the Brunnian braids
artifacts:
  - research/artifacts/zp-braid-haagerup-b4-attacks-2026-09-13-part3.md
distinct_from:
  braid-haagerup-iff-punctured-sphere-mcg-haagerup: that claim transfers the property between B_n and Mod(S_{0,n+1}) at a fixed n; this is the induction step from n-1 to n, isolating the Brunnian subgroup
---

Let `n ≥ 2`, and let `Brun_n = ∩_{i=1}^n ker(P_n → P_{n−1})` be the Brunnian subgroup: the pure braids that
become trivial when any one strand is deleted. It is free and normal, and infinite for `n ≥ 3`.

If `B_{n−1}` has the Haagerup property, then `B_n` has it iff `P_n` admits a conditionally negative definite
function whose restriction to `Brun_n` is proper.

Since `B_3` has the property (`braid-groups-b2-and-b3-have-the-haagerup-property`), the smallest open case is
this: `B_4` has the Haagerup property iff `P_4` admits a cnd function proper on `Brun_4`. Every obstruction
therefore lives on the Brunnian braids.

Theorem F of `research/artifacts/zp-braid-haagerup-b4-attacks-2026-09-13-part3.md`.
