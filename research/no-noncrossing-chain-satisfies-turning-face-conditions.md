---
rg: 2
id: no-noncrossing-chain-satisfies-turning-face-conditions
kind: claim
title: No chain of a noncrossing partition lattice satisfies the four turning-face conditions together with its dual
distinct_from:
  noncrossing-partition-diagonal-links-are-cat1: that claim is the curvature statement; this one is a purely combinatorial sufficient condition for it, which may fail for some n even if the curvature statement holds
---

For every `n >= 5` there is no chain `F` of `NCP_n \ {0, 1}` such that both `F` and its Kreweras dual `F*` satisfy the
conditions I, II, III', IV of `research/artifacts/zp-braid-cat0-turning-face-reduction-2026-09-13.md`:

- I: the corank of `F` contains two consecutive integers;
- II: `F` is not universal;
- III': some gap of `F` contains two partitions failing modularity in `S(V)`;
- IV: some maximal chain `C` of `NCP_n` has `F'_i ∩ C'_i = ∅` for all `i`.

By induction on `n` with Theorem R, this claim gives `noncrossing-partition-diagonal-links-are-cat1`.

## Attempts

- `n <= 6`: HKS Lemma 4.14 excludes turning faces with a dominant-vertex version of IV (by inspection).
- `n = 7`: Jeong, arXiv:2009.09350 Theorem 1, excludes chains satisfying I, II, III (crossing version), IV together
  with the dual, by a hand enumeration of 39 families.
- Mechanical check of both variants for `n = 5, 6, 7, 8` launched on MSI 2026-09-13 (`nc_turning.py` in the lane
  directory). If it finds witnesses at `n = 8`, this claim is false as stated, and the next question is whether the
  specific chamber through the loop's midpoint can still be matched.
