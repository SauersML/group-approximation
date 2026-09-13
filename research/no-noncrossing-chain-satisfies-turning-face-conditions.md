---
rg: 2
id: no-noncrossing-chain-satisfies-turning-face-conditions
kind: claim
title: No chain of a noncrossing partition lattice satisfies the four turning-face conditions together with its dual
refuted_by:
  - some-noncrossing-chain-satisfies-turning-face-conditions
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

**Refuted at n = 8** (`some-noncrossing-chain-satisfies-turning-face-conditions`, hand-checked witness
`({18} < {18, 26})`). The statement does hold for `n = 5, 6, 7` by exhaustive search.

## Attempts

- `n <= 6`: HKS Lemma 4.14 excludes turning faces with a dominant-vertex version of IV (by inspection).
- `n = 7`: Jeong, arXiv:2009.09350 Theorem 1, excludes chains satisfying I, II, III (crossing version), IV together
  with the dual. The mechanical search (`nc_turning.py`, MSI, 2026-09-13) agrees and finds none even without the dual:
  2534 chains in `NCP_7` satisfy I, II, III', and all of them fail IV.
- `n = 8`: 22268 chains satisfy all four conditions together with their duals. The next attempt weakens IV by
  allowing every pair of opposite universal vertices `(v, w)` in place of `({i, i±1}, {{i}, U_n \ {i}})`, with apartments
  as noncrossing spanning trees (HKS Proposition 4.4). The HKS Theorem 4.17 argument works verbatim for any such pair.
