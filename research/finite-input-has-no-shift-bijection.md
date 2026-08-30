---
rg: 2
id: finite-input-has-no-shift-bijection
kind: claim
title: The trivial finitely presented decidable group has no bijection to the naturals
distinct_from:
  compilers-cannot-drop-the-decidability-hypothesis: that obstructs a hypothesis-free compiler using an infinite finitely presented group with undecidable word problem; this is a cardinality obstruction inside the stated decidable class, already at the trivial group.
---

The trivial group `1` is finitely presented and has decidable word problem,
but there is no bijection

```text
nu : 1 -> N.
```

Consequently `P=1` is a counterexample to the universal quantifier in
[[shift-higman-compiler]]; its displayed envelope `E_nu(P)` cannot even be
formed from the demanded `nu`.

This does not contradict Mallery--Zaremsky's universal Theorem 3.28.  Their
proof embeds an arbitrary finitely generated group into permutations of
`N`; the concrete regular-action construction that starts from a bijection
of the group with `N` is Example 3.31, and that example explicitly begins
with an **infinite** group.

**Primary source.** Brendan Mallery and Matthew C. B. Zaremsky,
*Houghton-like groups from “shift-similar” groups*, J. Comb. Algebra **9**
(2025), no. 3/4, 169--208, DOI `10.4171/JCA/106`, arXiv:`2202.00822`;
Theorem 3.28 and Example 3.31 (p. 194).  Source checked 2026-08-30.

