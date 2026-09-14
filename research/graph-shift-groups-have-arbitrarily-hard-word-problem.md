---
rg: 2
id: graph-shift-groups-have-arbitrarily-hard-word-problem
kind: claim
title: For every recursive time bound some two-generated group with solvable word problem beats it
distinct_from:
  novikov-boone-fp-group-undecidable-word-problem: that gives a finitely presented group with unsolvable word problem; this gives, for each recursive time bound, a two-generated group whose word problem is solvable but not within that bound.
  decidable-fp-groups-need-not-embed-in-rational-group: that imports the Kharlampovich--Myasnikov--Sapir finitely presented residually finite examples and uses a single-exponential bound; this is a self-contained construction for an arbitrary recursive bound, and its groups are not claimed finitely presented or residually finite.
artifacts:
  - research/artifacts/boone-higman-self-similar-and-complexity-2026-09-11.md
---

**ESTABLISHED.** For `A` a set of positive integers let `Gamma_A` be the
graph on `Z` with `i ~ j` iff `|i-j| in A`, and put

```text
G_A = A(Gamma_A) x| Z = < a, b | [a, b^-n a b^n] = 1  (n in A) >,   (GS1)
```

with `b` shifting the vertices. Then:

1. if `A` is decidable, `G_A` has solvable word problem;
2. for every `n >= 1`, the word `u_n = [a, b^-n a b^n]` of length `4n+4`
   is trivial in `G_A` iff `n in A`;
3. for every recursive `T: N -> N` there is a decidable `A` such that no
   deterministic algorithm decides the word problem of `G_A` over `{a, b}` in
   time `C*T(C*l) + C*l + C` for any constant `C`, where `l` is word length.

DERIVATION
graph-shift-groups-have-arbitrarily-hard-word-problem-proof
