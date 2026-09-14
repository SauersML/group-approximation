---
rg: 2
id: dyadic-derived-full-groups-no-uniform-semifree-diameter
kind: claim
title: If an infinite minimal subshift has constant dyadic towers with bounded induced alphabets, its derived topological full group has no uniform semi-free diameter
artifacts:
  - research/artifacts/sk-rauzy-intermediate-2026-09-14-part1.md
distinct_from:
  dyadic-tower-subshift-full-group-non-uniform-growth: that is the growth clause of Cornulier's question 7 (ω([[T]]′) = 1); this is its semi-free-diameter clause, derived from it.
  dyadic-substitution-derived-full-groups-non-uniform-growth: that is the growth clause for dyadic substitution subshifts; this is the semi-free-diameter clause for the wider tower class.
---

**ESTABLISHED (unreviewed; sk-rauzy-intermediate).**
- **Statement.** Let `(X,T)` satisfy the hypotheses of `dyadic-tower-subshift-full-group-non-uniform-growth`: (H1) and (H2) at infinitely many scales. An example is every primitive substitution of constant length 2 with a non-periodic fixed point. Then for every `N ≥ 1` there is a finite generating set of `[[T]]′` whose `N`-ball contains no pair of elements freely generating a free semigroup.
- **Meaning.** The semi-free clause of Cornulier's question 7 (Bourbaki 1064, arXiv:2002.09342, source l.216) has a negative answer for these subshifts. Verbatim: "existe-t-il un entier $N$ tel que pour tout système générateur, la $N$-boule contient un couple d'éléments engendrant librement un semi-groupe libre".
- **Not covered.** The torsion-free clause ("resp. contient un élément sans torsion") stays open. The generating sets of the dyadic proof contain the shift pair `σ_n`, which has infinite order.

Route: `dyadic-derived-full-groups-no-uniform-semifree-diameter-proof`.

## Review
- **sk-verify-22 PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-22-2026-09-14.md` §1):** re-derived the count: the `2^k` positive words of length `k` in `a, b` are distinct and have `S`-length `≤ Nk`, so `γ_S(Nk) ≥ 2^k` and `ω_S ≥ 2^(1/N)`, the limit existing by submultiplicativity. The conclusion follows from `ω([[T]]′) = inf_S ω_S = 1` (`dyadic-tower-subshift-full-group-non-uniform-growth`, sk-verify-19 PASS-WITH-FIXES, whose infinitely many scales contain the good scales `m ≥ 8` of its fix F2). The hypotheses are exactly that node's (H1) and (H2) with one bound `K`. The example is its Instance, which rests on the import `mosse-bilateral-recognizability`. Read at source on MSI: `bou1064.tex` l.201–218. The outer list is `enumerate[(1)]`, l.216 is item (7), and the quote is verbatim. Subsumption scan of main (semi-free, semi-libre, free semigroup), untruncated: no node implies or refutes this claim, and the open node `topological-full-group-derived-uniform-exponential-growth` no longer calls the clause open. Fix N1 (wording, scope of an open claim): replace "The torsion-free clause ("resp. contient un élément sans torsion") stays open." with "The torsion-free clause ("resp. contient un élément sans torsion") is not answered here; the novelty check was bounded to greps of main."
