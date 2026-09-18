---
rg: 2
id: juschenko-zheng-question-5-fails-for-countable-groups
kind: claim
title: The countable nonamenable group SL_2 of the real algebraic numbers acts transitively with abelian stabilizers and a non-degenerate symmetric Liouville measure, so Juschenko–Zheng's Question 5 fails for countable groups
distinct_from:
  juschenko-zheng-liouville-actions: that imports Question 5; this answers it negatively for countable, not finitely generated groups, and leaves the finitely generated case open.
  amenably-coupled-actions-admit-symmetric-liouville-measures: that is the general Liouville criterion; this applies it to an Iwasawa factorization to get abelian stabilizers.
  thompson-f-random-walks-are-not-liouville: that concerns finitely supported walks on F; this concerns a linear group and an infinitely supported measure.
---

**ESTABLISHED** through `juschenko-zheng-question-5-fails-for-countable-groups-proof`.

Let `R` be the field of real algebraic numbers, which is countable and real closed. Let `G = SL_2(R)`, viewed as a
countable discrete group, and `K = SO_2(R)`. Then:
- `G ↷ G/K` is transitive, and every stabilizer `gKg⁻¹` is abelian;
- `G` is nonamenable, and the action `G ↷ G/K` is not amenable;
- `G ↷ G/K` admits a symmetric non-degenerate Liouville measure.

So Question 5 of `juschenko-zheng-liouville-actions` ("… StabG(x) is abelian … Is G amenable?") has a negative
answer when `G` is only required to be countable. The mechanism is the Iwasawa factorization `G = BK`, with `B`
the solvable group of upper triangular matrices with positive diagonal.

**Scope.** Juschenko–Zheng fix a finite generating set. The finitely generated case is **not** settled here.
- A finitely generated counterexample by this mechanism needs a finitely generated nonamenable group in which
  every finite set of cosets of an abelian subgroup lies in one orbit of an amenable subgroup.
- Any finitely generated `G = HK` with `H` amenable and `K` abelian would do; whether such a nonamenable `G`
  exists is not decided here.
