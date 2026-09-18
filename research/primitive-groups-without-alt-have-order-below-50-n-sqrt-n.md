---
rg: 2
id: primitive-groups-without-alt-have-order-below-50-n-sqrt-n
kind: claim
title: A primitive permutation group of degree n not containing A_n has order below 50 n^sqrt(n)
distinct_from:
  liebeck-shalev-normal-subset-covering: that claim imports covering numbers of normal subsets (and cites Maroti--Pyber); this is the order bound for primitive groups, Maroti 2002 Corollary 1.1(ii).
---

Let `G` be a primitive subgroup of `S_n`. If `G` does not contain `A_n`,
then `|G| < 50 * n^(sqrt n)`.

In particular `log |G| = O(sqrt(n) log n)`, far below the exponential
entropy `n log m` needed by the pull-back moment bound in the Rich 2-to-1
analysis.
