---
rg: 2
id: paired-prefix-joint-rank-proof
kind: route
title: Truncate the common transcript and bound the concatenated row space
target: paired-prefix-shears-have-bounded-joint-approximate-rank
requires:
  - bounded-prefix-decision-cost-forces-bounded-approximate-rank
  - low-rank-weyl-tables-have-polynomial-models
---

Fix `k` and replace the output vector by zero whenever the common procedure
has not stopped after `k` symbols.  The edited vector table is determined by
the two length-`k` prefixes.  In particular, if two row words `u,u'` have
the same length-`k` prefix, then their complete concatenated rows

```text
(K_n'^1(u,v),...,K_n'^b(u,v))_(v in {0,1}^n)
```

agree.  There are at most `2^k` row prefixes, so the horizontal
concatenation has rank at most `2^k`.  Each component row space has the same
bound, giving the weaker sum estimate `(PPR4)`.

All component tables are changed on the same event `{L_n>k}`.  Markov's
inequality gives

```text
Pr(L_n>k)<=C/k.
```

Taking `k=ceil(C/epsilon)` proves `(PPR3)`.  Chebyshev's inequality with
the second moment gives the stated square-root cutoff.

For each fixed `b`, regard the horizontal concatenation as a rectangular
pairing table.  Add `b-1` zero row blocks to make it square, apply the
low-rank Weyl model theorem once, and then discard the auxiliary row
families.  The resulting restricted model uses one common central sign for
every output coordinate.  Its exponent depends on `b,C,epsilon` but not on
the prefix depth or label count.  This is precisely the claimed paired-phase
escape.
