---
rg: 2
id: partial-schreier-completion-preserves-sofic-loss
kind: claim
title: Near-total partial generator bijections can be completed to permutations with only linear Hamming loss
---

Let `S` be a fixed finite generator alphabet and `X` a finite set of size
`N`.  For each `s in S`, let

```text
sigma_s : D_s -> R_s
```

be a bijection between subsets with

```text
|X\D_s|, |X\R_s| <= eta N.
```

Extend each `sigma_s` arbitrarily to a permutation `bar_sigma_s of X`.
For every word `w=s_1...s_L`, the completed word map can differ from the
partial word map on at most `L eta N` roots on which the latter comparison is
otherwise meaningful.

Consequently, for a fixed finite multiplication/relator window of maximum
word length `L_0`:

- if all tested partial relations fail on at most `theta N` roots, their
  completed permutation relations fail on at most
  `(theta+2 L_0 eta)N` roots (and `theta+L_0 eta` for a relator against the
  identity); and
- if every tested nontrivial partial word moves all but `theta N` roots, the
  completed permutation word moves all but
  `(theta+L_0 eta)N` roots.

Hence a coupled **near-perfect** partial Schreier model is already sufficient
for soficity after `eta,theta -> 0`.  Exact perfect matchings, absorption, and
finite divisibility conditions are conveniences for a construction, not
logical requirements of the spherical route.
