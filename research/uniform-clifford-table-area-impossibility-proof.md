---
rg: 2
id: uniform-clifford-table-area-impossibility-proof
kind: route
title: Turn two table cells into a forbidden bounded centralizer commutator
target: uniform-clifford-table-area-is-impossible-for-a-fixed-finite-mark
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Write `bar_sigma_N(g)` for the element of `Gamma` represented by
`sigma_N(g)`.  The nullity of every word in `(UCT1)` gives

```text
bar_sigma_N(g) bar_sigma_N(h)=bar_sigma_N(gh).
```

In particular `bar_sigma_N(1)=1`, so `bar_sigma_N` is a homomorphism and
the image `b` of `J` is the element represented by `j`.  It is independent
of `N`, nontrivial by hypothesis, and has order two.

The homomorphism is injective.  If a noncentral `g in E_N` belonged to its
kernel, nondegeneracy of the extraspecial commutator form would give `h`
with `[g,h]=J`, forcing `b=1`.  A nontrivial central kernel element would
itself be `J` and gives the same contradiction.  Hence

```text
|bar_sigma_N(E_N)/<b>|=|E_N/<J>|=2^(2N).                 (1)
```

All these image elements centralize `b`.  Now fix `g in E_N` and abbreviate

```text
x=sigma_N(g),       y=sigma_N(Jg)=sigma_N(gJ).
```

The two table discrepancies are

```text
u=j x y^(-1),       v=x j y^(-1),
```

and each has area at most `A`.  Their product satisfies freely

```text
u v^(-1)=j x j^(-1)x^(-1)=[j,x].
```

Therefore `(UCT2)` holds.  By `(1)`, choose one word `x` from each of an
arbitrarily large number of distinct `<b>`-cosets.  These words represent
elements of `C_Gamma(b)` while all their commutators with the fixed word `j`
have area at most `2A`.

But `finite-mark-centralizer-commutator-area-is-proper` says that commutator
area with a fixed nontrivial finite-order word is proper on every section of
`C_Gamma(b)/<b>`.  The displayed family contradicts that theorem.  Thus the
data in `(UCT1)` cannot exist.

