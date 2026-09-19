---
rg: 2
id: inner-tensor-agreement-is-amplification-stable
kind: claim
title: Random inner tensor codes have quantitatively strong agreement under arbitrary amplification
distinct_from:
  collective-sheaf-cofilling-for-good-ltc: that is the global common-cofilling conclusion; this is the one quantitative local lemma left after amplifying the sheaf criterion.
  collective-cofilling-is-common-erasure-cleaning: that identifies global collective filling with erasure cleaning; this concerns the complete-bipartite row-column link of one inner tensor code.
---

For arbitrarily large inner length `D`, let `C_A,C_B<=F_2^D` be positive-
rate, positive-distance inner codes of the kind used in the First--Kaufman
double-Cayley sheaf.  For every finite auxiliary vector space `V`, consider
row labels

```text
r_a in C_B tensor V  (a in [D])
```

and column labels

```text
c_b in C_A tensor V  (b in [D]).
```

Let `E` be the set of cells `(a,b)` where the `b`-component of `r_a`
differs from the `a`-component of `c_b`.  The required quantitative
amplified agreement statement is that there is a constant `kappa_*>0`,
independent of `D` and `V`, and matrices

```text
m_v in C_A tensor C_B, one for every basis coordinate v of V,
```

such that the union of row and column blocks on which the corresponding
row/column ensembles differ from `(m_v)` has size at most
`kappa_*^(-1)|E|`.

Equivalently,

```text
inf_(D,V) cbe_0(link_D, F_link_D tensor V)>0.            (ATI1)
```

for the sheaf on the complete bipartite `A`--`B` link, using block-support
Hamming norm.  Equivalently again, ordinary agreement testability must hold
uniformly after every scalar extension/direct sum, where one amplified
symbol is counted once whenever any component is nonzero.

For the First--Kaufman application, a constant in `(ATI1)` is stronger than
necessary.  With inner degree `D` and Cayley eigenvalue
`lambda=Theta(D^(-1/2))`, the inequality in their Theorem 8.10 only needs
the amplified local constant to dominate `sqrt(lambda)=Theta(D^(-1/4))`.
The trivial finite-link estimate below is `Theta(D^(-1))` and is therefore
quantitatively insufficient.

First--Kaufman arXiv:2403.19388, Lemma 9.4, identifies the unamplified
`cbe_0` with ordinary agreement testability.  Their input theorem from the
good-LTC construction supplies only that one-summand estimate.  The
product-expansion/robust-testability results of Kalachev--Panteleev,
arXiv:2206.09973, likewise state scalar Hamming inequalities and do not state
the uniform block-support scalar-extension estimate `(ATI1)`.

Primary sources:

* https://arxiv.org/abs/2403.19388
* https://arxiv.org/abs/2206.09973

## Attempts

* **Expand into scalar components and repair separately.**  Each component
  costs `O(|E|)`, but the repaired row/column supports can be disjoint; their
  union loses a factor `dim(V)`.
* **Use bounded size of each local link.**  This gives the trivial bound
  `K=O(D)`, uniform in `V`.  It is too weak for the published
  local-to-global parameters: the available Cayley eigenvalue is
  `Theta(D^(-1/2))`, whereas inserting this crude local constant in
  Theorem 8.10 requires substantially stronger expansion.
* **Invoke ordinary product expansion.**  The scalar theorem is precisely
  the `dim(V)=1` case.  Block-support distance to the amplified kernel is a
  simultaneous/generalized-support quantity and does not follow by choosing
  one scalar component.
