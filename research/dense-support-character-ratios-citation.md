---
rg: 2
id: dense-support-character-ratios-citation
kind: route
title: Larsen--Shalev--Tiep support character bound for finite classical groups
target: dense-support-character-ratios-of-sl-n-2-vanish
requires: []
---

# Literature import: character ratios at dense-support elements

This is not a new theorem.

**Source.**  Michael Larsen, Aner Shalev, Pham Huu Tiep, *The Waring
problem for finite simple groups*, Ann. of Math. (2) 174 (2011), 1885--1950,
Definition 4.1.1 and Theorem 4.3.6 (restated as Theorem 1.2.1).

They define the support of `g` to be

```text
supp(g)=min_lambda codim ker(g-lambda I),
```

where `lambda` ranges over the algebraic closure, and prove for simple
simply connected classical groups and every nontrivial irreducible character
`chi` the uniform estimate

```text
|chi(g)|/chi(1) < q^(-sqrt(supp(g))/481).                              (1)
```

Equivalently, their theorem states that for every `epsilon>0`, once the
support is sufficiently large the ratio is at most `epsilon`, uniformly in
the rank, field, element, and nontrivial character.

**Assembly.**  Take `q=2`.  If `supp(g)>=delta n`, `(1)` is at most
`2^(-sqrt(delta n)/481)`, which tends to zero uniformly in `chi` and `g`.
This is `(DSC1)`.  No minimal-degree assertion is used.

**Primary link.**
https://annals.math.princeton.edu/wp-content/uploads/annals-v174-n3-p10-p.pdf

**What is imported and what is not.**  The imported statement is `(1)`,
a bound on complex characters of finite groups.  Nothing about infinite
groups, unitary representations of infinite groups, spectral gaps, or
property `(T)` is imported.
