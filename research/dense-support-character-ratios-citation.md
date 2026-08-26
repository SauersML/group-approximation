---
rg: 2
id: dense-support-character-ratios-citation
kind: route
title: Larsen--Shalev--Tiep support character bound plus the minimal degree of SL_N(2)
target: dense-support-character-ratios-of-sl-n-2-vanish
requires: []
---

# Literature import: character ratios at dense-support elements

This is not a new theorem.

**Source.**  Michael Larsen, Aner Shalev, Pham Huu Tiep, *The Waring
problem for finite simple groups*, Ann. of Math. (2) 174 (2011), 1885--1950.
Their character bound for `SL_n(q)` states that there is an absolute
constant `c>0` such that for every `g in SL_n(q)` of support `s` (the
codimension of the largest eigenspace of `g`) and every irreducible
character `chi`,

```text
|chi(g)| <= chi(1)^(1 - c*s/n).                                        (1)
```

Sharper exponents are given by Bezrukavnikov--Liebeck--Shalev--Tiep,
*Character bounds for finite groups of Lie type*, Acta Math. 221 (2018),
in terms of the Levi subgroup containing the centralizer; only the weak
form `(1)` is used here, and only in the limit `n -> infinity` with
`s/n >= delta` fixed.

**Minimal degree.**  The smallest degree of a nontrivial irreducible
complex representation of `SL_n(2)`, `n>=3`, is `2^(n-1)-1` (the
Landazuri--Seitz bound, which for `SL_n(q)` is `(q^n-q)/(q-1)` with the
listed small exceptions, none at `q=2`, `n>=3`).

**Assembly.**  For nontrivial `chi` and `supp(g)>=delta n`,
`|chi(g)|/chi(1) <= chi(1)^(-c*delta) <= (2^(n-1)-1)^(-c*delta)`, which
tends to `0` as `n -> infinity` uniformly in `chi` and `g`.  This is
`(DSC1)`.

**What is imported and what is not.**  The imported statement is `(1)`,
a bound on complex characters of finite groups.  Nothing about infinite
groups, unitary representations of infinite groups, spectral gaps, or
property `(T)` is imported.
