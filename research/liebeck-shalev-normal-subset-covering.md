---
rg: 2
id: liebeck-shalev-normal-subset-covering
kind: claim
title: Nontrivial normal subsets of finite simple groups cover the group in a logarithmic number of steps, and large Sym(n) classes cover a coset of Alt(n)
distinct_from:
  glebsky-fin-case-instantiation: that records Glebsky's use of an alternating-group covering lemma inside the sofic permanence proof; this imports the two covering theorems themselves, for all finite simple groups and for products of symmetric group classes.
---

**ESTABLISHED (literature import).**

1. **Liebeck--Shalev** (Ann. of Math. (2) 154 (2001), 383--406, Theorem 1.1). There is an
   absolute constant `c` such that if `S` is a nontrivial normal subset of a nonabelian
   finite simple group `G`, then `S^k = G` for every integer `k >= c log|G| / log|S|`.
2. **Rodgers** (Comm. Algebra 30 (2002), 425--435, Corollary 2.4). If `C_1, ..., C_k` are
   conjugacy classes of `Sym(n)`, `n >= 5`, and `prod_i |C_i| > n^(6(n-2))`, then
   `C_1 ... C_k` equals `Alt(n)` or `Sym(n) \ Alt(n)`.
3. **Minimal degrees** (Landazuri--Seitz, as stated by Nikolov--Pyber). There is an absolute
   `c > 0` such that the minimal degree of a nontrivial representation of a finite simple
   group of Lie type of rank `r` over `F_q` is at least `c q^r`.

A normal subset is a union of conjugacy classes. Item 1 is the diameter bound used for
products of conjugates of one element. Item 2 handles parity in symmetric groups with an
explicit constant.

Source status: `liebeck-shalev-normal-subset-covering-citation`.
