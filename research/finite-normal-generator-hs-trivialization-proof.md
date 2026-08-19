---
rg: 2
id: finite-normal-generator-hs-trivialization-proof
kind: route
title: Telescope a finite conjugacy generating set and average the representation
target: finite-normal-generator-hs-trivialization
requires: []
---

Because `g` normally generates the finite group `G`, finitely many conjugates
of `g` and `g^-1` form a symmetric generating set `S`.  Let `L` be the diameter
of the finite Cayley graph `Cay(G,S)`.

Put

```text
delta = ||pi(g)-1||_2.
```

For every `s in S`, unitary conjugation invariance gives

```text
||pi(s)-1||_2 = delta.
```

If `x=s_1 ... s_l` is a shortest `S`-word, then `l<=L` and the usual unitary
telescoping identity gives

```text
||pi(x)-1||_2
 <= sum_(j=1)^l ||pi(s_j)-1||_2
 <= L delta.                                           (1)
```

Average `(1)` over `x in G`.  Since

```text
Q_pi=(1/|G|)sum_x pi(x)
```

is the orthogonal projection onto the invariant vectors,

```text
||1-Q_pi||_2
 = ||(1/|G|)sum_x (1-pi(x))||_2
 <= (1/|G|)sum_x ||1-pi(x)||_2
 <= L delta.
```

Finally `1-Q_pi` is itself a projection, so for normalized matrix trace

```text
tr_d(1-Q_pi)=||1-Q_pi||_2^2 <= L^2 delta^2.
```

The constant depends only on the fixed finite pair `(G,g)` and is therefore
unchanged under arbitrary matrix amplification.  This proves both asserted
bounds.
