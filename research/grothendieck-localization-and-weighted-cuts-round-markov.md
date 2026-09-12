---
rg: 2
id: grothendieck-localization-and-weighted-cuts-round-markov
kind: route
title: Localize the defect and peel low-boundary sets using the original reversible kernel
target: symmetric-markov-near-idempotents-round-to-partitions
requires: []
artifacts:
  - research/artifacts/symmetric-markov-partition-rounding-2026-09-08.md
---

For `0<delta<=1`, the complex commutative little-Grothendieck theorem
supplies a probability weight controlling `D=K^2-K`. Remove the atoms
where its density relative to `mu` exceeds `delta^(-2/5)`. Their
total mass is at most `delta^(2/5)`, and every function supported
outside them satisfies

```text
||Df||_2 <= c delta^(4/5)||f||_2,       c=2/sqrt(pi).
```

This is a restriction on inputs to the ORIGINAL operator, not a
compression. Weighted coarea applied to `K 1_T` gives a set `U` with

```text
b(U) <= 3 sqrt(3c) delta^(2/5) mu(T),
mu(U symmetric_difference T) <= 18 b(T),
b(S)=sum_(i in S,j outside S) mu_i K_ij.
```

At each stage choose a nonempty set `T` of minimum mass among
the remaining sets with `b(T)<mu(T)/36`, and remove the part
of `U` still remaining. Minimum mass ensures expansion for
every subset of the new block of at most half its mass.
Charging each cross-block edge at its earliest removed endpoint
bounds the sum of all block boundaries by
`[2+12 sqrt(3c)]delta^(2/5)`. Exceptional atoms become singleton
blocks.

A weighted Cheeger estimate for zero extensions of the positive
and negative parts about a block median gives a variance bound
with an explicit exterior-boundary error. Applied to `Kx`, it
uses `E_K(Kx)<=delta` for every contraction `x`. Symmetry also
cancels the internal flow in every block average of `(K-I)x`.
Together these give

```text
||K-E_Pi||_(infinity->2)
 <= 36 sqrt(2delta+16beta)+2sqrt(beta)
 <= (36sqrt(402)+10)delta^(1/5)
 < 750delta^(1/5),
beta=sum_(P in Pi) b(P).
```

Zero defect is the exact finite Markov projection case; defect above
one has the trivial bound two. Diagonal restriction and embedding
preserve the mixed norms exactly. Self-adjointness makes any UCP
map with commutative range factor through a containing maximal
abelian algebra, giving the matrix-channel corollary.

The only imported estimate is the commutative little-Grothendieck
theorem, with its complex constant as stated in
[Kalenda--Peralta--Pfitzner, Theorem A](https://arxiv.org/html/2002.12273).
The set-repair and peeling method is related to
[Kun, Theorem 3, implication (2) to (3)](https://arxiv.org/html/1606.04471v5).
The artifact proves the full weighted argument, including all boundary
charges, rather than importing a bounded-degree decomposition theorem.
