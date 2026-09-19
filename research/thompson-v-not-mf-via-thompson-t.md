---
rg: 2
id: thompson-v-not-mf-via-thompson-t
kind: route
title: T sits inside the simple group V, so full radical of T forces full radical of V
target: thompson-v-is-not-mf
requires:
  - thompson-t-has-full-mf-radical
  - thompson-v-finitely-presented-infinite-simple
  - universal-mf-quotient
---

**Imported.**  `T <= V`, as the subgroup of `V` preserving the cyclic order of
the Cantor set (Cannon--Floyd--Parry, *Introductory notes on Richard
Thompson's groups*, Enseign. Math. 42 (1996), §5–6).  This is the same
inclusion `(I1)` that `lifted-thompson-t-mf-radical-dichotomy-proof` uses.

**Proof.**
1. `Rad(V)` is normal in `V`.  By `thompson-v-finitely-presented-infinite-simple`,
   `V` is simple, so `Rad(V) = 1` or `Rad(V) = V`.
2. Suppose `Rad(V) = 1`.  By `universal-mf-quotient`, `V` is MF.  Restrict a
   faithful corona representation of `V` to `T`.  This gives a faithful corona
   representation of `T`, so `Rad(T) = 1`.  But
   `thompson-t-has-full-mf-radical` says `Rad(T) = T != 1`, a contradiction.
3. So `Rad(V) = V`, and `V` is not MF. ∎

## What this route changes

The binary-Leavitt endpoint `property-t-free-leavitt-full-mf-radical` now
follows from the single Thompson-`T` statement, through this route and
`property-t-free-leavitt-via-thompson-v-not-mf`.  That statement is also
one of the two exact conjuncts of the torsion-free hole
`lifted-thompson-t-is-not-mf`; see
`lifted-thompson-t-not-mf-via-central-eigencorners`.  The flagship
`property-t-free-manuscript-results` is thus reduced to two claims:

- `thompson-t-has-full-mf-radical`, which by itself gives the Leavitt
  endpoint;
- `lifted-thompson-t-centre-has-commutant-eigencorners`, which together with
  the first gives the torsion-free endpoint.
