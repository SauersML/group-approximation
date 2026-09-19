---
rg: 2
id: finite-order-unitary-has-uniform-opnorm-gap
kind: claim
title: Nontrivial N-torsion unitaries are uniformly far from 1 in operator norm, in any C*-algebra
distinct_from:
  additive-index-instability: that is the established no-go saying additive Fredholm/rank indices are destroyed by amplification, so they cannot serve as full-norm invariants; this exhibits a full-norm invariant that survives every one of the same dilution operations, and is its positive counterpart.
  opnorm-packet-exactification-is-dimension-free: that rounds an approximate system of matrix units to an exact one with a modulus depending only on the packet size; this is a separation statement about exact torsion elements, involves no rounding, and has an explicit constant.
  finite-group-opnorm-support-profile: that fixes a finite group and stabilizes the irreducible support of a corrected operator-norm model; this fixes only an exponent, names no group, and asserts a metric gap rather than a stable invariant.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

Let `A` be a unital C*-algebra and `u in U(A)` with

```text
u^N = 1,      u != 1.                                            (TG1)
```

Then

```text
||u - 1|| >= delta_N := 2 sin(pi/N).                             (TG2)
```

So in **every** unital C*-algebra -- in particular in each `M_d(C)` and in a
norm matrix corona `Q = (prod_n M_(d_n)) / (oplus_n M_(d_n))` -- the
exponent-`N` elements form a **uniformly discrete** subset of the unitary
group, with a separation constant depending on `N` alone.

## Why this is the invariant the exclusion tests ask for

The repository's recorded no-go `additive-index-instability` says an additive
Fredholm/rank index is multiplied by `k` under `phi |-> phi tensor I_k`, so it
is not amplification stable and cannot be a canonical full-norm invariant.
`(TG2)` is the positive counterpart: it is exactly invariant under every
operation that destroys normalized quantities.

```text
||(u ⊕ 1_D) - 1||   = ||u - 1||          (large trivial summand)
||(u ⊗ I_k) - 1||   = ||u - 1||          (tensor dilution)
```

A one-dimensional nontrivial `N`-torsion block inside a `d`-dimensional
model still contributes at least `delta_N`, because the operator norm reads
the spectrum and not a rank density. No moving support is selected, no
normalization is chosen, and no trace, Hilbert--Schmidt norm, Hamming
distance, corner, lamp or Kazhdan projection occurs. Passing to a
subsequence preserves the gap, because the corona norm is a `limsup`.

The one operation that is *not* preserved is passage to an extension, where
the exponent changes; bounded exponent itself passes to subgroups and to
quotients.
