---
rg: 2
id: conjugate-commuting-perfect-copies-force-exponential-dimension
kind: claim
title: n commuting conjugate copies of a perfect group with mark density mu need dimension two to the n mu
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  marked-clifford-table-exponential-dimension: that is the robust Pauli bound, pinned by a central involution and proved through Gowers--Hatami; this is an exact-representation bound for commuting conjugate copies of any perfect group, proved by block counting, with no central element and no robustness claim.
  approximate-gram-data-certifies-only-inverse-square-dimension: that bounds what approximate trace data can certify; this is the exact statement whose approximate version that fence limits.
---

Let `rho` be a finite-dimensional unitary representation of a group
`Gamma` on `C^d`.  Suppose `A_1,...,A_n<=Gamma` are pairwise commuting
subgroups, all conjugate in `Gamma` to `A_1`, and `A_1` is perfect.  For
`w in A_1` let `mu=(1-Re tr rho(w))/2` with the normalized trace.  Then

```text
d >= 2^(n mu).                                                   (CC1)
```

*Proof.*  `rho` restricts to a completely reducible representation of
`A_1 x ... x A_n`, a sum of tensor products of irreducibles with weights
`p_b`.  The conjugates `w_i=g_i w g_i^(-1) in A_i` all have mark density
`mu` (conjugation invariance of the trace), and on a block the density of
`w_i` is that of its `i`-th tensor factor, which is at most one and is
zero on a trivial factor.  Summing over `i`, some block has at least
`n mu` nontrivial factors, each of dimension at least two because a
perfect group has no nontrivial characters.

**Thompson's `V`.**  `V` is perfect and contains, at every depth `k`, the
`2^k` pairwise commuting cylinder copies `V_x`, each isomorphic to `V` and
mutually conjugate.  So any finite-dimensional unitary representation has
`d>=2^(2^k mu)` for every `k`, forcing `mu=0`: a quantitative form of the
absence of nontrivial finite-dimensional representations.  In the regular
representation every copy has `mu=1/2`.

**What it does for the programme.**  This is the exact form of "copy the
bad region": mark density is exactly conjugation-invariant, so deep copies
cost as much as the shallow one, and `n` copies multiply the dimension
demand exponentially.  The approximate version is governed by
`approximate-gram-data-certifies-only-inverse-square-dimension`: the block
decomposition must be recovered by exactifying the `n`-fold product from
approximate commutation and conjugation data, whose cost grows with `n`
(for `V`, the depth-`k` relations have area growing with `k`).  Optimizing
the depth against the microstate precision gives a hyperlinear-profile
lower bound of the form `d>=exp(c delta^(-a))`, the shape of Slofstra's
Clifford--HNN profile, which hyperlinearity permits.  Converting copying
into nonhyperlinearity needs fixed-precision exactification of an
unboundedly large structure, i.e. the same uniform stability input as
every other route.
