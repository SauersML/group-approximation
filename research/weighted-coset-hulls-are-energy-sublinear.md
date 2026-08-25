---
rg: 2
id: weighted-coset-hulls-are-energy-sublinear
kind: claim
title: Arbitrary sums of regular coset displacement hulls have e-two-thirds density
distinct_from:
  displacement-carrier-has-p-fold-bs-hull: that proves the per-cell p-fold loss and only observes qualitative vanishing cellwise; this proves a uniform weighted estimate for arbitrary heterogeneous direct sums.
  regular-short-low-frequency-bs-source-hull-is-sublinear: that uses a diagonal length-frequency cutoff for arbitrary approximate sources; this gives an explicit e-two-thirds law on the canonical regular-coset displacement family with no cutoff choice.
  direct-sum-weil-compressions-have-quadratic-padding: that adds authenticated Weil boundary blocks with rank linear in energy; this treats the regular-coset flip whose legal reducing hull has an unavoidable moving p factor.
---

**ESTABLISHED.**  Take an arbitrary finite orthogonal sum of the canonical
rank-one regular-coset flips from
`displacement-carrier-has-p-fold-bs-hull`, allowing arbitrary primes and
arbitrary multiplicities.  Index the summands by `j`, write

```text
d_j=|PSL_2(F_(p_j))|=p_j(p_j^2-1)/2,
D=sum_j d_j,                                             (WCH1)
```

and let `K_j` be the smallest reducing BS carrier containing the flipped
source.  If `E` is the unnormalized sum of the two squared cubic residuals,
then

```text
E=24 N,                    N=#summands,                 (WCH2)
rank(K_j)=p_j.                                             (WCH3)
```

Consequently, with `e=E/D` and `K=(+)K_j`,

```text
rank(K)/D
 <=4^(1/3)(E/(24D))^(2/3)
 =4^(1/3)24^(-2/3)e^(2/3).                             (WCH4)
```

In particular arbitrary heterogeneous direct sums of these unbounded-loss
cells still have legal exact/reducing BS hull density tending to zero when
their normalized endpoint energy tends to zero.  Block cutting across `K`
and its image under either reflection has support rank at most
`2 rank(K)`, so its normalized-HS cost is

```text
O(sqrt(rank(K)/D))=O(e^(1/3)).                          (WCH5)
```

For this canonical family the support-changing endpoint surgery is even
more direct: replacing the flipped reflection by the original regular
endpoint reflection changes only the `N` source lines and makes every row
exact.  Formula `(WCH4)` proves that insisting on a legal reducing core
carrier is also qualitatively affordable despite the absence of any
energy-linear hull estimate.

The theorem uses additivity of the canonical one-source cells.  It does not
cover several source flips packed into one congruence block when their
three-cycle residuals overlap and can cancel.  A general legal-truncation
theorem must either decompose such packed data into odd-parity cells or
prove a replacement energy lower bound before applying `(WCH4)`.

DERIVATION
weighted-coset-hull-concavity-proof
