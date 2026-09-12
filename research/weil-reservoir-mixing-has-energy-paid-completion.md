---
rg: 2
id: weil-reservoir-mixing-has-energy-paid-completion
kind: claim
title: Arbitrarily mixed even-Weil boundary reservoirs have an energy-paid flexible completion
distinct_from:
  direct-sum-weil-compressions-have-quadratic-padding: That proves the ledger by adding blockwise cubic energies; this remains block-free after arbitrary unitary mixing of the whole deleted reservoir and gives the completion displacement directly from its rank.
  positive-fixed-corner-cubic-energy-charges-deleted-rank: That proves the positive-corner energy identity for a supplied dilation; this specializes it to all heterogeneous even-Weil reservoirs and conjoins it with the exact arithmetic completion.
  bs14-flexible-cross-packet-boundary-reconciliation: That starts from an arbitrary near-solution with no authenticated dilation; this proves the full desired conclusion once the near-solution is known to be a compression of an arbitrary mixed even-Weil reservoir.
---

**ESTABLISHED.**  Take any finite multiset of full even-Weil Iwahori
representations at primes `p=1 mod 4`, with arbitrary multiplicities and
heterogeneous levels.  Let `Q` be the direct sum of their parabolic fixed
lines, transported by any common unitary change of basis, and put `P=1-Q`.
Allow arbitrary unitary mixing of the deleted lines inside `QH`.  Compress
the exact tuple `(X,R,S)` to `PH` and polar-correct `PXP` to the involution
`X_0` as in `even-weil-fixed-line-compression`.  Write

```text
k=rank(Q),   d=rank(P),
E_cub=||(X_0S_P^2)^3-1||_F^2+||(X_0R_PS_P)^3-1||_F^2. (WRM1)
```

Then, for one absolute `c_0>0`,

```text
E_cub >= c_0 k.                                       (WRM2)
```

Restoring exactly the same `k` boundary dimensions recovers the original
exact direct sum, and the flexible generator displacement satisfies

```text
d_2(compressed,full)^2 <= C k/(d+k)
                         <=(C/c_0)E_cub/(d+k).        (WRM3)
```

Thus the sharp energy-paid boundary-dimension completion survives arbitrary
heterogeneous block sums, multiplicities, common basis changes, and all
unitary mixing internal to the deleted reservoir.  Neither determinant
cancellation nor loss of the original block labels affects it.

This is the maximal conclusion available from an authenticated Weil
dilation.  It does not cover an arbitrary near-solution whose two residual
carriers have not yet been shown to arise from such a positive fixed
reservoir.  The remaining part of
`bs14-flexible-cross-packet-boundary-reconciliation` is exactly that reverse
authentication, not the energy or completion ledger after authentication.

DERIVATION
weil-reservoir-energy-completion-proof
