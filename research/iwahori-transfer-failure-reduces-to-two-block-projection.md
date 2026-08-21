---
rg: 2
id: iwahori-transfer-failure-reduces-to-two-block-projection
kind: claim
title: Every failed Iwahori unitary transfer has a two-block projection witness
distinct_from:
  iwahori-outlier-repair: that tries to turn one low-energy operator into an invertible exact intertwiner; this replaces a failed unitary centralizer by a projection and asks only whether the second vertex mixes its two blocks.
  iwahori-transfer-equals-matricial-commutant-codensity: that identifies the limiting relative-commutant equality; this gives an exact finite-stage normal form for any sequence violating it.
---

If `iwahori-unitary-commutant-transfer` fails, then after doubling every
matrix dimension it fails with the witness unitary `v` an exact selfadjoint
involution.  Equivalently it fails with projections `P_d` such that

```text
delta_B(d)->0,
max_(c in S_C)||[P_d,pi_(d,+)(c)]||_2->0,             (TBP1)
max_(c in S_C)||[P_d,pi_(d,-)(c)]||_2 >= epsilon_0   (TBP2)
```

for one `epsilon_0>0` along a subsequence.  Conversely any such projection
sequence gives a failed unitary-transfer sequence by `v_d=2P_d-I`.

Indeed, starting with arbitrary unitary witnesses `v_d`, replace both vertex
representations by two identical copies and put

```text
J_d = [[0,v_d],[v_d^*,0]].                            (TBP3)
```

Then `J_d=J_d^*=J_d^-1`.  For every matrix `X`, with
`X~ = diag(X,X)`, the normalized Hilbert--Schmidt norms satisfy

```text
||[J_d,X~]||_2=||[v_d,X]||_2.                        (TBP4)
```

The doubled Iwahori edge defect is unchanged.  Set `P_d=(I+J_d)/2`; its
commutators are one half of those of `J_d`.

In the tracial ultraproduct, `P=[P_d]` therefore lies in the first-vertex
commutant but not in the second.  The problem is exactly whether the second
vertex can retain macroscopic off-diagonal mass across a two-block
decomposition that asymptotically reduces the first vertex and the common
Iwahori edge.  No general invertible-intertwiner repair is required.
