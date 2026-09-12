---
rg: 2
id: exceptional-endpoint-detector-products-stay-at-depth-three
kind: claim
title: Products of the exceptional endpoint detectors stay at the third depth
artifacts:
  - research/exceptional-endpoint-detector-product-fence-proof.md
  - experiments/exceptional_endpoint_detector_product_audit.py
distinct_from:
  five-return-legs-cover-hecke-detectors-not-source-gauge: that finds the three exceptional endpoint classes and audits one representative at a time against the existing probe menu; this closes their full L0-normal product subgroup.
  endpoint-detector-cell-retains-coboundary-gauge: that moves one exact third-depth detector cell through fresh endpoint Whiteheads; this asks whether products of the original fixed-source detectors already contain two adjacent depths and proves that they do not.
  signed-hecke-detectors-are-uniformly-mark-saturated-but-untyped: that returns every nonidentity detector to the mark using bounded external conjugates; this keeps every operation inside the signed actor group and tracks the endpoint columns exactly.
---

**ESTABLISHED FINITE FIXED-SOURCE FENCE.**  Let `g_A,g_B,g_C` be the
three exceptional positive signed-Hecke representatives from `(MPF4)`, with
nonidentity actor entries

```text
g_A: E_(2,9)+E_(4,6)+E_(4,9),
g_B: E_(2,6)+E_(2,9),
g_C: E_(2,6)+E_(2,9)+E_(4,6)+E_(4,9).                (EDP1)
```

Close these elements under `L_0` conjugacy and arbitrary finite products.
The result is the elementary abelian positive-character subgroup

```text
H_exc=<u,v,w> isomorphic to C_2^3,
u=x_26(1),       v=x_29(1),
w=x_46(1)x_49(1).                                     (EDP2)
```

In particular `|H_exc|=8` and `lambda_0(g)=+1` for every `g in H_exc`.
The three conjugacy classes have sizes `2,1,2` and their union generates
all of `(EDP2)`.

Let

```text
Y_m=x_(k_m,3)(b_m),       (k_1,k_2,k_3)=(7,8,9),
A_(r,m)=x_(1,r)(a_m),     r in {2,4}.                  (EDP3)
```

For a constant actor matrix `g`, the endpoint factor
`x_(r,3)(b_m)` occurs in `[g,Y_m]` exactly when the actor entry
`E_(r,k_m)` occurs in `g`.  Therefore

```text
[A_(r,m),[g,Y_m]]=z
iff the (r,k_m) entry of g is 1.                       (EDP4)
```

Every element of `H_exc` has zero endpoint entries in columns `7` and `8`.
Its complete possible endpoint-depth profiles are

```text
empty,       {(3,2)},       {(3,4)},       {(3,2),(3,4)}. (EDP5)
```

Consequently no product of `L_0` conjugates of the three exceptional
detectors gives one signed-positive ordinary actor word with mark-return
cells at depths `(1,2)` or `(2,3)`.  This remains a fixed-source statement:
all these elements act positively on the original `Q`, but none supplies
the second adjacent occurrence needed to compare gauges there.

Thus bounded multiplication inside the exceptional detector subgroup does
not avoid the moving-frame seam.  Reaching depth `1` or `2` requires a word
outside this `L_0`-normal closure, such as a non-source-preserving probe or
an endpoint Whitehead; the former changes the signed source and the latter
has the already fenced coboundary gauge.  No Property `(T)`, canonical
trace, literature input, local computation, or Lean compilation is used.

DERIVATION
exceptional-endpoint-detector-product-fence-proof
