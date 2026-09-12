---
rg: 2
id: stw82-scalar-band-depth-floor
kind: claim
title: Scalar partition-of-unity subdivision cannot reduce the original colour-count depth
distinct_from:
  stw82-quasicentral-cutdowns-repair-to-banded-order-zero: that proves every individual colour can be subdivided and repaired inside hereditary spectral bands; this proves why applying that construction independently to all colours cannot by itself yield the extension maximum.
  stw82-odd-support-cycle-stable-two-colour-obstruction: that uses nonorthogonal operator supports after maps are chosen; this is a prior combinatorial obstruction for scalar band covers, independent of the target algebra.
---

Let `X` be a nonempty compact space and let `V` be a finite set of `N`
original colours.  For each `v in V`, let

```text
g_(v,1),...,g_(v,m_v) in C(X)_+
```

satisfy, for some fixed `eta>0`,

```text
sum_j g_(v,j)(t) >= eta       for every t in X.        (D1)
```

For each `(v,j)`, let `J_(v,j)` be any subset of `X` containing the cozero
set of `g_(v,j)`.  Then the total band family has depth at least `N`:

```text
sup_(t in X) |{(v,j):t in J_(v,j)}| >= N.              (D2)
```

Indeed, the stronger pointwise inequality holds at every `t`.  In
particular (D2) applies when each original colour is subdivided by a scalar
partition of unity, or even by an approximate partition whose sum stays
uniformly positive.

Therefore independent common-axis scalar subdivision of `N` outgoing
colours cannot certify fewer than `N` colours through spectral-band depth.
For an extension with finite endpoint dimensions `p` and `q`, independently
subdividing all `(p+1)+(q+1)` endpoint colours cannot by this mechanism alone
reach the desired `max(p,q)+1` colours.  Some cross-colour support
orthogonality, support-sensitive vanishing, or replacement of the maps is
logically necessary.
