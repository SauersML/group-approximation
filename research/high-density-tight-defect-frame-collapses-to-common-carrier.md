---
rg: 2
id: high-density-tight-defect-frame-collapses-to-common-carrier
kind: claim
title: A high-density tight defect frame collapses to one common carrier
distinct_from:
  rowwise-shared-involution-forces-pairwise-marginal-closeness: that gives an L2 distance bound between two marginal involutions; this gives an exact structural collapse of any weighted tight frame when the total deleted mask mass is smaller than its carrier.
  common-meet-local-sectors-pay-one-deficit: that assumes a common local-sector meet and derives a game-energy bound; this proves that the proposed cubic frame itself creates a common negative carrier in the high-density regime.
---

**ESTABLISHED.**  In the setting of
`tight-defect-cubic-is-weighted-fusion-frame`, let `p` be the join of the
negative incidence projections and suppose `(TFF4)` holds for arbitrary
positive weights.  Compatibility gives

```text
pq_i=q_ip=r_i.                                          (HDF1)
```

Consequently

```text
l_i=p-r_i=p(1-q_i)                                     (HDF2)
```

is a projection and

```text
tau(l_i)<=tau(1-q_i).                                  (HDF3)
```

There is the following exact dichotomy:

```text
either r_i=p for every i,
or    tau(p)<=sum_i tau(1-q_i).                         (HDF4)
```

Hence whenever

```text
sum_i tau(1-q_i)<tau(p),                               (HDF5)
```

the cubic frame has no nontrivial fusion-frame geometry at all: every
column has the same range `p`, and

```text
e_iq_i=p                         for every i.           (HDF6)
```

Moreover

```text
tau(p)>=max_i(tau(e_i)-tau(1-q_i)).                    (HDF7)
```

Thus `(HDF5)` follows from the directly checkable condition

```text
sum_i delta_i < max_i(tau(e_i)-delta_i),
delta_i=tau(1-q_i).                                   (HDF8)
```

For `r` equal Frobenius deficits `delta_i=1/P` and an orientation with one
negative marginal of trace at least `1/2`, every prime

```text
P>2(r+1)                                               (HDF9)
```

lies in the collapse regime.  Column repetition, unequal positive weights,
and internal equal-angle-frame proposals do not change this conclusion.

This does not refute the affine-Frobenius CRT route: the common carrier in
`(HDF6)` could itself be the desired algebraic projection.  It does show
that, at the strict high-density scale for which the route was introduced,
the tight-frame ansatz is not a softer distributed substitute for the
projection CRT.  It reduces to constructing one literal common algebraic
negative carrier, now isolated as
`affine-frobenius-common-negative-carrier`.  Conversely that claim makes
the cubic automatic by `tight-frame-via-common-negative-carrier`.  Hence in
the high-density regime the two construction targets are equivalent.
