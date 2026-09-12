---
rg: 2
id: three-line-first-hit-table-proof
kind: route
title: Compute the stabilized three-line first-hit character partition
target: three-line-first-hit-solves-local-morita-edge
requires:
  - murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness
---

Since `q=b+a`, the relations `a<=q` imply `ab=ba=0`.  The adaptive range
relations give `db=bd=da=ad=0`.  Therefore the three displayed stabilized
coefficients commute additively and give the finite root-table homomorphism
`(TLF1)`.  Pulling a representation back to `T_0` gives its Fourier PVM even
when that homomorphism has a kernel; characters nontrivial on the kernel have
zero projection.

For the involution

```text
W=[[1-a,sbar],[s,1-d]]
```

from `murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness`, one has
`W a_0 W=d_0` and `W d_0 W=a_0`.  Because `b a=0` and `b d=0`, direct block
multiplication also gives `W b_0 W=b_0`.  This proves `(TLF2)` and hence
transport of `Omega_a` to `Omega_d`.

Every triple other than `(0,0,0)` lies in exactly one of the two cases

```text
(u,v)!=(0,0),       or       (u,v)=(0,0) and w!=0.
```

This proves the disjoint union in `(TLF3)`.  Fourier projections belonging
to disjoint character sets of one PVM are orthogonal, so normalized trace is
additive on that union.  Unitary conjugacy preserves normalized trace, which
proves `(TLF4)`.

Finally, the full source-support set is `{(u,v,w):v!=0}`.  Its intersection
with the two spectator kernels is exactly `Omega_a={(0,v,0):v!=0}`.  No
identity above controls how a representation distributes multiplicity
between these fibers.  Therefore `(TLF5)` is precisely the remaining
estimate and is not smuggled into the algebraic calculation.
