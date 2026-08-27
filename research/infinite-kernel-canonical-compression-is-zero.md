---
rg: 2
id: infinite-kernel-canonical-compression-is-zero
kind: claim
title: No nonzero canonical group-factor compression kills an infinite subgroup
distinct_from:
  infinite-index-canonical-subgroup-corner-is-impossible: that assumes a base projection and separates cosets by zero Fourier compressions; this allows an arbitrary projection in the whole group factor and rules out killing an infinite kernel by making its compressed canonical unitaries equal the corner identity.
  affine-haar-membership-does-not-promote-irs-trace: that gives a trace mismatch for a Dirac IRS membership process; this is an intrinsic no-corner theorem in every group von Neumann algebra.
  cdi-character-cannot-be-promoted-by-regular-corners: that treats finite-support corners and an ICC character; this needs neither finite support nor ICC and applies directly to the Mihailova free-cover kernel.
---

Let `W` be a countable group and let `N<W` be infinite.  Write `u_w` for
the canonical unitaries in `L(W)`.  There is no nonzero projection
`p in L(W)` satisfying

```text
p u_n p = p                    for every n in N.       (IKC1)
```

Consequently, if `pi:G->Q` has infinite kernel and `G<W`, no positive corner
of `L(W)` can realize the quotient representation by sending the class of
`g` to the compression `p u_g p`: the kernel relation would force `(IKC1)`.

Apply this to the Mihailova coset-lamp group

```text
W = (direct_sum_Q C_2) rtimes (F_m times F_m).
```

Both free-cover kernels act trivially on the lamp coordinates, but their
canonical actor unitaries retain regular trace.  Even a projection chosen
arbitrarily in the full Bernoulli crossed product cannot turn either kernel
into the identity through canonical compression.  Thus the quotient `Q`, or
its left-right algebra, cannot be imported by the standard kernel-killing
corner.  Any non-CE inclusion in this candidate must mix canonical Fourier
grades nontrivially; it cannot be a compressed quotient of the actor copy.
