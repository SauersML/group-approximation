---
rg: 2
id: full-weyl-defect-equals-pvm-transport-energy
kind: claim
title: Complete RMS Weyl defect is exactly the common-PVM transport energy
distinct_from:
  expander-pvm-transport-forces-dimension-or-mass-collapse: that converts PVM transport energy into dimension or mass collapse; this identifies that energy exactly with the complete mixed Weyl defect.
  sampled-weyl-defect-controls-common-pvm-dirichlet-energy: that must derive the complete defect from only the sparse sampled matchings.
---

ESTABLISHED.  Let `V=F_2^n` with a nondegenerate pairing, let
`U:V->U(H)` be an exact additive action with spectral PVM `(P_x)_(x in V)`,
and let `W(b)` be arbitrary unitaries.  On a common invariant marked carrier
of normalized trace `mu`, put

```text
Delta(a,b)
 =W(b)U(a)W(b)^* - (-1)^<a,b> U(a).                           (FWD1)
```

Then the exact operator-valued Parseval identity is

```text
E_(a,b) ||Delta(a,b)||_2^2
 =E_b sum_x ||W(b)P_xW(b)^*-P_(x+b)||_2^2.                    (FWD2)
```

The right side is the transport energy of the one common PVM for the
complete translation graph on `V`.  That graph has normalized spectral gap
one.  Therefore
`expander-pvm-transport-forces-dimension-or-mass-collapse` gives

```text
E_(a,b)||Delta(a,b)||_2^2
 >=2 mu (1-d/2^n).                                            (FWD3)
```

In particular, if `d<2^(n-1)`, then

```text
mu <= E_(a,b)||Delta(a,b)||_2^2.                              (FWD4)
```

Thus full average Weyl soundness already has the required
dimension-independent normalized-HS endpoint.  No individual Fourier-block
threshold, path propagation, or separately chosen context PVM appears.
