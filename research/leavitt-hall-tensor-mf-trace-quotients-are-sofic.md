---
rg: 2
id: leavitt-hall-tensor-mf-trace-quotients-are-sofic
kind: claim
title: Every Hall-tensor fold MF trace has a sofic GNS group quotient
invalidates:
  - leavitt-hyperlinear-nonsofic-via-fold-mf-trace
distinct_from:
  leavitt-presentation-double-has-all-fold-mf-moments: that constructs the continuum of MF traces and computes one fold moment; this identifies the approximation class of every resulting GNS group quotient.
  leavitt-presentation-double-fd-radical-is-fold-kernel: that computes the intersection of kernels of honest finite-dimensional unitary representations; this constructs genuinely asymptotic permutation-ultraproduct models in which the fold word survives.
  slofstra-involution-not-sofic-radical: that separates one solution-group involution by a specialized permutation construction without proving its whole image sofic; this proves the entire GNS quotient is sofic for each Hall/tensor trace.
---

**ESTABLISHED RADICAL-ROUTE NO-GO.** Let `tau_t`, `t in [0,1]`, be any
subsequential MF trace produced by
`all-fold-mf-moments-from-tensored-hall-reflections`, including the final
swap symmetrization, and put

```text
H_t=P/ker(pi_(tau_t)).                                  (HGS1)
```

Then `H_t` is sofic.  Consequently

```text
Rad_sof(H_t)=1.                                         (HGS2)
```

For `t<1`, the fold word `w` is nontrivial in `H_t` because

```text
tau_t((u_w-1)^*(u_w-1))=2-2t>0,                         (HGS3)
```

and therefore

```text
w_bar notin Rad_sof(H_t).                               (HGS4)
```

Every coordinate in the construction is signed monomial: `bar_sigma_n` is
a permutation representation, `bar_V_n` is diagonal with signs `+1,-1`,
and direct sums, tensor powers and the swap symmetrization preserve signed
monomiality.  The coordinates define `P` in the metric ultraproduct because
each fixed amalgam relation is eventually exact.  Their HS identity kernel
is exactly `ker(pi_(tau_t))`.  Now
`signed-monomial-tracial-images-are-sofic` replaces each coordinate by its
action on the doubled signed basis and preserves that kernel.  The induced
embedding of `H_t` into a permutation metric ultraproduct proves soficity.

The trace-negligible norm-faithful block added by
`faithful-mf-models-realize-all-mf-traces` is irrelevant here: the original
signed-monomial coordinates already induce `tau_t`, and the added block does
not change its GNS kernel or GNS quotient.

Thus the continuum of fold-visible MF traces does not furnish a
sofic-radical collision.  It instead supplies explicit sofic groups with
two maps `u,v:F->H_t` which agree on `K` and differ on `f_0`.  This is also a
concrete countermodel to any attempted inference from simplicity and
nonsoficity of `Q=F/K`, or from the associated `Q`-indexed centralizer
cocycle alone, to sofic-radical membership of the fold word.

DERIVATION
hall-tensor-coordinates-are-signed-monomial-proof
