---
rg: 2
id: faithful-mf-models-realize-all-mf-traces
kind: claim
title: Faithful MF coordinate models realize exactly the MF traces
distinct_from:
  shulman-symmetric-double-has-no-stable-trace-upgrade: that is a source-scope correction for one permanence theorem; this gives the intrinsic classification of traces obtainable from faithful norm-corona coordinates of any separable unital MF algebra.
  weak-mf-embedding-not-reusable: that proves a fixed weak-MF embedding need not retain trace separation; this proves that changing faithful coordinates permits arbitrary prescribed MF-trace selection.
  common-padding-erases-julia-derivation-density: that dilutes one rank profile by a trivial exact block; this reweights an arbitrary MF-trace model against an arbitrary faithful MF model and identifies the entire resulting trace class.
  hyperlinear-trace-not-mf-trace: that separates hyperlinear from MF traces; this classifies only traces produced by operator-norm MF coordinates and therefore lands exactly on the smaller MF-trace class.
---

**ESTABLISHED TRACE-REWEIGHTING THEOREM.** Let `B` be a separable unital MF
C-star algebra.  A trace `tau` on `B` is an MF trace if and only if there is
an asymptotically isometric operator-norm MF coordinate model

```text
Theta_n:B->M_(D_n)
```

whose normalized matrix traces converge pointwise to `tau`.

The forward direction is the nontrivial selection statement.  Start with
arbitrary MF-trace coordinates

```text
phi_n:B->M_(k_n),                 tr_(k_n) phi_n(a)->tau(a),
```

and any faithful MF coordinates

```text
psi_n:B->M_(ell_n),               ||psi_n(a)||->||a||.
```

Choose integers `m_n` so that

```text
ell_n/(m_n k_n+ell_n)->0
```

and set

```text
Theta_n(a)=phi_n(a)^(directSum m_n) directSum psi_n(a).    (FMT1)
```

Operator-norm defects of a direct sum are maxima, so `(FMT1)` is again an MF
model.  The `psi_n` block keeps it asymptotically isometric, while its trace
weight tends to zero; hence `tr Theta_n(a)->tau(a)`.  Conversely, a
trace-convergent MF coordinate model witnesses the MF-trace axioms directly.

Thus the phrase "the trace induced by a faithful MF embedding" carries no
extra selection content: after harmless direct-sum reweighting, the traces
induced by faithful embeddings are **exactly all MF traces of `B`**.  In
particular, norm-corona injectivity cannot privilege a canonical trace or
force a chosen ideal to have positive trace.

DERIVATION
faithful-mf-trace-reweighting-proof
