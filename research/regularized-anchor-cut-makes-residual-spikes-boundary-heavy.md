---
rg: 2
id: regularized-anchor-cut-makes-residual-spikes-boundary-heavy
kind: claim
title: Below the regularized anchor cut every residual odd spike is boundary-heavy
distinct_from:
  localized-loewner-pays-spike-or-boundary: that tests Loewner order on an exact spectral cut of one odd square and has a row-heavy alternative; this permits an arbitrary anchor-commuting compressed cut and uses the regularized average bound to eliminate the row-heavy alternative.
  regularized-anchor-square-function-has-dimension-free-cut: that makes the averaged odd square operator-small; this converts that average operator bound into a stopping inequality for every remaining individual compressed spike.
---

ESTABLISHED.  Assume the exact parity hypotheses and max-fractional
pseudodistance `kappa L` of
`adjoint-parity-cone-lifts-to-loewner-order`.  Fix an anchor `a`, write
`R_i=Y_(a,i)^2` and `K=L^(-1)sum_iR_i`, and let `q` be a projection
commuting with `Q_a` such that

```text
 qKq<=eta q.                                            (RSP1)
```

For a site `i`, take any spectral cut

```text
 r=1_[s,1](qR_iq) <=q,
 D(r)=(1/L)sum_k||[r,Q_k]||_2^2.                       (RSP2)
```

Then

```text
 (s-4eta/kappa)tau(r)<=3D(r)/(2kappa).                 (RSP3)
```

In particular, if `eta<=kappa s/8`, every nonzero residual cut satisfies

```text
 D(r)>=(kappa s/3)tau(r).                              (RSP4)
```

Thus after the regularized aggregate cut with `(RAC6)`, choosing
`theta<=kappa s/16` eliminates the row-heavy branch of the localized
Loewner dichotomy: every remaining compressed `s`-spike has a physical
boundary proportional to its trace, with no factor depending on `L`.

Unlike a literal join, `r` need not commute with `Q_i`, but it does commute
with the anchor because `q,R_i` do.  It is therefore still admissible for
the one-row anchor reset and its exact sign-trace Lyapunov.  The remaining
global task is to sum these boundary-heavy residual cuts, or to show that
the `L_2` leakage of the aggregate cut can be carried directly through the
row-column Newton contraction.
