---
rg: 2
id: single-spike-split-or-charge-has-fourth-root-modulus
kind: claim
title: One anchor-odd spike either splits cheaply or has fourth-root-small mass
distinct_from:
  one-anchor-odd-spike-has-a-cheap-reducing-cut: that constructs a coarea threshold and gives an unconditional boundary upper bound; this compares the ACTUAL boundary with the spike mass and optimizes the resulting split-or-charge alternatives.
  y-square-coarea-has-a-compatible-hard-soft-window: that inserts an RMS energy scale and records three vanishing absolute costs; this gives a pointwise dichotomy without assuming the pair defect itself is RMS-small.
  central-weighted-erasure-ledger-recovers-reset-density: that sums blockwise coordinate reset sets after reducing blocks exist; this is the local physical split which can feed that external ledger.
  localized-loewner-pays-spike-or-boundary: that uses parity Loewner order to charge a spike to anchor-row mass unless its boundary is large; this uses the coarea row bound to show that failure of a CHEAP boundary correction makes the spike trace itself fourth-root-small, while simultaneously controlling the retained operator norm.
---

Let `Q_1,...,Q_L` be reflections, fix `(a,i)`, and write

```text
Y=(Q_i-Q_aQ_iQ_a)/2,       R=Y^2,
r=q_i+q_a.                                                (SSC1)
```

Assume `0<r<1/4`.  Apply
`one-anchor-odd-spike-has-a-cheap-reducing-cut` with base threshold

```text
t=r^(1/2),                                                (SSC2)
```

and let `s in [t,2t]`, `p=1_[s,1](R)`,

```text
m=tau(p),
b=(1/L)sum_l ||[p,Q_l]||_2^2.                            (SSC3)
```

Put `eta=r^(1/4)`.  Exactly one of the following alternatives applies.

1. **Split.**  If `b<=eta m`, the tuple can be changed to reflections
   `(V_l)` commuting with `p`, leaving `Q_a,Q_i` unchanged, with

   ```text
   (1/L)sum_l ||Q_l-V_l||_2^2<=C r^(1/4)m.               (SSC4)
   ```

   Resetting coordinate `i` on `p` then costs an additional `4m/L` in
   average squared generator distance and `C'm/L` in induced balanced
   energy.
2. **Charge.**  If `b>eta m`, then

   ```text
   m<2 r^(1/4).                                          (SSC5)
   ```

In both cases the retained block has

```text
||(1-p)Y(1-p)||_infty<=sqrt(2) r^(1/4).                 (SSC6)
```

Thus a spike of macroscopic physical mass is automatically in the cheap
split branch; failure of cheap splitting charges its entire mass to a
fourth-root modulus of the two pair rows.  The `m/L` reset term is exactly
the coordinate-density quantity handled by the external central weighted
ledger.

The exponent `1/4` is optimal for this three-term power-law ledger.  If one
sets `t=r^alpha`, `eta=r^beta`, the soft norm, split coefficient, and charged
mass have exponents

```text
alpha/2,       beta,       1-alpha-beta.                 (SSC7)
```

Their minimum cannot exceed `1/4`: if all three exceeded `c`, then
`alpha>2c`, `beta>c`, and `1-alpha-beta>c`, forcing `1>4c`.  Equality is
attained at `alpha=1/2`, `beta=1/4`.

This is a one-spike theorem.  It does not select a disjoint family of cuts
or prevent different spikes from charging the same row; repeated-cut
summability remains external in
`central-adaptive-peeling-or-noncentral-stopping`.
