---
rg: 2
id: one-anchor-odd-spike-has-a-cheap-reducing-cut
kind: claim
title: One anchor-odd spike has a cheap approximately reducing spectral cut
distinct_from:
  covariant-square-function-has-common-reducing-threshold: that thresholds one preassembled global defect square function; this applies coarea to an individual anchor/site odd square and computes its boundary from two complete-pair commutator rows.
  block-adaptive-sparse-reset-is-cheap: that resets coordinates after reducing blocks and coordinate sets are known; this manufactures one such block for one anchor/site spike.
  central-adaptive-peeling-or-noncentral-stopping: that must iterate and paste many vector-state-adaptive cuts; this supplies its local charged-boundary move.
---

ESTABLISHED.  For reflections `Q_1,...,Q_L`, fix an anchor `a` and site `i`
and put

```text
 Y_(a,i)=(Q_i-Q_aQ_iQ_a)/2,       R_(a,i)=Y_(a,i)^2,
 q_i=((1/L)sum_l ||[Q_i,Q_l]||_2^2)^(1/2).              (OSC1)
```

For every `0<t<1/2`, there is `s in [t,2t]` such that
`p=1_[s,1](R_(a,i))` satisfies

```text
 tau(p) <= ||[Q_a,Q_i]||_2^2/(4t),                      (OSC2)

 (1/L)sum_l ||[p,Q_l]||_2^2
 <= 2(q_i+q_a)/t.                                      (OSC3)
```

Every `Q_l` can consequently be changed to a reflection `V_l` commuting
with this same `p`, with

```text
 (1/L)sum_l ||Q_l-V_l||_2^2
 <= C(q_i+q_a)/t.                                      (OSC4)
```

On the complementary block `(1-p)`, one has the operator bound

```text
 (1-p)R_(a,i)(1-p) <=2t(1-p).                           (OSC5)
```

In fact `R_(a,i)` commutes exactly with both `Q_a` and `Q_i`.  Leave those
two reflections unchanged in the cosine--sine correction of the other
generators.  Then `(OSC5)` survives the correction.  Resetting coordinate `i` to the
identity only on `p` costs at most `4tau(p)/L` in average squared generator
distance and `C'tau(p)/L` in induced balanced energy, by
`block-adaptive-sparse-reset-is-cheap`.

For the boundary calculation, direct expansion gives

```text
 ||[R_(a,i),Q_l]||_2
 <=2(||[Q_i,Q_l]||_2+||[Q_a,Q_l]||_2).                  (OSC6)
```

Indeed first
`||[Y_(a,i),Q_l]||_2<=||[Q_i,Q_l]||_2+||[Q_a,Q_l]||_2`,
then commute the square and use `||Y_(a,i)||_infty<=1`.  Averaging `(OSC6)`
and applying Cauchy--Schwarz gives covariance at most `2(q_i+q_a)`.
Spectral coarea on `[t,2t]` proves `(OSC3)`, Markov proves `(OSC2)`, and
cosine--sine block diagonalization proves `(OSC4)`.

There is also a high-tail version, possibly at a different threshold
`s_tail in [t,2t]`:

```text
 (1/L)sum_l ||[1_[s_tail,1](R_(a,i)),Q_l]||_2^2
 <=2 tau(R_(a,i)1_[t,1](R_(a,i)))/t.                  (OSC7)
```

To see this, diagonalize `R`.  The coarea integral is the sum of lengths
with which `[t,2t]` intersects the intervals between pairs of eigenvalues,
weighted by matrix coefficients of `Q_l`.  A contributing interval has a
maximum endpoint above `t`.  Bound its intersection length by that maximum,
assign according to which endpoint is larger, and use the unit row and
column sums of `(|q_(uv)|^2)`.  The integral is at most twice the high
spectral first moment.  Averaging over `l` and dividing by `t` proves
`(OSC7)`.  This replaces the square-root covariance charge by a quantity
linear in removable high spectral mass.

For exact commutation, put `U=Q_aQ_i`.  Direct expansion gives

```text
 4R_(a,i)=2-U^2-U^(-2).
```

Conjugation by either `Q_a` or `Q_i` sends `U` to `U^(-1)`, so it fixes
`R_(a,i)` and all its spectral projections.

Thus every individual operator spike admits exactly the desired dichotomy:
remove a small reducing block or obtain an operator-small complement.  The
remaining global issue is summability: independently applying `(OSC4)` to
many overlapping `(a,i)` can pay the same commutator row repeatedly.
