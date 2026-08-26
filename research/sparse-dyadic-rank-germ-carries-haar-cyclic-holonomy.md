---
rg: 2
id: sparse-dyadic-rank-germ-carries-haar-cyclic-holonomy
kind: claim
title: One sparse corona projection absorbs every fixed dyadic depth and carries Haar-like cyclic holonomy
artifacts:
  - research/sparse-dyadic-rank-germ-haar-proof.md
distinct_from:
  matrix-corona-rank-germs-absorb-fixed-depth-leavitt-escape: that proves ambient packing and divisibility through every separately fixed depth; this strengthens its explicit projection by placing an asymptotically Haar cyclic unitary on the very same sparse carrier.
  long-cyclic-return-holonomy-annihilates-every-carrier: that proves Haar-like holonomy kills every approximately fixed subcarrier; this constructs the Haar-like holonomy simultaneously with all fixed dyadic divisibility constraints.
  consecutive-dyadic-splitting-does-not-report-dimension: that pads a fixed finite splitting tree by a bounded residual rank; this gives exact divisibility at every fixed depth eventually, with no residual at that depth, while the carrier remains sparse in the ambient matrices.
---

**ESTABLISHED.**  In the corona `(UCS1)`, put

```text
k(n)=floor(n/2),
rank(p_n)=2^(k(n)),
p=[p_n] in Q.                                           (SDH1)
```

Then `p` is a nonzero projection although

```text
tr_(2^n)(p_n)=2^(k(n)-n)->0.                            (SDH2)
```

For every fixed `r`, once `k(n)>=r` the corner `p_nM_(2^n)p_n` contains a
unital copy of `M_(2^r)` and

```text
[p]=2^r[q_r] in V(Q)                                   (SDH3)
```

for a nonzero projection `q_r` depending on `r`.  Also `M[p]<=[1]` for
every fixed `M`.  Thus every bounded-window dyadic rank/divisibility test is
satisfied eventually by one nonzero sparse carrier.

There is simultaneously a unitary `u in pQp` which is asymptotically Haar
on that carrier.  On `p_n C^(2^n)`, let `u_n` be the regular cyclic shift of
order `2^(k(n))`.  Then for every fixed nonzero integer `m`,

```text
tr_(p_n)(u_n^m)=0                                      (SDH4)
```

for all sufficiently large `n`.  Hence all fixed nonzero moments of `u`
vanish in the normalized corner traces.

This rules out a generic bounded-window rank endpoint for the sparse
Property-`(T)`-free Leavitt carrier.  Even allowing the inspected dyadic
depth to tend to infinity coordinatewise gives no contradiction when the
carrier rank is `2^(k(n))`: exact divisibility and Haar-like multiplicity
escape coexist.  A valid rank proof must instead produce one closed
supercritical equation on a fixed corona class, such as `[p]=2[p]`, or first
prove a positive-density/common-reservoir return.

No statement here refutes a coefficient-sensitive mixed Leavitt occurrence;
it fences only deductions from recursive divisibility and bounded-window
rank data.

DERIVATION
sparse-dyadic-rank-germ-haar-proof
