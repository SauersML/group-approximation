---
rg: 2
id: terminal-cut-tree-carleson-controls-aggregate-offdiagonal
kind: claim
title: The retained cut tree has a terminal operator-row Carleson bound
distinct_from:
  adaptive-spike-quarantines-have-summable-trace: that budgets the trace of witness spikes; this must control the final aggregate generator seam in operator norm or an equivalent row-Carleson norm.
  aggregate-terminal-even-defect-is-quartic-summable: that is the desired balanced-energy conclusion; this isolates the missing cut-tree invariant which makes the elementary quartic ledger apply.
---

OPEN.  Strengthen the retained terminal cut-tree construction so that, off
the prescribed vanishing spike quarantine, its final off-diagonal parts

```text
O_i=Q_i-Phi_F(Q_i)
```

obey either

```text
max_i||O_i||_op^2=o(1),                               (TCC1)
```

or a dimension-free row-Carleson substitute which simultaneously controls
all bounded-width even parity products, the diagonal fourth moments
`L^(-1)sum_i tau(O_i^4)`, and
`tau((L^(-1)sum_iO_i^2)^2)` by `o(1)D`.

The currently recorded stopping invariant gives small normalized-HS cost
for each selected cut and an exact Pythagorean sum.  It does not imply
`(TCC1)`: `small-cut-hs-does-not-control-terminal-operator`
has vanishing individual cut scale but terminal operator seam one.  A proof
must therefore use the balanced parity/complete-pair equations to exclude
that direct-sum swap geometry, rather than infer operator-smallness from
cut bookkeeping or spike trace alone.

## Attempts

1. **Take the maximum individual cut boundary.**  This is only a normalized
   Hilbert--Schmidt number.  Disjoint two-dimensional swaps make that maximum
   tend to zero while their terminal seam has operator norm one.
2. **Use exact cut Pythagoras.**  It controls `tau(A)=D`, not `||A||_op` or
   `tau(A^2)`; the same swaps have `A=I`.
3. **Invoke the current spike budget.**  Its spectral projections belong to
   clipped low-gap witnesses.  No recorded invariant identifies every high
   spectral subspace of the final generator seam with one of those witness
   spikes.
