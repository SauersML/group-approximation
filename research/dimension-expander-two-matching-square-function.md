---
rg: 2
id: dimension-expander-two-matching-square-function
kind: claim
title: Turn dimension-expander matching defects into one orthogonal bridge square function
distinct_from:
  two-matching-matrix-block-propagation: that asks for robust propagation for the primitive two-matching orbit; this allows a bounded family of dimension-expanding matchings and states the required global energy ledger.
  multiscale-square-function-checksum-forces-hs-floor: that is an abstract scalar recurrence; this asks for its concrete Fourier-PVM realization.
---

OPEN, BUT THE STATED DIMENSION-EXPANSION INPUT IS NOT BY ITSELF THE NEEDED
ANALYTIC HYPOTHESIS.  Choose a fixed `k` and binary linear maps

```text
T_(1,n),...,T_(k,n) in GL(V_n)
```

forming a uniform dimension expander: for every subspace `0<W<V_n` of
dimension at most `dim(V_n)/2`,

```text
dim(sum_i T_(i,n) W) >= (1+gamma) dim(W)                        (DE1)
```

for one `gamma>0` independent of `n`.

After exactifying the two same-basis additive representations, Fourier
expansion of the sampled relations on the matchings `a=T_i b` gives
approximate matrix-block transports `(MB2)--(MB3)`.  Prove a square-function
ledger with the following consequence: if the total sampled relation defect
is at most `epsilon`, then either

```text
dim(H) >= 2^(c n)                                               (DE2)
```

or the central/Pauli marked carrier has trace at most `C epsilon^theta`, for
fixed `c,C,theta>0` independent of `n` and `dim(H)`.

The intended ledger branches a bridge along the expanding subspace tree.
Different new Fourier labels are orthogonal, so their squared HS masses add.
`approximate-orthogonal-bridge-transfers-hs-mass` charges every failed branch
to its local transport error.  Dimension expansion reaches a positive
fraction of `V_n` in `O(log n)` generations, but the proof may not telescope
an `O(log n)epsilon` path error: first-hit losses across all branches must be
summed by Pythagoras against the one global sampled-defect budget.

The sharper replacement is
`sampled-weyl-defect-controls-common-pvm-dirichlet-energy`: require the
induced label/Schreier graph itself to have a uniform spectral gap, and make
the mixed-test defect control the transport Dirichlet energy of one common
PVM.  Dimension expansion only controls support ranks.  It does not give a
Poincare inequality for weights and therefore does not, without an
additional quantum/edge-expansion input, justify the proposed square
function.

## Attempts

- **Follow one primitive affine orbit.**  This proves the exact theorem but
  accumulates exponentially many approximate errors.
- **Apply the local bridge inequality to one block.**  Its amplitude squares
  at every generation and can disappear into tiny multiplicity blocks.
- **Sum after thresholding.**  There is no dimension-independent lower bound
  on one spectral block.  The unresolved step is to sum the orthogonal child
  blocks before the quadratic bridge estimate and charge only first-hit
  failures.
- **Infer weighted expansion from `(DE1)`.**  This conflates dimension
  expanders with spectral/quantum expanders.  The scalar endpoint actually
  needed is proved in
  `expander-pvm-transport-forces-dimension-or-mass-collapse`; its hypothesis
  is a spectral gap for the induced label graph, not merely `(DE1)`.
