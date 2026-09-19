---
rg: 2
id: kt-finite-image-relative-edge-models-are-impossible
kind: claim
title: Blockwise finite-image matrix models cannot recover the Kun--Thom reduced edge expectation
distinct_from:
  kt-shulman-profinite-vertex-model-is-nontempered: that uses one Kesten element to exclude the regular finite-quotient vertex norm; this survives deletion of constant vectors and excludes arbitrary weighted finite-image blocks at the relative edge-expectation stage.
  coordinate-action-not-sofic: that is the external obstruction used at the end; this translates it into a matrix conditional-expectation no-go for the inclusion Gamma less than G.
  kt-double-mixed-word-trace-selection: that asks for arbitrary normalized-Hilbert--Schmidt models of the whole double; this rules out only models assembled from finite-image vertex blocks followed by relative-commutant randomization.
artifacts:
  - notes/FALSE_RELATIVE_RANDOMIZATION_NEEDS_EDGE_TRACE_MODEL.md
---

**ESTABLISHED.**  Let `Gamma<G` be the explicit Kun--Thom pair.  There is no
sequence of finite direct sums of finite-image representations of `G` whose
**blockwise** matrix edge algebras model the canonical conditional expectation

```text
E_(L(Gamma)):L(G)->L(Gamma).                            (KFE1)
```

Precisely, at stage `n` allow finite quotients `q_(n,r):G->Q_(n,r)`, arbitrary
unitary representations `pi_(n,r)` of `Q_(n,r)`, and normalized dimension
weights `mu_(n,r)`.  Put

```text
rho_n=directSum_r pi_(n,r) o q_(n,r),
B_n=directSum_r C*(pi_(n,r)(q_(n,r)(Gamma))).           (KFE2)
```

If `E_(B_n)` is the trace-preserving matrix expectation, then it is
impossible that

```text
||E_(B_n)(rho_n(g))||_2 ->0       for every g notin Gamma. (KFE3)
```

Indeed, whenever `q_(n,r)(g)` belongs to `q_(n,r)(Gamma)`, the whole block
`pi_(n,r)(q_(n,r)(g))` already belongs to the edge algebra and is fixed by
the expectation.  Hence `(KFE3)` forces the total weight of all such false
membership blocks to tend to zero.  A union bound over each finite subset of
`G\Gamma` then produces one finite quotient separating that whole subset
from `Gamma`.  Products of these quotients make `Gamma` closed in the
profinite topology of `G`; equivalently, the finite Schreier actions converge
locally to `G/Gamma`.  This makes the coset action sofic, contradicting
`coordinate-action-not-sofic`.

Within this blockwise architecture, the conclusion is unchanged by deleting invariant vectors, choosing
nonregular representations of the finite quotients, taking arbitrary
multiplicities, or mixing many quotient blocks with vanishing weights.  Haar
randomization in `B_n'` can create relative freeness only after `(KFE3)` is
available and therefore cannot repair the obstruction.

This does not refute reduced MF of the double.  It proves that a positive
Certificate C must either use vertex-edge models which are genuinely
non-finite-image before the final amalgamated-freeness step, or use a
non-blockwise edge algebra which couples distinct quotient summands.

DERIVATION
kt-finite-image-relative-edge-no-go-proof
