---
rg: 2
id: schreier-grassmann-square-function-for-all-weak-commutator-layers
kind: claim
title: Sum the Schreier gaps of all weak-commutator exterior layers in one HS square function
distinct_from:
  involutive-schreier-matchings-uniformly-kill-alternating-commutator-forms: that proves the complete exterior-square inequality; this must include every nonlinear Sidki layer and arbitrary operator multiplicity.
  dimension-expander-two-matching-square-function: that starts from subspace dimension growth; this uses a uniform Cayley/Schreier spectral gap on independent frames, which is strictly stronger than dimension expansion.
---

OPEN.  Use the bounded involutive expanding family `S_n` supplied by
`bounded-involutive-cayley-expanders-for-sl-n-two`.  Test the identity
matching and the mixed matchings

```text
a=s b,                    s in S_n.                           (GS1)
```

After exact same-basis BLR decoding, prove that their total normalized-HS
twisted-commutator defect controls the complete Weyl defect with constants
independent of `n` and the matrix dimension.

The class-two term is now closed by
`involutive-schreier-matchings-uniformly-kill-alternating-commutator-forms`.
The proposed higher-layer ledger is as follows.  The successive multilinear
initial terms of the diagonal weak-commutativity kernel are alternating
commutator tensors.  At exterior degree `k`, evaluate such a tensor on the
transitive Schreier set `Omega_k` of independent ordered `k`-frames.  The
minimum-distance theorem for the binary Grassmann evaluation code gives a
positive relative support bounded away from zero uniformly in `k<n`: its
smallest support is attained by a decomposable Pluecker coordinate and has
asymptotic density

```text
product_(j>=1) (1-2^(-j)) > 0.28.                             (GS2)
```

Thus a uniform Cayley gap can charge every nonzero exterior layer by a
constant, unlike a raw degree-`k` Reed--Muller bound.  The top layer `k=n`
is the determinant invariant and must be charged directly by one seed
relator; it cannot be removed by a Schreier Poincare inequality.

The missing theorem is operator-valued and simultaneous: identify the
actual matrix-block/Sidki filtration with orthogonal HS summands carrying
these frame representations, show that each sampled relator supplies the
corresponding edge gradient, and sum first-hit losses across all degrees
before applying Poincare.  Paying the defect separately at each of the `n`
layers would leave an `n epsilon` loss and is not sufficient.

## Two cautions fixed by this formulation

- Dimension expansion alone does not imply the required edge or quantum
  expansion.  The hypothesis is the Cayley spectral gap, so every Schreier
  representation and every Hilbert-valued amplification inherits the same
  Poincare constant.
- The sampled commutator itself is a vertex constraint, not literally
  `f(sb)-f(b)`.  Formula `(SG2)` constructs the gradient only after
  polarization at degree two.  The higher-degree analogues must be proved;
  ordinary scalar expander mixing cannot be substituted for them.
