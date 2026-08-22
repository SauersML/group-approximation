---
rg: 2
id: bs14-flexible-cross-packet-boundary-reconciliation
kind: claim
title: Cubic energy pays the global boundary rank in flexible BS14 extension
distinct_from:
  bs14-relative-involution-extension-stability: that asks for the final dimension-independent repair modulus; this isolates the quantitative boundary-rank and multiplicity-semigroup statement which the Weil compression shows is necessary.
  direct-sum-weil-compressions-have-quadratic-padding: that proves the desired ledger for a canonical orthogonal family; this asks for it for arbitrary cross-packet couplings and heterogeneous scalar BS packets.
  iwahori-torsion-multiplicity-stratum-reconciliation: that reconciles nearby exact torsion strata; this must first extract and globally balance the missing extension types from the two cubic residuals.
---

OPEN.  Let `(R,S)` be an exact finite-dimensional representation of
`BS(1,4)` and let `X` be a unitary.  Set

```text
E=||X^2-1||_F^2+||X R X-R^(-1)||_F^2
  +||(X S^2)^3-1||_F^2+||(X R S)^3-1||_F^2,           (FBR1)
```

where the norm is **unnormalized** Frobenius norm.  Prove that there is an
integer `k<=C E`, an exact Iwahori tuple `(X~,R~,S~)` on dimension `d+k`,
and an isometric inclusion of the original space into the enlarged one for
which the normalized-HS displacement tends to zero as `E/d tends to 0`,
with one modulus independent of all fourth-power orbit lengths, scalar
return phases, and multiplicities.

Equivalently, after decomposing the exact BS core into scalar packets
`(O,v)`, the two cubic residuals must pay for an added nonnegative
multiplicity vector `b` such that the old multiplicity data plus `b` lies in
the restriction semigroup of exact Iwahori representations:

```text
weighted_size(b) <= C E.                              (FBR2)
```

The same `b` must repair both cubic triangles.  It may couple different
`(O,v)` packets off diagonally; requiring an independent repair of every
packet is false.  A proof also has to control generator displacement after
the semigroup reconciliation, rather than merely produce an abstract exact
extension of the enlarged BS core.

The quadratic scale is forced by the normalized form of `(FBR2)`.  If
`epsilon^2=E/d`, then

```text
k/(d+k)=O(epsilon^2).                                 (FBR3)
```

It is not yet known whether `(FBR2)` holds for arbitrary mixtures.  In
particular, the statement is deliberately stronger than merely permitting
unspecified `o(d)` padding and is the sharp flexible target suggested by the
compressed Weil packets.

## Attempts

- **The canonical `p=5 mod 8` blocks obey the exact ledger.**  On one
  compressed even-Weil block,
  `even-weil-second-cubic-has-a-rank-six-determinant-gap` proves

  ```text
  ||(X R S)^3-1||_F^2 >= 2/3,
  ```

  while one restored fixed line gives an exact extension.  On an orthogonal
  sum of `K` such blocks, Frobenius squares add, so `E>=2K/3`; the evident
  `K`-line completion satisfies `K<=3E/2`.  Thus `(FBR2)` is proved, with
  the sharp quadratic normalization, for this authenticated block-diagonal
  family.

- **Heterogeneous primes are not covered by determinant multiplication.**
  For `p=1 mod 8` the second compressed cubic has determinant `+1`, so the
  rank-six determinant certificate is silent.  Even among
  `p=5 mod 8` blocks, multiplying determinants globally retains only the
  parity of the number of missing lines; opposite phase defects can cancel
  while Frobenius energy remains positive.  Therefore a scalar determinant
  or Fredholm index cannot prove `(FBR2)` for arbitrary mixtures.  The
  required charge must be positive and matrix-valued (or be recovered after
  an authenticated packet decomposition).

- **Cross-packet coupling is essential.**  The full even-Weil involution
  couples the deleted fixed line to the primitive nonzero BS packet.  The
  latter has no exact extension by itself.  Consequently the desired
  correction cannot first round each scalar packet and then take a direct
  sum.  Its multiplicity vector must be balanced globally, allowing the
  same added line or packet type to participate in off-diagonal cubic
  coefficients.

- **The remaining algebraic sublemma is semigroup saturation with an energy
  certificate.**  One needs either (i) a positive boundary operator whose
  trace/rank is bounded by the energy `(FBR1)` and whose packet-valued index
  is exactly the obstruction to lying in the Iwahori restriction semigroup,
  or (ii) a
  finite-period preconditioning theorem which authenticates the scalar
  packet table and proves a uniform integral-flow rounding bound.  A mere
  spectral threshold on the cubic residual controls only its large singular
  directions and does not recover low-amplitude boundary spread over many
  packets.

- **A possible counterexample must exhibit genuine boundary recycling.**
  To refute `(FBR2)`, it is not enough to sum the known compressed blocks:
  those already satisfy the bound.  One must mix heterogeneous levels or
  phases through one common `X` so that both cubic Frobenius energies are
  `o(k)`, while every exact enlargement requires at least `k` new
  dimensions.  This is the precise phase/multiplicity-mismatch test left by
  the one-block calculation.
