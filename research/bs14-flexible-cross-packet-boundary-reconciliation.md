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

- **Every canonical compressed even-Weil block obeys the exact ledger.**  If
  `p=5 mod 8`,
  `even-weil-second-cubic-has-a-rank-six-determinant-gap` proves

  ```text
  ||(X R S)^3-1||_F^2 >= 2/3,
  ```

  If `p=1 mod 8`, the determinant is neutral, but
  `deleted-fixed-line-first-cubic-has-explicit-positive-spectrum` computes
  the first cubic exactly and gives Frobenius square at least `144/125`.
  One restored fixed line gives an exact extension in either case.  On an
  orthogonal sum of `K` heterogeneous canonical blocks, the **sum** of the
  two cubic Frobenius squares is therefore at least `2K/3`; the evident
  `K`-line completion satisfies `K<=3E/2`.  Thus `(FBR2)` is proved, with
  the sharp quadratic normalization, for this authenticated block-diagonal
  family.

- **Heterogeneous primes are not covered by determinant multiplication, but
  their canonical orthogonal sums are covered by positive cubic energy.**
  For `p=1 mod 8` the second compressed cubic has determinant `+1`; its
  deleted mode instead appears as a conjugate rank-two eigenvalue pair in
  the first cubic.  Even among
  `p=5 mod 8` blocks, multiplying determinants globally retains only the
  parity of the number of missing lines; opposite phase defects can cancel
  while Frobenius energy remains positive.  Therefore a scalar determinant
  or Fredholm index cannot prove `(FBR2)` for arbitrary mixtures.  The
  required charge must be positive and matrix-valued (or be recovered after
  an authenticated packet decomposition).  Squared Frobenius energy gives
  exactly such a noncancelling charge once the canonical blocks are known;
  the open issue is to authenticate an analogous boundary decomposition for
  an arbitrary common `X` which mixes scalar packets.

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

- **A block-free positive charge exists once the boundary corner is
  exposed.**
  `positive-fixed-corner-cubic-energy-charges-deleted-rank` treats an
  arbitrary finite-rank reservoir `Q` fixed pointwise by the first parabolic
  word.  It allows the ambient involution to mix every deleted direction and
  proves the exact identity

  ```text
  ||first cubic residual||_F^2=Tr_Q f(QXQ)
  ```

  with `f(t)>0` on every compact subinterval of `[0,1)`.  Thus neither
  determinant cancellation nor heterogeneous mixing can recycle a positive
  corner whose compression stays uniformly below one.  The logical
  direction is load-bearing: the theorem starts with an exact dilation and
  its corner `Q`, whereas `(FBR2)` starts only with the compressed
  near-solution.  The remaining gate is therefore a reverse boundary
  dilation/authentication theorem, not another scalar index.

- **Two cubic carriers give an exact reverse decoder under one angle
  hypothesis.**
  `two-cubic-residual-carriers-recover-the-deleted-source` proves that, in a
  positive-corner dilation, each cubic residual has a rank-doubled carrier
  containing the common source image `PXQH`.  If the two exit halves have a
  uniform principal-angle gap, then

  ```text
  PXQH=ran(W_1-1) intersect ran(W_2-1),
  ```

  and a spectral projection of the product of the two carrier projections
  recovers it stably.  This also gives a sharp one-cubic no-go: one carrier
  contains source and exit with equal rank and cannot distinguish them.
  General scalar phases do make the exits asymptotically parallel, as
  recorded below.  Thus the surviving arbitrary-model question is how to
  separate energy-paid active parallel modes from continuously correctable
  passive modes, not whether every carrier has a uniform angle.

- **Canonical determinant-neutral packets have a large uniform carrier
  angle.**
  `even-weil-two-cubic-exit-angle-is-one-over-root-p-plus-two` computes the
  non-source principal cosine for `p=1 mod 8` as

  ```text
  1/(sqrt(p)+2)<1/6.
  ```

  Orthogonal sums, heterogeneous primes, and multiplicity mixing preserve
  this bound.  Hence the known neutral Weil family cannot furnish the
  parallel-exit counterexample.  Any such counterfamily must use genuinely
  non-Weil scalar return phases or an approximate off-diagonal coupling not
  unitarily equivalent to multiplicity mixing of exact Weil blocks.

- **Fixed-period preconditioning leaves a quantitative basin condition.**
  `fixed-level-bs14-compatible-basin`
  identifies the bounded problem as the arbitrary-multiplicity extension of
  one finite metacyclic core `B_(K,M)` by `x`.  If its stability radius and
  modulus dominate the explicit preconditioning error
  `alpha_(K,M)=O(K^(-1/2)+M^(-1))` along a cofinal sequence, the staircase
  closes the qualitative relative-stability endpoint, but does not itself
  give the sharp quadratic padding bound in the present claim.  Qualitative
  stability separately for every
  fixed `(K,M)` is not enough: its radius may decay faster than `alpha`, so
  the preconditioned tuple never enters the local basin.  This is the exact
  uniformity datum a finite-level packet proof must report.

- **General scalar phases refute a uniform angle but obey an energy-angle
  dichotomy.**  `scalar-bs14-exit-angle-energy-dichotomy` computes the exit
  cosine from the return-shift numerical range:

  ```text
  kappa=|(1+a)^2<z,S^(-2)RSz>-a^2|/(1+2a).
  ```

  Long scalar cycles with return phase chosen so the weighted shift has
  monodromy one admit Gram data with `kappa->1`.  Thus the canonical Weil
  angle cannot be extended phase-uniformly.  However the first-cubic energy
  satisfies `f(a)>=(3/8)(1-a^2)^2`: after thresholding the source coupling,
  active parallel directions have rank charged by the relator energy and
  passive directions have total normalized-HS coupling at most
  `sqrt(tau)`.  The remaining task is to turn this active/passive split into
  one global multiplicity-semigroup repair; searching for an unconditional
  angle gap is now fenced.

- **The global threshold has explicit qualitative rates, but invariant
  hulling is impossible.**  `bs14-energy-threshold-active-passive-ledger`
  chooses `tau=e^(1/4)` and gives active padding fraction `O(e^(1/2))` and
  passive coupling cost `O(e^(1/8))`.  This would already suffice for the
  qualitative relative-stability endpoint.  However
  `bs14-residual-invariant-hull-has-unbounded-packet-loss` shows that the
  BS-core invariant hull of a rank-one Weil source is the entire
  `d`-dimensional packet.  The remaining reverse operation is isolated as
  `bs14-residual-polar-data-build-active-dilation`: jointly round the two
  high-residual polar decompositions to integer source/exit cells and add
  trivial-core dimensions, without replacing the non-invariant source by a
  core-central projection.

- **The active flow is typed by the inversion relation.**
  `bs14-trivial-boundary-inversion-forces-r-fixed-source` shows that every
  neutral source column must lie in `Fix(R)`; on a scalar packet this exists
  exactly at return phase `v=1`.  An ordinary integral transportation of
  carrier dimensions is therefore insufficient.  Explicit long
  `v=1` cycles still make the two exits parallel, so the phase restriction
  does not revive an angle gap.  The last flow must jointly round
  `R`-fixed source cells, their exit Grams, and the involution equations.

- **The fixed-source flow is genuinely three-way and need not saturate.**
  `bs14-two-exit-typed-transport-is-not-saturated` decomposes
  `Fix(R|H_(O,V))` as the orbit-sum copy of `ker(V-1)` and writes the joint
  multiplicity matrix: one source type must be matched simultaneously to
  one exit type for each cubic.  The resulting three-uniform incidence
  matrix has a determinant-two minor; an explicit even-parity four-cell
  support has integral unit margins but only the half-integral joint table.
  Therefore ordinary network-flow integrality cannot close `(FBR2)`.
  A proof needs a BS-specific balanced-support theorem, an energy-controlled
  parity padding lemma, or an operator argument excluding the parity cycle.

- **Multiplicative saturation is not additive flexible padding.**
  `bs14-native-cell-padding-preserves-lattice-charge` records the exact
  affine-semigroup obstruction.  A margin outside the lattice generated by
  the native cells stays outside after adjoining arbitrarily many cells from
  that same support.  In the determinant-two example, a mod-two charge is
  conserved by all four even-parity cells: doubling the entire margin vector
  works, but same-support padding never does.  Hence even a bounded
  saturation exponent does not prove `(FBR2)`.  The analytic repair must
  either change rounded packet types at energy-controlled cost or exhibit a
  native support-enlarging cell which cancels every torsion charge.

- **A possible counterexample must exhibit genuine boundary recycling.**
  To refute `(FBR2)`, it is not enough to sum the known compressed blocks:
  those already satisfy the bound.  One must mix heterogeneous levels or
  phases through one common `X` so that both cubic Frobenius energies are
  `o(k)`, while every exact enlargement requires at least `k` new
  dimensions.  This is the precise phase/multiplicity-mismatch test left by
  the one-block calculation.
