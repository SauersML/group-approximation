---
rg: 2
id: toeplitz-amenable-cells-reduce-to-base-hyperlinearity
kind: claim
title: For the Toeplitz Schur packet, amenable and finite-index coefficient cells have no leverage beyond deciding whether EL_r(T) is hyperlinear
distinct_from:
  toeplitz-finite-head-hnn-approximation-is-base-equivalent: that removes one finite-head stable letter from the hyperlinear and sofic questions; this removes every amenable-holonomy or finite-index coefficient-payment cell for the Schur packet embedding, and records that the earlier residually finite fences were vacuous there.
  rf-amenable-two-cell-retains-coefficient: that fences amenable cells over residually finite bases; the Toeplitz base is not residually finite and that fence's models have zero forbidden mass for this packet.
  hyperlinear-base-amenable-cells-retain-coefficients: that is the general telescope; this applies it to the actual compressor base together with the head-blindness of residually finite models.
---

**ESTABLISHED DICHOTOMY.**  Let `iota:B_f->EL_r(T)` be the Toeplitz
Schur--Clifford packet embedding of `schur-child-crosses-toeplitz-compressor`,
`z` a forbidden packet projection with `tau_B(z)=q_0>0`, and `a` the
bounded-type coefficient of `one-bounded-type-coefficient-separates-unbounded-exits`.
Consider any cell `C` over `Lambda=EL_r(T)` (or `EL_r(T) x C_2`) built from:

* covariance rows for a finitely generated right-cancellative compression
  semigroup with right Følner sets (one or several stable letters, commuting,
  nilpotent/Hall--Witt or Heisenberg tables, and any fixed semigroup
  relations), with all rows acting on the base `Lambda` itself; or
* a finite-index overgroup of the base (finite automorphism covariance,
  finite projective normalizer tables).

Not covered: an HNN letter whose associated subgroup `Lambda` is a proper
subgroup of a finite-index overgroup `B` (the shape of the bare parity
compressor `H_T`, with `B=<Lambda,J,q>`).  There the edge group is
non-amenable and neither branch below applies; that is
`parity-compressor-hs-return`.

Suppose `C` is claimed to pay `z(1-a)` by word energy on marked
microstates with positive forbidden mass.  Then exactly one holds:

1. `EL_r(T)` is not hyperlinear.  Then `non-hyperlinear-group` is already
   answered by the finitely generated group `EL_r(T)`, and the cell adds no
   logical leverage.
2. `EL_r(T)` is hyperlinear.  Then `C` has microstates of vanishing cell
   energy, canonical on every base window, with forbidden packet mass
   `-> q_0>0` and `||z(1-a)||_2 -> ||lambda(z(1-a))||_2 >= (1-epsilon)sqrt(q_0)`.
   So the payment fails.

So this whole class of cells is dead as a *first* source of
non-hyperlinearity, whatever relations it uses.  The obstruction invariant
is **hyperlinearity of the base `EL_r(T)`**, and every member dies at the
same step: telescoping one canonical base microstate through the cell.

Before this, the attempts on `parity-compressor-old-commutant-has-positive-density`
fenced this class only with finite quotients of a residually finite base.
By `toeplitz-schur-packet-center-dies-in-residually-finite-models` those
models kill the packet centre and have forbidden mass `0` for the actual
Toeplitz embedding, so they never touched the regime `(PCD1)` constrains.
The corrected fence is unconditional as a *leverage* statement and
conditional (on hyperlinearity of `EL_r(T)`) as a *countermodel* statement.

**The gate left open.**  The class not covered is nonamenable joint holonomy
over this non-residually-finite base.  There
`profinite-free-compressors-retain-coefficient-residual` has no analogue:
its exact profinite folding cannot separate `iota(J)`, and a microstate
version needs, for several injective endomorphisms `alpha_i` at once,
canonical microstates `rho` of `EL_r(T)` with `rho o alpha_i` approximately
unitarily conjugate to `rho` on windows.  For one endomorphism such
microstates exist whenever the base is hyperlinear (restrict microstates of
the ascending HNN extension, `ascending-hnn-cannot-create-nonhyperlinearity`).
For two or more non-commuting compressors of a non-amenable base,
uniqueness of embeddings fails, so joint self-similarity is not automatic.
A live cell for this route must use exactly that: nonamenable joint
holonomy of compressors acting on the finitary head `L`.

DERIVATION
toeplitz-amenable-cells-base-reduction-proof
