---
rg: 2
id: stw99-problem-xx-villadsen-algebras-uniform-gamma
kind: claim
title: The Villadsen algebras of the first type have uniform property Gamma (STW Problem XX)
root: true
distinct_from:
  stw99-problem-xix-uniform-gamma-stably-finite-nuclear: that universal CETW question is false by Toms's different higher-stable-rank AH example; this stable-rank-one Villadsen family is positive by Vaccaro.
artifacts:
  - research/artifacts/stw99-xix-xx-literature-status-2026-08-30.md
  - research/artifacts/stw99-xix-xx-uniform-gamma-recon-2026-08-30.md
  - research/artifacts/stw99-xx-point-dominated-diagonal-gamma-2026-08-30.md
  - research/artifacts/stw99-xx-clustered-eigenmap-gamma-2026-08-30.md
  - research/artifacts/stw99-xx-eigenmap-metric-entropy-2026-08-30.md
  - research/artifacts/stw20-two-coordinate-mixing-tradeoff-audit-2026-08-30.md
---

**Problem XX of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Do the
Villadsen algebras of the first type (Villadsen, JFA 1998; the simple AH
algebras with diagonal connecting maps, positive asymptotic
identity-coordinate weight, and positive radius of comparison) have
uniform property Γ?

**ESTABLISHED IN THE CURRENT LITERATURE (status checked 2026-08-30).**
Vaccaro, arXiv:2604.24682v2, Theorem A and Corollary 4.1, proves that every
simple unital non-elementary AH algebra of stable rank one has uniform
property Γ and explicitly names the Villadsen algebras of the first type.
The paper states that this solves STW Problem XX affirmatively.  Toms,
arXiv:2606.12188v2, independently records the same positive status in its
introduction.

The earlier negative status reported in the May 2026 STW addendum came from a
superseded version of Elliott--Niu, arXiv:2504.03611.  Its current v3
(2026-08-13) no longer asserts the ambient-uniform-Γ equivalence for diagonal
AH algebras.  The exact version reconciliation is in the literature-status
artifact.

## Historical attack record

* **Cheap positive fails.**  Block-subset projections (unions of
  connecting-map blocks at a deep stage) are exactly central against
  earlier stages and halve the block-uniform weights, but against atomic
  diagonal traces — limit traces concentrating all identity coordinates at
  one point `x`, available with mass equal to the asymptotic identity
  weight `w > 0` — a fixed subset misses `τ(a)/2` by a margin `~ w/4` for
  test functions separating the selected coordinates.  So constant
  selectors cannot witness Γ; any witness must vary over the base.
* **Cheap negative fails.**  The forcing "norm-central ⟹ block-subset"
  holds only where the composite evaluations take pairwise distinct
  values; at the diagonal/coincidence loci — exactly where the atomic
  adversarial traces live — equal block values open a large within-block
  commutant and rank-half rotations exist freely.  A genuine negative
  proof must therefore obstruct 2-norm-continuous half-rank selections
  over the coincidence stratification, presumably with the Euler-class
  machinery that drives the radius of comparison; a genuine positive proof
  must build them, and Elliott--Niu says not inside the Cartan.
* Both directions are recorded in
  `research/artifacts/stw99-xix-xx-uniform-gamma-recon-2026-08-30.md`
  with the block-weight computations.
* **Vanishing coordinate weight is positive.**
  `point-dominated-diagonal-ah-has-uniform-gamma` proves uniform Gamma
  directly when the composite nonconstant-coordinate proportion tends to
  zero and the multiplicity tends to infinity.  Distinct point evaluations
  are balanced on each finite test set by vector discrepancy; only the
  coordinate blocks contribute a uniform-in-the-base error.  Thus wild
  point-evaluation data is not the obstruction.  What remained outside that
  internal theorem was the classical Villadsen regime with positive
  asymptotic coordinate mass carried by independently variable,
  low-multiplicity eigenmaps.
* **Positive coordinate weight is not by itself an obstruction.**
  `asymptotically-clustered-diagonal-ah-has-uniform-gamma` proves uniform
  Gamma when almost all eigenmaps can be grouped into fixed-size packets
  which are uniformly close on each prescribed finite test set.  Flat
  Fourier projections in each packet split every fibre trace exactly and
  asymptotically commute in operator norm.  This allows coordinate weight
  one and includes the concrete case where the number of distinct
  eigenmaps is sublinear in total multiplicity.  These witnesses are
  off-diagonal and evade the canonical-Cartan obstruction.  Independently
  variable multiplicity-one coordinate maps fail the packet hypothesis, so
  this internal sufficient condition did not reach the positive-radius
  Villadsen case.  Vaccaro closes it by a different
  stable-rank-one/tracial-local-homogeneity argument.
* **Metric entropy is the intrinsic packet threshold.**
  `sublinear-eigenmap-metric-entropy-implies-uniform-gamma` replaces exact
  eigenmap repetition by a sublinear covering-number condition for the
  pseudometric induced by each finite early-stage test set.  It is strictly
  broader: all eigenmaps may be distinct but lie in `o(L)` shrinking
  clusters.  Conversely, independent coordinate projections are uniformly
  separated by any scalar test function with nonzero oscillation, so their
  covering number remains linear.  Thus this refinement identifies, but does
  not itself cross, the classical Villadsen boundary.
* **Continuous phase variation cannot repair an independent pair.**
  `stw20-two-coordinate-variable-mixing-tradeoff` computes an exact local
  obstruction.  For a rank-one mixer over two coordinate blocks separated
  by a scalar function of oscillation `Delta`, the commutator error `C` and
  pointwise mixed-trace-halving error `E` obey
  `C^2+4E^2=Delta^2/4`.  Thus a fibre-dependent phase cannot make both
  errors small.  This fenced pairwise pointwise constructions only: it did
  not settle the full uniform-2-norm question over limit traces, which is
  now settled positively by the cited theorem.
