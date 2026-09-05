---
rg: 2
id: maslov-mod3-projective-defect-gap
kind: claim
title: The two nontrivial mod-three Maslov projective sectors of Sp4(Z) have a dimension-free normalized-HS defect gap
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
  - research/artifacts/maslov-mod3-sector-numerics-2026-09-05.md
distinct_from:
  iwahori-local-global-defect-question: Iwahori asks whether two almost-compatible SL2(Z) representations can be repaired to a compatible pair; this asks only whether one fixed nonzero projective cohomology class of Sp4(Z) has any arbitrarily accurate normalized-HS models.
  exel-loring-mark-quantization: Exel--Loring quantizes a winding invariant of almost commuting matrices; this is a projective relator-energy gap for the mod-three Meyer--Maslov multiplier.
  quantum-context-frame-index: that builds parity/index from a finite contextual frame system; this uses the classical symplectic universal-cover cocycle and no BCS frame packet.
---

Fix a finite presentation of `Gamma=Sp_4(Z)` and let `alpha` be the
`Z/3`-valued multiplier obtained from the three-fold Deligne cover (equivalently
a mod-three representative of the universal-cover/Meyer--Maslov class).

Prove that there are a finite presentation window and `c>0` such that for
**every** matrix dimension `d`, every tuple of unitaries attempting to satisfy
the `alpha`-projective relations has maximum normalized-HS relator defect at
least `c`; and likewise for `alpha^2`.

Equivalently, neither nontrivial twisted sector admits a sequence of
finite-dimensional projective almost representations with defect tending to
zero.

By `deligne-sector-gap-is-exactly-nonhyperlinearity`, this statement is
equivalent to non-hyperlinearity of the Deligne triple cover itself: any
surviving projective almost representation can be tensored with canonical
finite-quotient microstates of `Sp_4(Z)` to produce a faithful hyperlinear
embedding of the cover.  Thus this node is a terminal formulation, not a
strictly easier analytic precursor.

By `maslov-inverse-sector-symmetry`, the two nontrivial sectors are exchanged
by an anti-symplectic automorphism.  Analytically it is enough to prove the gap
for `alpha`; the `alpha^2` case follows with the same constant after changing
presentation coordinates.

## Attempts

- **Twisted Fox/Jacobian gap.** Linearize the projective relators with the
  multiplier held fixed.  The scalar gauge direction disappears.  A
  dimension-uniform lower bound on the twisted Jacobian, followed by a
  quantitative implicit-function/Newton argument, would isolate the empty
  exact projective representation variety.
- **Maslov curvature energy.** Choose an explicit finite family of symplectic
  elements/Lagrangians whose Meyer--Maslov cocycle sum is `1 mod 3`, and seek
  a sum-of-squares inequality converting that nonzero curvature into a lower
  bound for the relator HS energy.  The certificate must be trace-density
  sensitive; bare determinant divisibility is not enough.
- **Finite-dimensional relation Laplacian.** Regard every candidate tuple as
  an exact representation of the free presentation group and study the
  positive relation-energy operator `D_R=sum_r (r(U)-1)^*(r(U)-1)`.  Seek a
  trace-normalized modulus forcing the central mark energy to vanish whenever
  `tr_d(D_R)` vanishes, uniformly in `d`.  Twisted Fox/cochain spectral gaps
  and low-energy rank-profile bootstraps are concrete subattacks.
- **Finite-subgroup atlas no-go.** Restriction multiplicities on finitely many
  finite subgroups cannot alone separate the multiplier: scaled projective
  regular representations give an exactly compatible local multiplicity ray
  on every finite atlas.
- **Bounded-block gap.** `maslov-bounded-block-sector-gap` proves a genuine
  normalized-HS floor on every fixed block-size stratum.  Thus any sequence
  falsifying this claim must put asymptotically all dimension into common
  irreducible blocks whose sizes escape every fixed bound; scalar phase
  mixtures and bounded packet induction cannot be countermodels.
- **Fixed-representation compression no-go.** C-star property (T), Brown's
  amenable-trace theorem, and Deligne invisibility show that the two twisted
  fibres have no amenable traces.  Hence no exact infinite-dimensional
  Maslov representation has finite-rank Folner compressions.  Any
  countermodel must vary intrinsically with dimension; it cannot be obtained
  by compressing the twisted regular, discrete-series, or another fixed
  projective representation.
- **No tracial-positivity shortcut.** The twisted left-regular representation
  exists in infinite dimension, so a moment/SOS certificate valid in every
  tracial von Neumann algebra cannot exclude `alpha`.  Any separator must use
  genuinely finite-dimensional structure.
- **Falsification.** Direct nonlinear optimization in increasing dimensions
  should be run first.  If the minimum projective relator energy visibly
  decays toward zero, this claim is false and the Deligne lane must use a
  weaker positive-density/trace obstruction rather than a full sector gap.
- **Tensor-camouflage audit.** Exact finite-dimensional invisibility rules out
  zero defect at each fixed dimension, but a dimension-uniform positive gap
  is already precisely non-hyperlinearity of the cover.  Property (T) does
  not by itself bridge that quantifier change.
- **Tensor-cube/adjoint neutralization has no inverse.**  Cubing an
  `alpha`-projective tuple or passing to its adjoint cancels the scalar
  cocycle and produces an ordinary almost representation.  Ordinary HS
  correction of the resulting tuple does not keep the correction inside the
  diagonal tensor-cube or inner-adjoint locus, so it supplies no projective
  tensor root.  `order-three-tensor-neutralization-loses-projective-root`
  records the exact `C_3 x C_3` Weyl model and the determinant discontinuity
  which rule out obtaining the gap from cocycle order or determinant alone.
- **Metaplectic-base degree-six relocation.**
  `maslov-mod3-gap-is-metaplectic-base-degree-six-gap` proves that this gap is
  quantitatively equivalent to the `1/6` gap.  At group level this replaces
  `E_3` by
  `1 -> Z/3 -> E_6 -> E_2 -> 1`, where the metaplectic base `E_2` is
  residually finite and the kernel is the full finite residual of `E_6`.
  Thus one may attack a finite invisible central extension of an RF Kazhdan
  base, but RF and property `(T)` alone still do not supply the missing
  normalized-HS stability modulus.
- **Falsification run, first attempt (2026-09-05).**  The relator exponents
  the "Falsification" item needs are now computed without any cocycle
  formula: `sp4-root-relators-below-length-twelve-lift-to-universal-cover`
  shows every root relation of length below twelve is sector-blind and the
  sector phase sits entirely on the twenty long-root `w^4` relators of length
  twelve.  Staged Riemannian descent on `U(d)^8` for `d <= 16`, from trivial,
  permutation and random starts, finds only abelian relaxations (identical
  minima at `d = 4` and `d = 8`) and does worse on the metaplectic control
  sector, which has exact finite-dimensional solutions, than on this sector.
  So local search of this kind cannot see the obstruction, and its numbers
  are not evidence either way; the artifact says what a decisive run needs
  (a theta-constant seed for the control, or exhaustive small-`d` search).
