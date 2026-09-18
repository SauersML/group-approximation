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
- **Falsification run, second attempt (2026-09-05, evening).**  Exact
  metaplectic models now exist in every dimension `4a + 10b`
  (`sp4-even-theta-constants-realize-the-metaplectic-class`,
  `sp4-second-order-thetas-realize-metaplectic-class-in-dim-four`), so the
  control the first attempt asked for is in hand.  Three facts came out.
  (1) Every mean-square descent from the ten-dimensional model into this
  sector (`d = 10, 20, 30`) converged to a pure coboundary rescaling of the
  model: the worst relators are scalar, the generator phases are small, and
  the energy of the pure rescaling agrees with the minimizer to six digits.
  (2) The best coboundary rescaling in the maximum norm over all `304,412`
  recorded relators has maximal defect `0.309` (only the four long-root
  generators move, by `0.062` radians); from the trivial class the same bar
  is `0.608`, and the spin classes do not relax at all.  This is an explicit
  tuple in every dimension `4a + 10b`, so it is what a nonabelian search
  must beat.  (3) Started at that optimum, with a smoothed-maximum objective
  (`beta = 30, 100, 300`) and no coboundary freedom removed, descents at
  `d = 4, 8, 10` never went below the bar on all relators: the minima are
  the coboundary point again (nonabelian residual `0.01` to `0.05` per
  generator), and a working-set maximum of `0.295` at `d = 4` became
  `0.340` on the full relator set.  Random starts stay near maximal defect
  `1.6`; `d = 12, 14, 20` are appended to the artifact as they finish.  So
  the numerics found no finite-dimensional tuple below the abelian bar and
  no dimension dependence; this is consistent with a gap and equally
  consistent with a nonabelian valley that local descent from the exact
  models cannot reach, so it remains no evidence either way.  What it does
  settle is the instrument: sampled mean-square energies, `p`-power
  objectives, and determinant pinning each produce artifacts (coboundary
  slides, invisible small defects, an eigenvalue-balance floor
  `2 sin(pi/3d)` when `3` does not divide `d`), all recorded in the
  artifact.
- **2026-09-18, swarm-0917-w7-w7-deligne-pull: the group-rings transplant
  (COLD family) dies at the characteristic split.**  Dictionary: a sector
  model `phi_n` gives `phi_omega: C^alpha[Gamma] -> M^omega`; a group-ring
  certificate reads ring data of the image (direct/stable finiteness, zero
  divisors, idempotent traces and `K_0` order, units and `K_1`, Sylvester rank
  functions) and derives a contradiction.
  - *Characteristic zero, tracial side.*  By
    `deligne-maslov-sector-traces-are-central-regular` the pulled-back trace is
    `t tau_+ + (1-t) tau_-`, determined by group data up to `t`.  So the
    tracial `*`-ring `(phi_omega(C^alpha[Gamma]), tau_omega)` and its
    von Neumann closure are fixed up to isomorphism, independently of the model.
    Every ring-theoretic property of that pair also holds for the abstract
    twisted algebra `L_alpha(Gamma)` cut by the central character. That
    algebra exists, so the certificate refutes nothing unless it uses the
    embedding into `M^omega` itself, and then it is the target restated.
    Invariant: the canonical central-regular trace.
  - *Characteristic zero, norm side (for the operator-norm gate).*  Stable
    finiteness certificates ("no stably finite quotient of `A_alpha`") are
    refuted by the reduced twisted algebra, which has a faithful trace.  `K_1`
    and determinant certificates are already killed by
    `deligne-sector-determinants-see-only-dimension-mod-three`.  `K_0` classes
    from finite subgroups are killed by the finite-subgroup atlas no-go above.
    Any other `K_0` certificate needs `K_0(C^*(Sp_4(Z),alpha))`, which is
    unknown, since twisted Baum--Connes for `Sp_4(Z)` is open.
  - *Characteristic `p != 3`.*  The central tool here is Elek--Szabo, as used
    by the Leavitt no-weakly-finite-image lane: sofic, or linear-sofic,
    approximations give faithful rank functions, so `F_q^alpha[Gamma]` with
    `q = 1 mod 3` would be stably finite.  Its failure proves only that `E_3`
    is **non-sofic**.  An HS model of the sector induces no rank function
    over `F_q`, so the conclusion is too weak for this gap, which is
    equivalent to non-hyperlinearity.  This route belongs to
    `deligne-cover-nonsurjunctive-from-twisted-algebra-failure` and
    `deligne-cover-linear-soficity-is-rank-projective-approximation`, not here.
  - Survivor: none inside the family.  A ring certificate must read the
    relative position of the image inside `M^omega` or `Q`. That is
    stability-approximation territory, which is HOT here.
- **2026-09-18, swarm-0917-w7-w7-deligne-pull: the calibration transplant
  dies, since no neighbouring world has a known answer.**  The idea was to
  calibrate the gap against a nearby Deligne-type cover whose hyperlinearity
  is decided.
  - `W_3`, the triple cover over `SL_2(Z[1/p])`, is Deligne-rigid with the
    congruence subgroup property.  Its soficity reduces to a
    voltage/frustration problem on congruence Selberg expanders, but its
    hyperlinearity is itself OPEN
    (`sl2-z-1-p-universal-cover-quotients-are-sofic`,
    `dv-s-arithmetic-hs-stable-nonhyperlinear-extension`).
  - BDL (`bdl-deligne-type-two-norm-inapproximability`) and genus
    monotonicity (`deligne-cover-hyperlinearity-is-monotone-in-genus`) move
    results only upward in genus.  As of April 2026, BDL leaves the real
    Deligne covers undecided, so neither gives a calibrated answer at
    genus two.
  - The metaplectic and trivial sectors are already the controls in the
    falsification runs above, so they add no new calibration point.
  - Survivor: none.  The claim stays OPEN.
- **2026-09-18, swarm-0917-w8-w8-deligne-pull: the entropy/measure transplant
  (measurable untwisting) dies at descent.**  The idea was to refute the gap by
  finding an action `Z` of `Gamma` on which `alpha` is a measurable `T`-coboundary,
  with `L^infty(Z) x| Gamma` Connes-embeddable.  Then
  `L_alpha(Gamma) ⊂ L^infty(Z) x|_alpha Gamma = L^infty(Z) x| Gamma` would make
  `E_3` hyperlinear.  The invariant is the image of `[alpha]` in
  `H^2(Gamma, L^0(Z,T))`.
  - `kazhdan-profinite-untwisting-is-virtual-splitting` (ESTABLISHED) proves that,
    for a group with (T), a multiplier dies on an ergodic profinite action only if
    it splits on a finite-index subgroup.  The argument has four stages.
    - Double the phase field, so that it twists a genuine representation.
    - Coset indicators are almost invariant by martingale convergence.  A (T)
      projection makes `c` cohomologous to `c(., . k)` on an open subgroup.
    - Peter--Weyl splits the resulting compact central `T`-extension.
    - `c` then descends to an exact monomial `alpha`-representation on a finite
      coset space.
  - `deligne-multiplier-survives-on-bernoulli-times-profinite-actions`
    (ESTABLISHED) combines this with Deligne invisibility, and with Popa product
    superrigidity for `E_3` acting on the generalized Bernoulli shift over
    `E_3/mu_3`.  Conclusion: `alpha` and `alpha^2` survive in `L^0` cohomology on
    every profinite action, on every Bernoulli shift, and on every Bernoulli-times-profinite
    action.  These are the standard Connes-embeddable actions of the residually
    finite `Gamma`, so the whole class of untwisting witnesses built from them is
    dead.
  - Survivor 1: `[0,1]^{E_3}/mu_3`, on which `alpha` is `mu_3`-trivial.  If its
    crossed product is Connes-embeddable, then `E_3` is already hyperlinear, so
    this witness is circular.
  - Survivor 2: incoherent finite-level voltage towers on `Gamma/Gamma_n`.  The
    doubling trick needs one measurable field on the limit.  At a fixed level it
    sees only the diagonal.  These towers stay governed by
    `deligne-class-finite-action-norms-vanish`.
  - The claim stays OPEN.
- **2026-09-18, swarm-0917-w9-w9-deligne-pull: the reframing transplant (auxiliary-radical transfer) dies at centrality and amenable flexibility.**
  - Idea: prove non-hyperlinearity of `E_3` by importing a computed hyperlinear (or MF) radical of an auxiliary
    group `H` along a homomorphism `f : H -> E_3`, since `z in Rad_HL(E_3)` iff `E_3` is not hyperlinear.
  - `deligne-auxiliary-radical-transfer-needs-rigid-image` (ESTABLISHED) shows, for every subgroup-closed class
    containing the countable residually finite groups:
    - (R1) `f(Rad_P H) <= C_3` is central, so it factors through the coinvariants `N/[N,H]`.  It is trivial when
      the radical is perfect or contains a relative elementary subgroup `EL_n(R,I)`, `n >= 3`.
    - (R2) A nontrivial transfer forces `p f(H)` to be Deligne-rigid, and `Q_H` to surject onto it.
    - (R3) If the maximal `P`-quotient is amenable or satisfies a law, the transfer is trivial.  This covers full
      radicals and the `K_1` extreme.
    - (R4) Homomorphisms out of `E_3` only give upper bounds on `Rad_P(E_3)`.
  - Every computed radical in the ring, groupoid and paradox lanes therefore maps trivially to `E_3`.
  - Survivor: an auxiliary group with central coinvariants whose maximal quotient maps onto a Deligne-rigid
    subgroup.  If `sp4-deligne-rigid-infinite-index-subgroup-exists` fails, that is the gap on a finite-index
    subgroup of `E_3`, which is circular.
  - The claim stays OPEN.
