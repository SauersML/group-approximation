---
rg: 2
id: deligne-nontrivial-maslov-opnorm-sectors-are-empty
kind: claim
title: The two nontrivial mod-three Maslov sectors have no point-norm matrix models
distinct_from:
  maslov-mod3-projective-defect-gap: that asks for a normalized-Hilbert--Schmidt defect gap; this asks for pointwise operator-norm asymptotic projective representations and is exactly the MF-radical gate.
  deligne-triple-cover-fd-central-invisibility: that excludes exact finite-dimensional odd-sector representations; this excludes their asymptotic operator-norm analogues.
---

**OPEN PRECISE OPERATOR-MF GATE.**  Let `alpha` and `alpha^2` be the two
nontrivial mod-three Maslov multipliers of `Sp_4(Z)`.  There is no sequence
of finite-dimensional projective unitary tuples which is pointwise
asymptotically multiplicative in operator norm with multiplier `alpha` or
`alpha^2`.

Equivalently, neither nontrivial Maslov sector defines a homomorphism into a
positive-dimension norm-matrix corona.  This statement uses no property
`(T)` hypothesis.  Exact finite-dimensional invisibility does not prove it:
the missing issue is precisely passage from exact representations to
operator-norm asymptotic representations.

## Attempts

- **2026-09-17, swarm-0917-w4-pull-deligne-2: transplanting the g >= 3
  stability route to genus two dies at the [T_2] hypothesis.** At g >= 3,
  empty sectors would follow from operator-HS-stability of the cover lattice
  (BDL Proposition 1.5 via `deligne-sp2g-covers-not-mf-from-operator-hs-stability`),
  and the only proposed source of that stability is BDL Conjecture 1.8, whose
  input is `[T_2]`. At g = 2 that input is false, even virtually:
  `genus-two-cover-lattices-fail-bracket-t2` shows that every finite-index
  subgroup `Delta` of `Gamma~_2` or of `E_3` has
  `dim H^2(Delta; l^2(Delta/Delta')) >= 117`, where `Delta'` is `Delta` meet the
  level-four preimage. The invariant is `b_2(Gamma_2(4)) = 118`
  (Hoffman--Weintraub), carried through the Gysin sequence, transfer and
  Shapiro. So DGLT/BLSW Theorem 1.1(F) and Conjecture 1.8 do not apply to
  this gate or to any finite-index model of it. A genus-two proof needs
  vanishing of the specific defect classes, or a non-cohomological route
  such as the Schur-kernel hole.
- **2026-09-17, swarm-0917-w5-deligne-sp4-schur: eigenline certificates
  (vector-state atoms, Magee--de la Salle invariant vectors, Kazhdan corners)
  die at their state-level step.** The Schur-kernel hole was already refuted
  (`sp4-schur-kernels-miss-every-deligne-multiplier`), so this lane pivoted to
  the two survivors that `deligne-sector-siegel-spectrum-is-full-torus` names.
  Established class-kill: `deligne-sector-eigenvector-certificates-die-at-induction`.
  For every `K <= E_3` containing `z`, the certificate "(V1) models have
  asymptotic `K`-eigenlines, and (V2) no state or corner of `A_omega` carries
  a `K`-character" goes one of two ways:
  - it is circular at (V1), since ultralimit eigenvalues form a character with
    `z -> omega`;
  - or it fails at (V2), since `Ind_K^(E_3) chi` lies in the fibre and has the
    eigenvector.

  Invariant: the class of `alpha|_(p(K))` in `H^2(p(K); T)`. The only survivor
  is an argument that uses the finite dimension in the refutation step too.
  Examples are the rank of the eigenspaces relative to `d_n`, or an
  interaction between eigenspaces that no infinite-dimensional representation
  reproduces.
- **2026-09-17, swarm-0917-w6-w6-deligne-last1: lifting routes are live but
  calibrated as hard, and the operator-norm version of ISW Theorem A does not
  go through.**
  - *Lifting route.* The target follows from (TF3), the LLP of `A_alpha`
    (`sp4-mod3-twisted-fibres-have-llp`).
    - A point-norm model gives an exact `alpha`-representation into the
      tracial matrix ultraproduct, hence a hyperlinear trace.
    - `llp-makes-hyperlinear-traces-amenable` makes that trace amenable,
      which `deligne-twisted-fibres-have-no-amenable-trace` forbids.
    - The argument passes through the HS gap. The same route was posted in
      parallel by swarm-0917-w6-w6-deligne-last2, so no separate route node
      is filed from this lane.
  - *Calibration check.* This lane first hoped to kill every lifting route
    by showing that (TF3) fails: `C^*(F_2 x F_2)` sits in `A_alpha` with a
    conditional expectation, via `mod3-twisted-fibre-llp-forces-f2xf2-llp`.
    The source check says that kill is not available. Enders--Shulman,
    arXiv:2403.12224v3 (May 2026), p. 3: "Whether C*(F2xF2) has the (L)LP is
    an outstandng open question."
  - *Operator-norm Theorem A transplant.* The attempt replaced the finite
    fd-realizable classes of `sp4-fd-projective-multiplier-is-finite` with
    the closed group `P_op` of `deligne-sep7-norm-parameter-closed-subgroup`.
    The target forces `P_op=(1/m)Z/Z` with `3` not dividing `m`, since an
    infinite `P_op` is all of `R/Z`. The idea was to take models at
    parameters `theta_n -> 0` and run ISW's argument. It dies at the NPS
    step.
    - The model defects vanish in operator norm. So the conjugation
      representations `rho_n(g)T = sigma_n(g) T U_n(g)^*` are only
      approximate `c_(-theta_n)`-projective representations.
    - The only multiplier-sensitive gap left is the Kazhdan bound
      `|e^(2 pi i theta_n) - 1| <= eta + C_eta delta_n`, taken through the
      universal-norm identity `(u_z - 1)(1 - q(Delta)Delta) ~ 0` in
      `C^*(Gamma~)`.
    - The ucp lifting error `delta_n` from Corollary 1.7 is not controlled by
      `theta_n`, so the bound is consistent with `theta_n -> 0`.
    - Invariant: every corona or ultraproduct object sees only
      `lim theta_n`, so it records the trivial multiplier.
    - Exact finite models, as in `klingen-twisted-fibres-all-fail-llp`, are
      the only published way around this, and Deligne invisibility removes
      them here.
- **2026-09-17, swarm-0917-w6-w6-deligne-last2: a missing edge. This gate is
  implied by the tracial defect gap, and hence by non-hyperlinearity of `E_3`
  and by fibre LLP.** Before this entry every live path to
  `deligne-triple-cover-exact-mf-radical` ran through this node and no route
  entered it. Two routes are now recorded.
  - `deligne-opnorm-sectors-empty-from-hs-defect-gap`: point-norm models
    are normalized-HS models, since `||.||_2<=||.||_op` and relator defects
    telescope through pair defects. So
    `maslov-mod3-projective-defect-gap` implies this gate. By the established
    `deligne-sector-gap-is-exactly-nonhyperlinearity`, non-hyperlinearity of
    `E_3` therefore already gives `Rad_MF(E_3)=C_3`.
  - `maslov-hs-gap-from-odd-fibre-llp-by-compression`: LLP of
    `C^*(Sp_4(Z);alpha)` gives ucp coordinate lifts on the Kazhdan generator
    system. Stinespring turns these into rank-`d_n` corners of exact
    `1/3`-projective representations, with
    `||[P,pi(s)]||_HS/sqrt(rank P) <= 2 sqrt(eta_n) -> 0`. This contradicts
    `deligne-sep8-moving-parameter-compression-gap`, so the defect gap
    holds.
  `bin/cairn impact sp4-mod3-twisted-fibres-have-llp` now flips seven claims:
  this gate, the exact radical, `deligne-triple-cover-is-not-mf`, the HS gap,
  stable non-hyperlinearity and `non-hyperlinear-group`.
  **Calibration for this lane.** Any refutation step that survives replacing
  operator-norm defects by normalized-HS defects proves that `E_3` is
  non-hyperlinear, which is the flagship. A proof of this gate that is
  genuinely easier must use a feature that normalized-HS limits lose:
  - spectral or K-theoretic data of the norm corona (determinants are
    already killed down to `d mod 3` by
    `deligne-sector-determinants-see-only-dimension-mod-three`);
  - liftability that holds only for the quotient
    `prod M_(d_n)/(+) M_(d_n)`.
  Liftability for all *homomorphisms* into that quotient is equivalent to
  this gate by vacuity. The open op-specific weakening of the fibre-LLP
  hypothesis is local liftability of all *ucp maps* into that single
  quotient. The gate stays OPEN.
- **2026-09-17, swarm-0917-w6-w6-deligne-break: arguments local to a
  flexible subgroup die, dimension-using ones included.** Established class-kill:
  `deligne-flexible-subgroup-restrictions-carry-exact-sector-models`.
  - Invariant: the virtual restriction of `alpha` to the subgroup `A`
    generated by the relations the argument uses, that is, whether `A~` is
    residually finite.
  - If `A` is flexible, genuine finite `omega`-models of `A~` exist with the
    canonical trace limit: the `omega`-part of the regular representations of
    `A~/N_k`. Every property of restricted models deduced from asymptotic
    multiplicativity, `z -> omega`, the trace limit and finite dimension
    (ranks, multiplicities, determinants, eigenlines, corners) holds for them.
    So the refutation step fails.
  - Flexible subgroups: finite, amenable, virtually free, virtually surface,
    virtually free x virtually free, and every subgroup of block
    `SL_2(Z) x SL_2(Z)` or of the Siegel or Klingen parabolic.
  - This kills the last survivor above (dimension-using arguments) whenever
    it is localized on such a subgroup. A proof must use relations generating
    a Deligne-rigid subgroup.
  - New decomposition prerequisite, which can fail:
    `sp4-deligne-rigid-infinite-index-subgroup-exists`. If it fails, the gate
    cannot be localized to any infinite-index subgroup.

- **2026-09-18, swarm-0917-w9-w9-deligne-follow (stability-approximation): a
  real untwisting on `Mod(S_2)`, and a new two-prerequisite route.**
  - Established: `mod-s2-real-untwisting-identifies-deligne-norm-parameters`.
    - `H^2(Mod(S_2);R) = 0` and `H^1 = 0`, so `b o pi = df` for a unique real
      `f`. Also `f|_Torelli = r * (separating-twist count)`, with `r = a/10`
      and `3 not | a`; this is read off the mod-three splitting and
      `deligne-triple-cover-fd-central-invisibility`.
    - Consequently `theta` lies in `P_op` iff `-r theta` lies in `Z_op`, the
      closed group of scalars that a separating twist can approach under
      point-norm asymptotic homomorphisms of `Mod(S_2)`.
    - So this gate holds iff no point-norm asymptotic homomorphism of
      `Mod(S_2)` sends `t_s` to `omega^(+-1) I`. Also `P_op = R/Z` iff
      `Z_op = R/Z`.
    - Invariant: after untwisting, the Maslov class, and with it the Dadarlat
      windings that make `Sp_4(Z)` unstable, is gone, since
      `H_2(Mod(S_2);Q) = 0`. Only one scalar remains.
  - New route `deligne-opnorm-sectors-empty-via-mod-s2-matricial-stability`
    requires two OPEN claims, each able to fail independently:
    - (A) `mod-s2-is-point-norm-matricially-stable`, where the known
      cohomological obstruction vanishes;
    - (B_op) `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`.
      It is *necessary* for this gate, is implied by the HS gap node, and is a
      purely spectral statement about honest representations.
  - Under (A), the gate is equivalent to (B_op). This meets the w6-last2
    calibration, since the route uses operator-norm liftability. Neither
    prerequisite was proved here, so the gate stays OPEN.
