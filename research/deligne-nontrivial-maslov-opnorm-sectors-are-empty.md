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

