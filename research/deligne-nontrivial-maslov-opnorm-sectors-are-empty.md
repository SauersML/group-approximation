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
- **2026-09-18, swarm-0917-w12-w12-deligne-pull (probability-random): the
  CLT/averaging amplification class dies at the op-norm gate; its HS shadow is
  ESTABLISHED.**
  - *Class.* Build a model `U` at a small parameter `t` whose curvature
    `D = U(g)U(h)U(gh)^*` has eigen-angles `psi_j` (measured from
    `2 pi t b(g,h)`) with small variance but possibly wide support. Then
    amplify by
    - mixtures (direct sums over a random choice of model),
    - independent products (tensor powers `U^(tensor k)`), or
    - any polynomial functor of `GL(d)` (Schur functors `S_lambda(U)` and
      sums of them),

    hoping for a `sqrt(k)` gain in the op defect.
  - *Where every member dies.*
    - Op norm of a direct sum is the max, so mixtures gain nothing.
    - For a functor `F`, the curvature of `F(U)` is `F(D)`.
    - `F(D)` contains the extremal `GL(d)`-weight. For `S_lambda` its
      angle is `sum_j (lambda_j - lambda_(j+1)) X_j`, with
      `X_j = psi_(1) + ... + psi_(j)` the partial sums of the sorted
      angles. For `U^(tensor k)` it is `k max_j psi_j`.
    - So `||F(D) - c^|lambda|||_op` is governed by the *support* of the
      curvature spectrum, additively. There is no concentration gain.
    - Rectangular `lambda = (c^d)` reduces to `det^c`: this is scalar data at
      an integer parameter, which item 8 of
      `sp4-winding-ratio-sharp-constant-is-gromov-dual` already
      shows sits exactly at the threshold.
  - *Invariant.* On this gate, the whole class reduces exactly to the sep8
    op threshold `o(|t|)`. It gains nothing over it.
  - *Not covered.* Subspaces invariant only under the specific image
    `U(Gamma)^(tensor k)` and not under `GL(d)`. Such a subspace can avoid
    extremal weights, but choosing it is structural input, not averaging.
  - *What survives, in HS.* The distributional gain is real for normalized
    traces.
    - `deligne-hs-parameter-trace-threshold` (ESTABLISHED): the HS
      parameter group `P_2`, which contains `P_op`, is `R/Z` iff small-parameter models have
      *trace* defect `o(|t|)`, i.e. HS defect `o(|t|^(1/2))` plus centring.
    - `1/3 in P_2` iff `E_3` is hyperlinear. So non-hyperlinearity is
      exactly "`P_2 != R/Z` (a linear trace gap on one finite window) and
      `3` does not divide `m`".
    - `mod-s2-separating-twist-character-semigroup-dichotomy`
      (ESTABLISHED): the circle part `G_2` of the separating-twist trace set
      is a closed subgroup. The genus-two HS gap is `omega not in G_2`, and
      `G_2 = S^1` iff the traces are tangent to the circle at 1.
    - That split is recorded as route
      `mod-s2-torelli-scalar-gap-via-nontangency`, with OPEN prerequisites
      `mod-s2-separating-twist-characters-are-nontangent-at-one` and
      `mod-s2-separating-twist-circle-group-has-order-prime-to-three`.
  - The gate itself stays OPEN.

- **2026-09-18, swarm-0917-w13-w13-deligne-pull (transplanter): calibration of the bus need "near-identity
  honest `Mod(S_2)` representations have zero Torelli winding" (need N). Nothing is established here.**
  N matters because, if true, it would refute (A) `mod-s2-is-point-norm-matricially-stable`. Stability would
  lift `Sp_4(Z)` quasi-representations with nonzero Dadarlat winding to honest `M`-representations with
  `t_s ~ 1` and nonzero winding.
  - *Reduction (elementary).* `M^ab = Z/10` and `t_s -> 2`, so `det rho(t_s)` lies in `mu_5`. If
    `||rho(t_s) - 1|| < eta_0 < 1`, the principal `w(rho) = Tr log rho(t_s)/(2 pi i)` lies in `(1/5)Z` and is
    continuous. So `w` is constant on each connected component of `{rho : ||rho(t_s) - 1|| < eta_0}` in
    `Hom(M, U(d))`. N is equivalent to: every such component contains a representation with `w = 0`.
  - *Classes where N holds.*
    - Monomial and Torelli-character representations: transfer gives winding sum `0` for real characters.
    - Jones rectangular `(3,3)` family: `rho(t_s)` has eigenvalues `zeta^2 q^(24/5)` (multiplicity 1) and
      `zeta^2 q^(-6/5)` (multiplicity 4). The `q`-exponents sum to zero, so `w` is identically `0` on the
      branch through `zeta^2 = 1`. Its near-scalar values lie only in `mu_5`, never at `omega`, which is
      consistent with (B_op).
    - Clock-shift and Heisenberg representations induced from a finite-index `H >= Torelli`: `H/Torelli`
      is a finite-index subgroup of the Kazhdan group `Sp_4(Z)`, so it has finite abelianization. A
      nilpotent quotient of `H` therefore sees `Torelli` through a finite-index image of an abelian
      quotient, and these representations reduce to the character class above.
  - *Survivor.* A counterexample to N, and so the only honest threat to (A) through windings, must have
    nonabelian, non-virtually-nilpotent Torelli image. It must also lie in a component of the near-identity
    locus that avoids every representation factoring through a finite or Jones-type quotient. No such
    representation is known.
  - *Status.* The Kazhdan reduction is recorded as a sketch, not as a claim. The gate stays OPEN.

- **2026-09-18, swarm-0917-w14-w14-deligne-pull (entropy-measure, third pass on
  this node): free-entropy and winding transplants die; no survivor.**
  - *Invariant.* A point-norm `alpha`-model `u_n` has an ultralimit trace
    `tau = lim tr_(d_n) o u_n`. It is a trace on the twisted fibre
    `C^*(Sp_4(Z), alpha)`, so it is the canonical trace (the character
    rigidity already used by `deligne-sector-gap-is-exactly-nonhyperlinearity`).
    Any microstate entropy counts matrix tuples through trace moments only.
    That covers Voiculescu `chi` and `delta_0`, the Jung--Shlyakhtenko bound
    `delta_0 <= 1` for property `(T)` generators, Hayes 1-bounded entropy, and
    sofic or `f`-invariant entropy of the fibre.
  - *Where every trace-level member dies.* An op-model gives microstates for
    `tau`, but so does every normalized-HS model. A trace-level entropy
    argument that refutes op-models therefore proves the microstate space of
    `(L_alpha(Sp_4 Z), tau)` is empty. That is non-hyperlinearity of `E_3`,
    which is the flagship itself (w6-last2 calibration). An argument that the
    space is only small (`delta_0 <= 1`, 1-boundedness) contradicts nothing,
    since op-microstates are a subset.
  - *The only op-level member.* This is Hadwin--Li--Shen topological free
    entropy, whose microstates are norm-approximate relation solutions.
    `delta_top = -infinity` for the Kazhdan generator system with multiplier
    `alpha` is a verbatim restatement of this gate. The inequality
    `delta_top <= sup_tau delta_0` gives only the trace-level bound again. So
    the class gives no new prerequisite.
  - *Winding and K-theory tests on route (A),
    `mod-s2-is-point-norm-matricially-stable`, all vanish.* For an asymptotic
    homomorphism of `M = Mod(S_2)`, the Dadarlat winding is additive on
    `H_2(M;Z) = Z/2`, so it vanishes on the Bott class of every commuting-twist
    `Z^2 < M`. Voiculescu pairs therefore cannot occur on such a `Z^2` inside
    an `M`-model. Windings pulled back from finite-index subgroups die under
    transfer, because `H_2(M;Q) = 0`. Determinants see only `d mod 3`
    (`deligne-sector-determinants-see-only-dimension-mod-three`).
  - *Conclusion.* An entropy-measure proof of this gate would have to use a
    norm-level invariant that is not a restatement of the gate, and none is
    known. The gate stays OPEN. Live routes are unchanged: (A) with (B_op),
    the Schreier cellular floor, and the HS gap.

- **2026-09-19, swarm-0917-w19-w19-deligne-pull (reframing, transplanter): superrigidity plus Deligne's
  finite-quotient order cannot see (R-a); the approach is DEAD, the gate stays OPEN.**
  - *Setting.* Take an honest `rho : M -> U(d)` with `eps = ||rho(t_s) - omega I||` small. This is the
    input to (B_op) `mod-s2-exact-representations-have-an-opnorm-torelli-scalar-gap`. Put `G = cl rho(M)`
    and `H = cl rho(I_2)`, as in `mod-s2-near-scalar-torelli-closure-dichotomy`.
  - *What the transplant gives.* Neither item is in the graph as a claim.
    - (S1) `[G : H] < infinity`, so `G^0 = H^0`. Proof: `H` is closed and normal in `G`, so `G/H` is a
      compact Lie group. It embeds in some `U(N)` by Peter-Weyl, and `Sp_4(Z) = M/I_2` maps densely into
      it. Margulis superrigidity with the congruence subgroup property (for `Sp_4`, real rank 2; not
      pinned in the graph) forces finite image. Hence `G/H` is finite.
    - (S2) In every finite quotient `Q` of `Gamma~_count = M/ker(count)`, the order of `t_s` is prime
      to 3. Proof: `t_s` is central there. If `3` divides its order `n`, then `Q/<t_s^3>` is a finite
      quotient of `E_3` in which `t_s` has order exactly 3. That contradicts
      `Res_fin(E_3) = C_3` (`deligne-triple-cover-finite-residual-is-center`).
  - *Where it dies: the step "exclude `omega I in cl[H,H]`", i.e. residue (R-a).*
    - (S1) says `rho` is controlled by `G^0 = H^0` up to a finite component group. (S2) and the Frobenius
      result (`mod-s2-finite-image-near-scalar-reps-are-torelli-abelian`) settle only the finite-image
      part, which is already done. Determinants see only `dim mod 3` (PC6/CD4).
    - Every certificate in this family reads only these invariants:
      - the finite group `G/G^0` and the image of `t_s` in it;
      - orders of `t_s` in finite quotients;
      - `det` and `Tr log` data;
      - the Zassenhaus smallness of the generators `g_x = omega^-1 rho(t_x)`.
    - All of these are compatible with the model configuration `G^0 = H^0 >= SU(3)`, with `omega I` in the
      semisimple part `[H^0, H^0]`. Examples: two `eps`-near-identity elements of `SU(3)` topologically
      generate `SU(3)`, `det = 1 in mu_5`, `3 | d`, and `G/G^0` is trivial.
    - The invariant this family never touches is *whether the central scalar `omega` lies in the connected
      semisimple part of the Torelli closure*. To decide it, one must use the `M`-relations (lantern,
      chain) on the `g_x` inside `H^0`, not on quotients of it.
  - *Consequence.* Compact-closure, superrigidity and finite-quotient reframings of (B_op) all reduce to
    (R-a) together with (R-b) of `mod-s2-near-scalar-torelli-closure-dichotomy`, and add nothing past
    (S1). A refutation of (B_op) through infinite-image `rho` must realize (R-a). Candidates are
    TQFT-type representations whose Torelli closure contains a copy of `SU(3k)`. The graph has no
    computation of separating-twist spectra for these beyond the Jones `(3,3)` family, and that
    computation is the natural next test.
