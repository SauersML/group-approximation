---
rg: 2
id: torsion-free-sofic-exact-mf-radical-over-z
kind: claim
title: A torsion-free finitely presented sofic group has a proper Kazhdan MF radical with quotient Z
root: true
goal: true
distinct_from:
  torsion-free-finitely-presented-non-mf: That established existence theorem supplies torsion-freeness and finite presentation but its known witness is nonsofic and has full, rather than proper, MF radical.
  literal-mf-radical-is-unsquared-defect: The literal group is finitely presented and sofic with an exact proper radical, but it has Clifford two-torsion and its radical is not a Kazhdan torsion-free kernel.
  compression-wreath-five-radicals-coincide: Those sofic finite-perfect-lamp examples have exact proper radicals but contain finite torsion, are only finitely generated, and their radicals are locally finite rather than Kazhdan.
  defect-saturation-full-mf-radical: That gives a finitely presented torsion-free Kazhdan group with full MF radical; soficity is not known and there is no visible quotient.
  simple-sofic-total-mf-radical: That gives a countable simple sofic full-radical group but supplies neither finite presentation, torsion-freeness, nor property (T).
artifacts:
  - research/split-cyclic-kazhdan-defect-exact-mf-radical.md
  - research/mapping-torus-mf-radical-lies-in-finite-residual.md
  - research/exact-kazhdan-radical-kernel-cannot-be-lef.md
  - research/torsion-free-sofic-extrinsic-kazhdan-defect-kernel.md
  - research/fp-kernel-crosses-alekseev-thom-open-problem.md
  - research/artifacts/torsion-free-exact-radical-team-audit-2026-08-26.md
  - research/artifacts/torsion-free-exact-radical-breakthrough-round2-2026-08-26.md
  - research/titz-witzel-mapping-tori-are-virtually-products.md
  - research/titz-witzel-exact-kazhdan-mf-radical-over-z.md
  - research/titz-witzel-soficity-is-one-finite-csp.md
  - research/titz-witzel-sofic-gate-two-generators-four-approximate-relators.md
  - research/fp-mapping-torus-iff-finite-automorphic-presentation.md
  - research/artifacts/torsion-free-exact-radical-breakthrough-2026-08-26.md
  - GroupApproximation/Kazhdan/KazhdanFiniteGeneration.lean
  - research/artifacts/torsion-free-full-mf-radical-2026-08-19.md
  - research/finite-outer-order-radical-witnesses-cross-alekseev-thom.md
  - research/ollivier-wise-z-torus-kernel-not-finitely-presented.md
  - research/automorphic-sofic-kazhdan-kernel-with-full-mf-radical.md
  - research/titz-witzel-smallest-kernel-not-mf.md
  - research/torsion-free-sofic-quotientless-kazhdan-group-exists.md
  - research/sofic-hyperbolic-stages-give-quotientless-kazhdan-monster.md
  - research/relation-gaps-forbid-fp-mapping-tori.md
  - research/rel-hyperbolic-hosts-make-witness-powers-host-inner.md
---

There exist a group `G` and a subgroup `K normal G` such that

```text
G is finitely presented, torsion-free and sofic,
K is nontrivial and has property (T),
Rad_MF(G) = K,
G/K ~= Z.                                              (TFZ1)
```

Consequently `G` is hyperlinear and non-MF, its MF radical is proper and
computed exactly, and precomposition with `G->Z` gives, for every countable
MF group `M`, a bijection

```text
Hom(Z,M) ~= Hom(G,M).                                  (TFZ2)
```

Preferred strengthening: `K` itself can be chosen finitely presented and
normally generated in `G` by one element.

The finite-presentation part of that strengthening is not a routine bonus.
By
`fp-kernel-crosses-alekseev-thom-open-problem`,
it would produce a finitely presented, sofic, property-`(T)`, non-residually-
finite group and therefore answer Alekseev--Thom Open Problem 6.1.  The base
target deliberately avoids that additional open problem: property `(T)`
already makes `K` finitely generated, but `K` need not be finitely presented.

Every witness necessarily has a sofic kernel with no nontrivial finite
quotient.  This is much stronger than non-residual-finiteness.
Indeed `K` is a subgroup of the sofic group `G`, property `(T)` makes `K`
finitely generated, and every extension with quotient `Z` splits after
choosing a lift of `1`.  By
`mapping-torus-mf-radical-lies-in-finite-residual`, the MF radical of the
resulting mapping torus is contained in the finite residual of `K`.  Equality
with `K` therefore forces the finite residual to be all of `K`.

Moreover, the kernel can never be LEF.  Indeed LEF implies operator-MF, and
the Dadarlat--Ozawa--Thom theorem gives every infinite operator-MF Kazhdan
group an infinite residually finite quotient.  Such a quotient produces a
nontrivial finite quotient, contradicting the previous paragraph.  Thus the
required kernel occupies the genuinely approximate region

```text
sofic but non-LEF, property (T), and no nontrivial finite quotient.
```

In particular, no marked limit of finite groups can supply it; this closes
the former alternating-mother branch.  See
`exact-kazhdan-radical-kernel-cannot-be-lef`.

The intended construction is a split extension

```text
G = K semidirectProduct_phi Z
```

with a Kazhdan subgroup `L<=G` satisfying `D_G(L)=K`.  The analytic lower
inclusion is already unconditional and kernel-checked.  The sharp remaining
obligation is an extrinsically defect-saturated, sofic Kazhdan kernel with no
nontrivial finite quotient.  It is not necessary to prove that `K` has full MF
radical before adjoining `Z`; that stronger arithmetic route remains
available separately.

The surviving candidates are now sharply separated.  Proving soficity of the
arithmetic single-defect saturated group would solve the target by taking its
direct product with `Z`; this would also cross Alekseev--Thom Open Problem 6.1.
For a Titz--Witzel simple Kazhdan lattice, every cyclic mapping torus is
virtually a direct product because its outer automorphism group is finite.
The kernel is already unconditionally non-MF with full MF radical by
`simple-kazhdan-groups-have-full-mf-radical`.  That route therefore succeeds
exactly when one such lattice is proved sofic.  The original twelve-equation
finite-permutation gate `titz-witzel-soficity-is-one-finite-csp` is now
Tietze-reduced by
`titz-witzel-sofic-gate-two-generators-four-approximate-relators` to one
exact involution, one arbitrary permutation, four approximate equations and
the separated word `u^8`.  The Elek--Szabo simple sofic
envelope supplies neither
torsion-free nor Kazhdan control.  No construction presently in Cairn or in
the audited primary sources closes any of these surviving seams.

In particular, `titz-witzel-exact-kazhdan-mf-radical-over-z` proves
unconditionally every clause of `(TFZ1)` and `(TFZ2)` except soficity and the
consequent hyperlinearity assertion: taking `G=K x Z` already gives finite
presentation, torsion-freeness, the exact proper Kazhdan radical, quotient
`Z`, non-MF, finite presentation of `K`, and one-element normal generation.

**Correction (2026-09-13, lane ex-fp-kazhdan-titz-witzel).** The two paragraphs above rest on
`simple-kazhdan-groups-have-full-mf-radical`, which is refuted
(`simple-kazhdan-lef-group-from-minimal-subshift`).
- For a Titz Mite--Witzel kernel `K`, whether `K` is MF is open (`titz-witzel-residual-is-mf`).
- `Rad_MF(K x Z)` is `K` if `K` is not MF, and trivial if `K` is MF.
- So the Titz--Witzel route to this root needs two things: some kernel is sofic, and that kernel
  is not MF.
- `titz-witzel-exact-kazhdan-mf-radical-over-z` is open, not established. Its correction records
  the two cases. An MF kernel would instead be hyperlinear (`kazhdan-mf-hyperlinear-fragment`).

## Attempts

- **2026-09-18, swarm-0917-w9-w9-titz-break (breaker, calibration).  Status: OPEN.**
  - New MF-killing criterion `kazhdan-centralizer-commuting-conjugates-kill-derived-subgroup`:
    `L` Kazhdan, `uLu^-1 <= L`, `C <= C_G(L)` with `[uCu^-1, l uCu^-1 l^-1] = 1`, and
    `D <= [C,C]` Kazhdan and normalized by `C` give `<<D>> <= Rad_MF(G)`.  It needs no
    normality and no local finiteness.
  - Heuristic refuted by `torsion-free-kazhdan-lamp-wreath-radical-has-kazhdan-subgroups`:
    `W = Gamma(3)^(X) semidirect H_aff` is torsion-free, finitely generated and sofic, and its
    MF radical (computed exactly) contains infinite Kazhdan subgroups.  So an obstruction to this
    root cannot rest on "sofic torsion-free radicals contain no infinite Kazhdan subgroup".  It
    must use that the radical is Kazhdan, that `G/K ≅ Z`, or finite presentation.
  - Calibration for this root:
    - (KC3) inside a sofic group with a Kazhdan compressor and infranormal `L`, the criterion is
      vacuous;
    - (KC4) for a normal Kazhdan radical reached through a single root, it is subsumed by
      `normal-kazhdan-defect-non-mf`.
    So the criterion does not yet produce an exact Kazhdan radical here.  The surviving routes
    need non-infranormal sources or a compressor of nonzero degree.

- **2026-09-18, swarm-0917-w10-w10-titz-last1 (last mile, reframing).  Status: OPEN.**
  - *Closest route and its obstruction.* The Titz--Witzel route has the fewest open
    prerequisites. Its holes are soficity of `Gamma_1^2` and non-MF of a residual. It lies wholly
    inside the finite-outer-order region, and so does the defect-core route (`phi = id`).
  - *New theorem* `finite-outer-order-radical-witnesses-cross-alekseev-thom` (ESTABLISHED, via
    `-proof`), called FO-AT.
    - A witness whose `[phi]` has finite order `r` in `Out(K)` contains an index-`r` subgroup
      `K x Z`, and that subgroup is again a witness with the same kernel.
    - `(K x Z, K)` is a witness exactly when `K` is nontrivial, finitely presented, torsion-free,
      sofic and Kazhdan with `Rad_MF(K) = K`.
    - Such a `K` answers Alekseev--Thom 6.1.
    - Dichotomy: every witness is either (AT), with `K` finitely presented and 6.1 answered, or
      (IO), with `K` infinitely presented, `[phi]` of infinite outer order, and `(FAP1)`.
    - Named invariant: the order of `[phi]` in `Out(K)`. Every finite value is at least as hard as
      6.1. This includes every kernel with finite `Out(K)`, such as all Titz--Witzel residuals.
  - *New decomposition of region (IO).* Descent through `Rad_MF(K)` splits it in two.
    - (IO-int), `Rad_MF(K) = K`. Before this attempt it had no route. The new route
      `exact-mf-radical-over-z-via-automorphic-full-radical-kernel` requires the new OPEN claim
      `automorphic-sofic-kazhdan-kernel-with-full-mf-radical`, whose parts can each fail on their
      own:
      - (P1) a finitely generated torsion-free sofic Kazhdan group with no nontrivial MF quotient;
      - (P2) a finite two-sided automorphic presentation for one automorphism.
      A refutation of (P1) kills (IO-int) and the whole finite-outer-order region together.
    - (IO-ext) is `mf-kazhdan-quotientless-mapping-torus-exact-radical`, as before.
  - *Route mis-specification found.* `torsion-free-sofic-exact-mf-radical-via-titz-witzel` asks
    for soficity of `Gamma_1^2` and for the existential `titz-witzel-exact-kazhdan-mf-radical-over-z`.
    The latter says some residual is not MF, and it can be witnessed by a different residual. So
    the route does not follow from its requirements. The corrected route
    `exact-mf-radical-over-z-via-sofic-non-mf-titz-witzel-kernel` requires
    `titz-witzel-kernel-sofic` and the new OPEN claim `titz-witzel-smallest-kernel-not-mf`, which
    are about the same kernel. It completes through FO-AT part 2.
  - The stale paragraph above ("That route therefore succeeds exactly when one such lattice is
    proved sofic") is superseded by the 2026-09-13 correction and by this corrected route.
- **2026-09-18, swarm-0917-w12-w12-titz-last1 (reframer, reframing).  Status: OPEN.**
  - New ESTABLISHED dichotomy `permanence-closure-radical-witnesses-have-lef-kernels`. For every
    witness, `G` lies in the sofic permanence closure `𝒫` iff `K` lies in some member of `𝒫` iff `K`
    is LEF.
  - When this holds, `K` is MF with `Rad_MF(K)=1`. The witness is then of extrinsic type (DX) with
    `Q=K`, `K` is not finitely presented, `G` is not LEF, and `(K,phi)` refutes (EKL1).
  - Class kill: no intrinsic full-radical kernel can get its soficity from `𝒫`. This covers (P1) of
    the automorphic route, the arithmetic saturated group and a non-MF Titz--Witzel kernel. The
    invariant is LEF of Kazhdan subgroups, and every member dies at the step LEF ⇒ MF.
  - Decomposition: goal ⇔ (W_lef) or (W_out).
    - (W_lef) is the new route `torsion-free-sofic-exact-mf-radical-via-lef-kernel`. Its only open
      prerequisite is `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`, and there
      soficity is free. That claim needs (L1) a torsion-free quotientless LEF Kazhdan group, (L2)
      failure of (EKL1), and (L3) a finite automorphic presentation of a non-finitely-presented kernel.
    - (W_out) needs a non-LEF sofic Kazhdan kernel certified outside `𝒫`.
  - Consequence: (EKL1) holds iff no witness lies in `𝒫`.
- **2026-09-19, swarm-0917-w14-w14-titz-last1 (reframing).  Status: OPEN.**
  - New necessary gate `torsion-free-sofic-quotientless-kazhdan-group-exists` (SQK): an
    infinite torsion-free sofic Kazhdan group with no nontrivial finite quotient.
    - Every witness kernel `K` satisfies it.
    - The hole of each live route implies it: `titz-witzel-kernel-sofic`, the defect core, and
      the extrinsic kernel.
    - So each route can fail at (SQK) on its own, before any MF-radical, finite-presentation or
      cyclic-action clause is reached.
  - New ESTABLISHED dichotomy `sofic-hyperbolic-stages-give-quotientless-kazhdan-monster`.
    - The Olshanskii--Osin--Sapir torsion-free Tarski monster quotient of a torsion-free
      `Sp(n,1)` lattice has no proper finite-index subgroup, unconditionally: a finite-index
      subgroup is cyclic, which would make the monster amenable and Kazhdan, hence finite.
    - The monster is sofic as soon as its torsion-free hyperbolic stages are, since it is their
      marked limit.
    - Hence (SQK) holds or `nonsofic-hyperbolic-group` holds.
  - **Class killed.** Any refutation of this root through the intrinsic properties it forces on
    `K` (sofic, torsion-free, Kazhdan, no finite quotient) solves the flagship root. So a
    disproof must use finite presentation, the exact radical, or the cyclic action.
  - The monster is not a witness here. Its MF-ness, the radicals of its mapping tori and its
    finite presentation are all unknown.
- **2026-09-19, swarm-0917-w15-w15-titz-follow (obstruction-miner, class kill).  Status: OPEN.**
  - New ESTABLISHED claim `relation-gaps-forbid-fp-mapping-tori`, with
    route `-proof` and the verbatim OOS import `oos-graded-small-cancellation-scales-separate`.
  - *Invariant.* Relation gaps: `N_{≤CR} = N_{≤R} ≠ N`, where `N_{≤R}` is the normal closure of
    the relations of length at most `R`.
  - *Gap lemma.* If `K ⋊_ψ Z` is finitely presented and `L` is the stretch of word lifts of
    `ψ^{±1}`, then at every large `R` a gap of ratio `L` forces `N_{≤R} = N`.
    - The reason is that at such a gap `N_{≤R}` is `ψ^{±1}`-invariant, so `F/N_{≤R} ⋊ Z` is
      sandwiched between two presentations of `P`.
    - So every infinitely presented witness kernel has `L`-bounded gaps over every finite
      generating set. The same holds for split extensions by finitely presented groups.
  - *Class killed.* Kernels with unbounded gaps (UG). This includes every infinitely presented
    graded small cancellation group, and in particular the OOS torsion-free Kazhdan Tarski monster
    `Q`.
    - No torus `Q ⋊_ψ Z` is finitely presented, for any `ψ`. This is unconditional: it needs
      neither `(RF_Γ)` nor any assumption on the outer order.
    - This kills survivor item 4 of `tarski-monster-tori-evade-compression-and-stage-lifts`, and
      with it the whole w14 monster-kernel branch of (L1)/(LK1).
    - The death step is (L3)/(LK2)/(FAP1).
  - *What survives in region (IO).* A kernel with a genuinely new relation in every window
    `[R, LR]`, so that the number of relation scales up to `T` is at least `log_L T`. This is the
    self-similar or branch-type regime, not a sparse limit. Any lacunary or monster construction
    of an (IO) kernel must first be shown to have bounded gaps.
- **2026-09-19, swarm-0917-w16-w16-titz-break (breaker, heuristic falsified).  Status: OPEN.**
  - New ESTABLISHED claim `ollivier-wise-z-torus-kernel-not-finitely-presented`, with route
    `-proof`. It uses the Ollivier--Wise import, Brown's cohomology facts and Stallings--Swan.
  - *Heuristic falsified.* w15 recorded above that the surviving (IO) regime is "self-similar or
    branch-type", and that no Kazhdan group with a finite invariant presentation that is not
    finitely presented is known. Both are false.
    - The Ollivier--Wise Rips construction over `Q = Z` gives a finitely presented, torsion-free,
      hyperbolic `G = N ⋊_φ Z` with `cd G ≤ 2`.
    - Its kernel `N = <x,y>` is Kazhdan, not FP_2, and `[φ]` has infinite outer order.
    - So `N` has a finite two-sided automorphic presentation. Its bounded gaps are forced by the
      w15 lemma, and it is hyperbolic-subgroup-like rather than branch.
  - *Dimension-jump lemma, a class kill.* If `cd G ≤ 2`, `G/N ≅ Z` and `N` is nontrivial Kazhdan,
    then `N` is not FP_2.
    - The invariant is `cd`. The death step is `H^{n+1}(G; ZG) ⊇ H^1(Z; Z[t^±]⊗H^n(N;ZN)) ≠ 0`,
      which forces `cd N ≤ 1`, so `N` is free.
    - Consequence: every witness with `cd G ≤ 2` (one-relator, `C'(1/6)`, `Gr'(1/6)`, aspherical
      2-complex) lies in (IO). The (AT) branch, which would answer Alekseev--Thom 6.1, needs
      `cd G ≥ 3`.
  - *What is left.* (P2)/(L3)/(FAP1) are no longer the hard part of (IO). For a Rips torus the
    remaining obligations are exactly three: `G` sofic, `N` without finite quotients (`G` not
    residually finite), and `N ⊆ Rad_MF(G)` (`G` not MF).
    - All three are open problems about torsion-free hyperbolic groups. So on this route the goal
      lives inside "a sofic, non-residually-finite, non-MF torsion-free hyperbolic group with a
      Kazhdan Rips kernel over `Z`".
- **2026-09-19, swarm-0917-w16-w16-titz-follow (reframer, reframing).  Status: OPEN.**
  - New ESTABLISHED claim `non-mf-tf-hyperbolic-gives-fp-full-radical-kazhdan-group`, with route
    `-proof`. It uses Olshanskii's G-subgroup theorem on `H_0 * P`, the partner `P`, the universal
    MF quotient and FO-AT part 2.
    - Fix any torsion-free non-elementary hyperbolic host `P`. Then "some torsion-free hyperbolic
      group is not MF" is equivalent to: `P` has torsion-free hyperbolic quotients `Q`, injective on
      any prescribed ball, with `Rad_MF(Q) = Q` and `Q = ⟨q, sqs⁻¹⟩`.
    - The mechanism: `X = ⟨r, prp⁻¹⟩` is free and lies in `Rad_MF(H_0 * P)`, and `X` and `P` both
      surject onto one Olshanskii quotient.
    - For a Kazhdan host, `(Q × Z, Q × 0)` meets every clause of `(TFZ1)` and of the preferred
      strengthening except soficity. It is a witness iff `Q` is sofic.
  - *Trichotomy.* One of the following holds:
    - (T1) every torsion-free hyperbolic group is MF;
    - (T2) some torsion-free hyperbolic Kazhdan group is not sofic;
    - (T3) the flagship holds, with a hyperbolic product kernel.

    So refuting even the strengthened flagship forces (T1) or (T2).
  - *New decomposition.* The route `exact-mf-radical-over-z-via-sofic-hyperbolic-kernel` needs the
    single OPEN `sofic-tf-hyperbolic-kazhdan-group-with-full-mf-radical`. That claim splits into
    (H1) a non-MF torsion-free hyperbolic group, and (H2) soficity of one Olshanskii quotient of a
    fixed `Sp(2,1)` lattice. Each half can fail on its own, and each failure is itself a result:
    - if (H1) fails, (T1) holds;
    - if (H2) fails, a nonsofic hyperbolic group exists.
  - *Relation to the w16 Rips list.* Of the three Rips-torus obligations listed just above, the
    non-residual-finiteness one is redundant here, and soficity is needed for the single group
    `Q` only. There is no Rips step and no automorphism. The price is region (AT), with
    `cd(Q × Z) = cd Q + 1 ≥ 3`, which is consistent with the dimension-jump lemma. An unlanded w14
    branch (commit 3ec242c521) proposed the same common-quotient step followed by a
    Belegradek--Osin Rips step. That branch needed soficity of all torsion-free hyperbolic groups.
  - *Audit note (not edited, outside this lane).* The "Kazhdan host" bullet of
    `hyperbolic-rf-question-reduces-to-one-fixed-host` says every quotient in its item (2) "is
    non-MF". Its proof route never proves this. For a finite-quotient-free hyperbolic Kazhdan group,
    non-MF is the open implication (3) ⇒ (4) of `hyperbolic-rf-question-equals-non-mf-question`. It
    should read "is not residually finite".
  - *Not done.* The converse "hyperbolic witness kernel ⇒ `Rad_MF(K) = K`" needs `Out(K)` finite
    for hyperbolic Kazhdan `K` (Paulin plus property FA_R). That theorem is not imported verbatim.
- **2026-09-19, swarm-0917-w17-w17-titz-break (breaker, class kill and reframing).  Status: OPEN.**
  - New ESTABLISHED import `fa-groups-finitely-many-homs-to-rel-hyperbolic-groups`,
    with route `-citation`. It quotes verbatim Drutu--Sapir Cor. 4.37 (an FA group has only
    finitely many non-parabolic homomorphisms to a relatively hyperbolic group, up to conjugacy),
    their standing assumption and Remark 1.13, and Levitt Thm 1.4.
  - New ESTABLISHED claim `rel-hyperbolic-hosts-make-witness-powers-host-inner`,
    with route `-proof`.
    - *Host-inner theorem.* Let `ψ : K → H` be injective and non-parabolic, with `H` relatively
      hyperbolic. The maps `ψφ^n` have the same image, so Drutu--Sapir gives `m ≥ 1` and `h ∈ H`
      with `ψφ^m = c_h ψ`.
    - Case A: a power `h^j ≠ 1` lies in `ψK`. Then `φ^{mj}` is inner, and the witness is FO-AT (AT).
    - Case B: no such power. Then `ψ(k)h^j` embeds the index-`m` torus `K ⋊ <t^m>` in `H`.
    - Either way `H` is not MF.
  - *Closes the w16 "Not done" item.* A relatively hyperbolic kernel, in particular a hyperbolic
    one, has `[φ]` of finite order and `Rad_MF(K) = K`. So a hyperbolic-kernel witness exists
    **iff** `sofic-tf-hyperbolic-kazhdan-group-with-full-mf-radical` holds. By the lacunary node,
    a kernel quasi-isometric to a lacunary hyperbolic group needs the same claim.
  - *Class kill.*
    - The invariant is the class of `[φ]` in `Out_H(ψK) = N_H(ψK)/ψ(K)C_H(ψK)`. It is torsion
      for every relatively hyperbolic host, and the death step is Drutu--Sapir pigeonhole.
    - Consequences:
      - region (IO), including (IO-ext), contains no relatively hyperbolic kernel;
      - an MF kernel embeds non-parabolically in no MF relatively hyperbolic group;
      - any design that builds `K` inside a hyperbolic group `H` makes `H` non-MF, which solves
        `non-mf-hyperbolic-group`;
      - with `H` torsion-free, it gives (H1), and hence (T2) or (T3) of the w16 trichotomy.
    - The w16 Rips-torus obligation "`G` not MF" is therefore forced for every hyperbolic host, not
      just the torus itself.
  - *Surviving region.* (IO) kernels must be neither relatively hyperbolic nor non-parabolically
    embeddable in an MF relatively hyperbolic group. Acylindrically hyperbolic kernels and hosts are
    not covered: Drutu--Sapir finiteness is not available there.
- **2026-09-19, swarm-0917-w17-w17-titz-break (breaker, calibration).  Status: OPEN.**
  - *Scope.* A screen of four remaining breaker ideas against the graph. None closes a hole. One
    elementary necessary condition on the (XMF) branch is recorded, with proof.
  - *Screened and discarded, with reasons.*
    - Congruence/torsion-free repair of `EL_3(LC(X,Z) ⋊ Z)`: already dead by
      `filtered-torsion-certificates-die-on-perfect-kernels`. Every separated filtration forces
      residual nilpotence, and a perfect kernel admits none.
    - MCG or `Out(F_n)` hosts: they are residually finite, so the Kazhdan kernel would have finite
      quotients. That contradicts `mapping-torus-mf-radical-lies-in-finite-residual`.
    - A `Σ^2` characterization of (IO): by Bieri--Renz, (IO) says only that one of `±χ` lies
      outside `Σ^2(G)`. This merely restates "`K` is not finitely presented", which (IO) already
      assumes, so it gives no new decomposition.
    - Kazhdan-corner reformulation. Write `p` for the Kazhdan projection of `K`, which is central
      and `φ`-invariant in `C*(G) = C*(K) ⋊_φ Z`, and put `B = (1-p)C*(K)`. Then `Rad_MF(G) = K`
      iff `B ⋊_φ Z` has no nonzero `*`-homomorphism into any `∏M_{k_n}/⊕M_{k_n}`, and
      `Rad_MF(K) = K` iff `B` has none.
      - Proof: if `ρ(p) = e ≠ 1`, then `1-e` lifts to projections, so its corner is again of
        this form. Conversely, `σ(g(1-p)) + (1-σ(1-p))` defines a group homomorphism.
      - This is the C*-form of `mapping-torus-mf-radical-descends-through-kernel-radical` together
        with (XMF). Stably finite targets cannot see it
        (`kazhdan-mapping-tori-have-proper-stably-finite-radical`). So it is not new leverage.
  - *Necessary condition (RET, exact return kills).* Let `Q = K/Rad_MF(K)`, with the induced
    automorphism `ψ`. Suppose that for some nontrivial `ρ : Q -> U(C)`, with
    `C = ∏M_{k_n}/⊕M_{k_n}`, some `m ≥ 1` and some `W ∈ U(C)`, we have `ρ∘ψ^m = Ad(W)∘ρ`. Then
    `Rad_MF(G) ≠ K`.
    - Proof, step 1: put `π = diag(ρ, ρψ, ..., ρψ^(m-1))` on `M_m(C)`, which is again of the form
      `∏M/⊕M`.
    - Step 2: let `T` have entries `T_(j,j+1) = 1` for `j < m-1`, `T_(m-1,0) = W`, and zeros
      elsewhere. Then `T` is unitary.
    - Step 3: `T π(q) T* = π(ψ(q))`, so `t ↦ T` extends `π` to a homomorphism of `Q ⋊_ψ Z`. This
      homomorphism is nontrivial on `Q`, and composing it with `G -> Q ⋊_ψ Z` gives the claim.
    - So in any (XMF) witness, `ψ` acts on the unitary-equivalence classes of nontrivial corona
      representations of `Q` without periodic points.
    - This recovers the finite-outer-order kill: take `ψ^m = Ad(k)` and `W = ρ(k)`.
    - RET is the exact-return case of periodization. The approximate-return version is recorded
      dead in the Attempts on `mf-kazhdan-quotientless-mapping-torus-exact-radical`: operator-norm
      error at the wraparound block does not vanish. The exact case is valid, but it applies to
      fewer pairs.
    - Survivors: pairs `(Q, ψ)` whose corona dual has no `ψ`-periodic class. Every nontrivial `ψ`
      of infinite outer order on the LEF subshift groups `EL_3(LC(X,F_q) ⋊ Z)` remains untested.
  - *Next falsifiable step.* Test RET on the `(HH)` pair of need `a111e246`, namely
    `Z wr_(Z[1/2]) BS(1,2)` with `Γ_0 = Z wr Z` and `α = Ad(τ)`. Specifically: does the natural LEF
    corona representation have a `τ`-periodic unitary class? If it does, that candidate dies by
    RET.
- **2026-09-19, swarm-0917-w17-w17-titz-last1 (last mile, class kill).  Status: OPEN.**
  - *Target.* The acylindrical extension that w17-titz-break left open. Does (HI) `ψφ^m = c_hψ`
    hold for acylindrically hyperbolic hosts? If it did, it would clear (IO) of acylindrically
    hyperbolic kernels.
  - New ESTABLISHED import `osin-acylindrical-trichotomy-and-cayley-models`, with route `-citation`.
    It quotes verbatim Osin's Theorem 1.1 (the trichotomy) and Theorem 1.2 (AH1 ⇔ AH2).
  - New ESTABLISHED claim `acylindrical-hosts-break-witness-host-inner-pigeonhole`, with route
    `-proof`. **The extension is false at the pigeonhole step.**
    - The Ollivier--Wise kernel `N` over `Z` acts acylindrically with unbounded orbits on two
      hyperbolic graphs: `Cay(G_OW)`, which is proper but not cobounded, and an Osin Cayley model,
      which is cobounded and non-elementary. So `N` is acylindrically hyperbolic.
    - With host `H = N` and `ψ = id`, the maps `φ^n` are pairwise non-conjugate, because `[φ]` has
      infinite outer order.
    - On `Cay(G_OW)` the Groves--Hull scaling factors are bounded, witnessed at `t^n`. So
      non-divergence, which is all that (T)/FR gives, does not force finitely many classes.
  - *Class killed.* Every attempt to prove (HI), finite outer order, or "host non-MF" for
    acylindrical hosts from these inputs dies at Step 1 of the w17 proof:
    - (T), torsion-free, infinite outer order;
    - a finitely presented, hyperbolic `cd 2` torus;
    - a non-elliptic acylindrical host, whether proper, cobounded, or Kazhdan.
  - *Consequence.* In region (IO), acylindrically hyperbolic kernels survive every such argument.
    Excluding them needs (S), (Q) or (R) of the Ollivier--Wise node.
  - *Not refuted.* The conclusion-level "acylindrical hosts of witness kernels are non-MF" is not
    refuted, because MF of `N` is unknown.
- **2026-09-20, swarm-0917-w20-w20-titz-break (breaker, reframing and calibration).  Status: OPEN.**
  - New ESTABLISHED (unreviewed) claim `mapping-torus-radical-is-pseudo-orbit-recurrence`, with
    route `-proof`. For `G = <S, t | R_0, t s t^-1 = w_s>` and `g ∈ K`: `g ∉ Rad_MF(G)` iff for
    some `δ` and every `ε`, the substitution map `W_d(b) = (w_s(b))_s` on `U(d)^S` has, in some
    dimension `d`, an `ε`-pseudo-orbit of `ε`-quasi-solutions of `R_0` that are `δ`-nontrivial at
    `g`, of length above the covering number of `U(d)^S`. The chain is closed by pigeonhole and
    wrapped by the cyclic block shift.
    - *Witness form.* The obligation is uniform transience of `W_d` on `δ`-nontrivial
      quasi-solutions, at one scale `ε(g, δ)` for all `d`.
    - *Correction.* The death of Attempt 1 of `mf-kazhdan-quotientless-mapping-torus-exact-radical`
      (accuracy on balls of radius `λ^J`) comes from using exact orbits. Re-projected chains need
      only `R_0`, and they are the universal form of every MF approximation of `G`.
  - *Screened, no new node.*
    - (a) Pimsner--Voiculescu `K_0` certificates `n[1 − p] ∈ Im(φ_* − 1)`, with `p` the Kazhdan
      projection of an infinite `K`. They die at the regular trace of `G`: it is `φ`-invariant,
      and `τ(1 − p) = 1`. This is subsumed by `kazhdan-mapping-tori-have-proper-stably-finite-radical`.
    - (b) Degree-4 almost-flat Chern invariants. Already (R4) of
      `mf-radical-is-blind-to-degree-two-windings`.
    - (c) Congruence and Minkowski torsion kills. A duplicate of
      `filtered-torsion-certificates-die-on-perfect-kernels`.
    - (d) Need `a111e246`. Dead, since its (HH) input is refuted by
      `automorphic-compressions-have-no-approximable-hilbert-hotel`.
  - *Next falsifiable step.* Find a candidate `(K, ψ)` for which one can compute
    `Q_ε ∩ N_δ(g)` in small `d` and test the almost-invariant-set condition (4) numerically.
- **2026-09-20, swarm-0917-w20-w20-titz-follow (follow-through on w19, stability-approximation).
  Status: OPEN.**
  - *Step taken.* Of the two w19 survivors of
    `finite-image-exact-kazhdan-torus-models-reduce-to-stage-lifts`, (S1) is killed and (S2) is made
    quantitative.
  - *New ESTABLISHED claim.* `locally-mf-stable-kazhdan-kernels-collapse-torus-radicals`, with route
    `-proof`. Call a finite set `R` of relators of `K` G-complete if it contains `R_Γ` and
    `<S, t | R, t s t^-1 = w_s> = G`. Such sets exist because `G` is finitely presented.
  - *Theorem D.* Suppose a corona model of `G` has kernel lifts that are `o(1)`-close to exact
    representations of `<S | R>`, along the indices where it sees `k ∈ K`. Then Theorem A gives an
    exact multiplicity-free wrap, and (GC) makes this a genuine finite-dimensional representation of
    `G`. So `k ∉ Rad_fin(G)` by Mal'cev.
  - *Corollaries.*
    - (D1) If `K` is Kazhdan and locally MF-stable, then
      `Rad_MF(G) = Rad_LEF(G) = Rad_fd(G) = Rad_fin(G)`.
    - (D2) An MF group that is locally MF-stable is LEF.
    - (D3) If `K` is Kazhdan, locally MF-stable and quotientless, then `Rad_MF(K ⋊_φ Z) = K` for every
      `φ` with a finitely presented torus.
    - (D4) For a witness, every model nontrivial on `K` has stability defect `σ_R > 0` for every
      G-complete `R`.
  - *Class killed.* Every rounding construction of MF models of a torus with `Rad_fin(G) = K`, of any
    image, character field, gap or wrap. The invariant is `dist_R` to `Hom(<S | R>, U(n))`. Every
    member dies at Theorem A plus (GC).
  - *What survives.* (S1) and (S2) merge into (S\*): lifts uniformly far from exact representations
    of every G-complete cover. The surviving part of (S1) is an instability of the finitely presented
    pair `(<S | R_Γ>, <S | R>)`.
  - *New decomposition.* A new route, `exact-mf-radical-over-z-via-locally-mf-stable-kernel`, with
    the single OPEN hole `torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel`. Its
    conditions are (P1'), (Q), (LS) and (P2).
    - (Q) is necessary. (LS) is not.
    - `Rad_MF(K) = K` implies (Q) and (LS), so the route contains the automorphic route.
    - A solution with an MF kernel would be LEF, so it would also refute (EKL1).
  - *Next falsifiable step.* Decide whether a Kazhdan group without finite quotients that is MF, for
    example the LEF group `EL_3(LC(X, F_q) ⋊ Z)` of the EKL2 correction, can be locally MF-stable.
    Otherwise, prove that (LS) together with (Q) forces `Rad_MF(K) = K`, which would show that the
    new route is no weaker than the automorphic one.
- **2026-09-20, swarm-0917-w21-w21-titz-last1 (last mile, class kill, cohomology-index).  Status:
  OPEN.**
  - *Target.* The MF half of the w20 hole `torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel`,
    which is on the landing branch. Its condition (LS) is local MF-stability.
  - New ESTABLISHED (unreviewed) claim `mf-stable-kernels-lack-lef-nonsplit-central-extensions`,
    with route `-proof`. It has no prerequisites.
    - Theorem (WK): if a central `Z`-extension `Ktilde` of `K` is LEF and `<t>` meets
      `[Ktilde, Ktilde]`, then `K` is not LS. The rounding already fails for one relator
      `zhat ∈ N ∩ [F,F]`.
  - *Invariant and death step.* The invariant is the integer winding `(1/2πi) Tr log zhat`.
    - Scalar-twisted irreducibles of the finite LEF approximations of `Ktilde` are asymptotic
      representations of `K` with winding `n_i d / m_i ≠ 0`.
    - Exact tuples on `{zhat}` have winding `0`, and a geodesic homotopy preserves the winding.
    - So the approach dies at the (LS) rounding step for `R = {zhat}`.
    - Sanity check: for `Z^2` and the Heisenberg group this is Voiculescu's pair.
  - *Consequence.* Every w20 kernel is perfect, since it is Kazhdan with (Q). So it has **no nonsplit
    LEF central `Z`-extension**.
    - In the MF regime the kernel is LEF (D2). The MF half now needs a LEF, perfect, quotientless
      Kazhdan group none of whose nonsplit central `Z`-extensions is LEF.
    - Or it needs `Hom(H_2(K;Z), Z) = 0`.
  - *Not decided.* Whether an MF model of `Ktilde`, rather than a LEF one, already gives a nonzero
    winding. See remark (R2) of the route.
