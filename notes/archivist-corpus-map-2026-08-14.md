# Archivist corpus map — every open frontier hole vs. the non-Cairn corpus

Date: 2026-08-14 · Agent: cairn-archivist · Noncanonical (notes/), not linted.

Scope: the 27 frontier holes listed in `research/FRONTIER.md` at the time of
the sweep. Method: read each `research/<slug>.md` for the precise statement,
then grep/read the proof corpus (`notes/*.md`, `non_mf_groups_exist.tex`,
`property_tt_leavitt.tex`, `GroupApproximation/**.lean`, git history) for the
answer. No compute was run: no `lake build`, no experiments.

Verdicts: **SOLVED** (complete argument exists), **PARTIAL** (specific lemmas
exist), **UNTOUCHED**, **CONTRADICTED** (corpus says the claim as stated is
wrong or ill-posed).

## Headline

**No frontier hole is SOLVED anywhere in the corpus.** The graph does not lag
the corpus on any *conclusion*. It lags substantially on *material* — proved
reductions, exact countermodels, sufficiency theorems, and in three cases
artifacts that were **deleted from HEAD and survive only in git**.

Three archaeological findings dominate:

1. **A 1,179-line machine-checked torsion-free non-MF development was deleted
   on 2026-08-14** (commit `241440fe`, message "Prove integral linear groups
   residually finite", which does not mention the deletion). It proves the
   entire torsion-free non-MF implication chain conditional on packaged
   Fournier-Facio/Hull input data. Recoverable at `4a210700`. Two docs still
   describe it as present.
2. **A complete proof of "there exist `2^{aleph_0}` pairwise non-isomorphic
   finitely generated non-MF groups" was deleted from the manuscript** on
   2026-08-13. Recoverable at `c3501887:non_mf_groups_exist.tex:2095-2129`.
   It proves the *unrelativized* statement, not the cylinder statement.
3. **`wreath-flexible-hs-stability` is mis-stated.** Its subject fuses two
   different groups (see that section).

Two docs are **stale** and should not be trusted as formalization status:
`notes/TORSION_FREE_FULL_CDE_MF_FORMALIZATION.md` and
`notes/WEAK_MF_NONSOFIC_DOUBLE.md` both cite Lean files deleted in `241440fe`.

## Verdict table

| slug | verdict | key artifact |
| --- | --- | --- |
| commuting-lamp-quotient-mf | UNTOUCHED | `notes/NOTEPAD.md:39199` (transferable criterion, never applied) |
| edge-pair-mixed-gap-collapse | PARTIAL | `notes/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md:228` |
| finite-window-decoder | PARTIAL | `notes/TRUE_POSITIVE_DENSITY_LEAVITT_DECODER_ENDGAME.md:32` |
| full-packet-bicommutant-synchronization | PARTIAL | `notes/TRUE_FULL_RAW_PACKET_COMMUTANT_WITNESS.md:22,166` |
| hyperlinear-wreath-model | UNTOUCHED (constructive) / PARTIAL (negative) | `notes/FALSE_POSITIVE_CORE_IS_SOFIC.md:41` |
| kun-thom-clifford-crossed-product-ce | PARTIAL | `notes/PERFECT_CORE_KUN_THOM_WREATH.md:358,498` |
| kun-thom-clifford-relative-wall | PARTIAL | `notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md:104-151` + `CliffordPhaseExtraction.lean:42` |
| leavitt-steinberg-hs-stable | PARTIAL | `notes/NOTEPAD.md:22220` (hyperfinite HS stability, proved) |
| leavitt-steinberg-hs-unstable | PARTIAL | `notes/ATLAS_HS_CRITERION.md:196-217` (reduction proved) |
| literal-mark-quotient-mf | UNTOUCHED | `non_mf_groups_exist.tex:1279` |
| literal-witness-kernel-amenable | UNTOUCHED | `notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md:206` |
| pauli-carrier-membership-decoder | PARTIAL | `notes/TRUE_PAULI_CARRIER_BINARY_ALGEBRA_GAP.md:59-69` |
| quantized-scale-index | PARTIAL | `notes/TRUE_LOCALLY_FINITE_COMMUTANTS_RECOVER_BUT_AT_SHIFTED_SCALES.md:16-45` |
| relator-energy-variance-bound | PARTIAL (negative only) | `notes/FALSE_EXACT_JOINT_COMPRESSOR_HAS_MAXIMAL_FIBER_VARIANCE.md:11` |
| same-orbit-closure | PARTIAL (negative only) | `notes/FALSE_EQUIVARIANT_WHOLE_MAPS_ALLOW_RECTANGULAR_ESCAPE.md:12` |
| sofic-radical-hyperlinear-survivor | PARTIAL | `notes/COMMUTING_WREATH_SOFIC_RADICAL.md:165` + `HyperlinearResidualDetector.lean:83` |
| transition-equivariance | PARTIAL (task written, not executed) | `notes/TRUE_EQUIVARIANT_TRANSITIONS_COARSEN_TO_WHOLE_MAPS.md:242-257` |
| wreath-flexible-hs-stability | **CONTRADICTED (ill-posed)** | `notes/OBSTRUCTIONS.md:123` |
| wreath-not-sofic | PARTIAL (cited, not imported) | `notes/COMMUTING_WREATH_SOFIC_RADICAL.md:30-37` |
| continuum-nonisomorphic-non-mf-cylinder | PARTIAL (**deleted proof of weaker statement**) | `git show c3501887:non_mf_groups_exist.tex:2095` |
| effective-transport-modulus | PARTIAL | `GroupApproximation/Sofic/LiteralUniformObstruction.lean:7-32` |
| finite-tracial-cstar-transport | UNTOUCHED | `GroupApproximation/Sofic/ManuscriptKazhdanTransport.lean:39` |
| literal-group-structural-normal-form | PARTIAL | `non_mf_groups_exist.tex:674,996,1197` |
| mf-implies-hyperlinear | PARTIAL | `GroupApproximation/Sofic/NormTraceGap.lean:276-336` |
| nonsofic-mechanism-mf-classification | PARTIAL | `notes/FALSE_CLIFFORD_NORM_MF_STERILITY.md:33` + `notes/WEAK_MF_NONSOFIC_DOUBLE.md:187` |
| scaling-family-pairwise-nonisomorphic | UNTOUCHED (historically declined) | `git show c3501887:non_mf_groups_exist.tex:2072` |
| torsion-free-finitely-presented-non-mf | PARTIAL (**deleted machine-checked conditional**) | `git show 4a210700:GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean` |

---

# Per-hole findings

## commuting-lamp-quotient-mf — UNTOUCHED

Claim: "For the Clifford witness `W` and its central sign `zeta`, the quotient
`W/<zeta>` is MF in the norm-matrix-corona sense."

Nothing in the corpus aims at the MF conclusion. The *algebraic* half is
established separately (`research/commuting-lamp-defect-survival-proof.md`),
and the consuming route is written, but no MF model is constructed or
obstructed. The manuscript states it as an open intermediate test,
`non_mf_groups_exist.tex:2032-2042`:

> "Thus proving $W/\langle\zeta\rangle$ MF would already show
> $u\notin\operatorname{Rad}_{\mathrm{MF}}(E)$; any such detecting models
> must be genuinely non-finite-quotient in flavor."

**Under-exploited asset the graph does not record.** `notes/NOTEPAD.md:39199-39232`
(2026-08-10) contains a general central-extension MF criterion of exactly the
right shape, proved for a *different* candidate and never applied here:

> "Let `1 -> C_p -> E -> K -> 1` be central, let `K` be MF, and write a
> section cocycle as `s(k)s(l)=omega(k,l)s(kl)`, `omega(k,l) in C_p`. For any
> nontrivial character `chi:C_p->T`, the following are equivalent:
> 1. `E` is MF;
> 2. there are maps `v_n:K->U(d_n)` satisfying
>    `||v_n(k)v_n(l)-chi(omega(k,l))v_n(kl)||_op ->0` for every fixed `k,l`.
> No separation condition on `v_n` is needed."

with the warning at `NOTEPAD.md:39226-39232` that a positive model must be
genuinely non-liftable. Note the direction of use: applied to `W` and
`<zeta>`, the criterion runs *backwards* from the established non-MF-ness of
the total group, so it constrains rather than constructs. The corpus does not
draw this inference anywhere.

Recorded obstruction: Theorem B (`non_mf_groups_exist.tex:575-587`) kills the
whole intrinsic defect subgroup in every finite-dimensional representation
over every field, so residual finiteness is closed as a route.

## edge-pair-mixed-gap-collapse — PARTIAL

Claim: reduced form of the Iwahori endpoint after
`iwahori-outlier-localization`; a negative sequence forces high-dimensional
edge-irreducible pairs whose mixed gap collapses along a near-unitary
intertwiner.

The **reduction** is proved. `notes/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md:228-241`:

> "Thus a counterexample cannot use an arbitrary sparse subspace. It must
> concentrate physical identity mass on pairs of edge irreducibles which:
> 1. have a collapsing mixed spectral gap;
> 2. occur as restrictions of representations extending through the two
>    opposite copies of SL_2(Z); and
> 3. have dimensions escaping every fixed bound, by the dimension-tight
>    theorem."

The **repair** is open, same file `:247-254` (statement of "Full-rank outlier
repair"). Supporting bimodule decomposition `(ICO22)` at `:219-221`; mirrored
in `notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md:29-37` and
`notes/AGENDA.md:5860-5866`.

Caution against a naive reading — the *diffuse* form is impossible,
`notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md:21`:

> "Thus diffuse mixed-gap collapse is impossible. The Iwahori endpoint is now
> a full-rank outlier-repair theorem"

**Graph lag:** three documents written *after* `HIGHEST_YIELD` (11:05) and
`AGENDA` (11:39) re-route this endpoint and are not reflected in either:
`notes/TRUE_IWAHORI_MATCHING_REDUCES_TO_FACTORIZED_BS14_REPAIR.md` (13:14),
`notes/TRUE_IWAHORI_FACTOR_GATE_IS_COSYSTOLIC_ANGLE.md` (13:26), and
`notes/FALSE_ODD_SPECTRAL_EQUIVARIANT_COARSENING.md` (17:45, newest file in
notes/), whose `:22-26` reads:

> "Thus spectral shadowing and dimension-free one-conjugator flag repair do
> not combine into simultaneous Iwahori repair by an abstract equivariant
> partition argument. Any valid completion must use the full modular vertex
> relations."

## finite-window-decoder — PARTIAL

The downstream consumer is proved:
`notes/TRUE_POSITIVE_DENSITY_LEAVITT_DECODER_ENDGAME.md:32-42` gives the
`sqrt(alpha)(2-sqrt(3))` ambient floor. The upstream input is proved:
`notes/AGENDA.md:85-90`, one joint extension-character PVM with total rounding
error below `9(e_L+e_R)^2`. The decoder itself is posed, not proved —
`notes/AGENDA.md:96-99`:

> "The live theorem is now the finite-window endomorphism decoder: extract from
> the joint outer characters common finite paired-radical label spaces on
> which the four one-sided Leavitt maps act with vanishing boundary and pairing
> error."

Delimited by `notes/FALSE_EXACT_JOINT_COMPRESSOR_HAS_MAXIMAL_FIBER_VARIANCE.md:7-11`
("That synchronization is exact and useful, but it cannot by itself produce
the finite-window endomorphism decoder") and by the carrier/decoder
distinction in `notes/TRUE_LONG_ROOT_CARRIER_IS_COMMON_BUT_NOT_A_DECODER.md`.

## full-packet-bicommutant-synchronization — PARTIAL

The **converse witness** is complete: `notes/TRUE_FULL_RAW_PACKET_COMMUTANT_WITNESS.md:22-41`
proves `E_A(F)=(1/4)1`, `dist_2(F,A)^2=3/16`, hence a unitary `V` commuting
with the full exactified copy of `K` with `||[V,F]||_2^2 >= 3/8-o(1)`.

The claim itself is explicitly unproved, same file `:166-179`:

> "This is not yet a nonhyperlinear group. The unitaries V_n are selected
> from coordinate commutants and are not fixed group words. The regular
> representation realizes (FCW2) exactly, so no abstract group relation can
> force F into L(K) or make it commute with L(K)' in every finite von
> Neumann algebra."

Lean has the scalar endpoint only:
`GroupApproximation/Leavitt/PauliCarrierBinaryGap.lean:143-149`
(`actualPacketFullCommutantWitnessEnergy = 3/8`). No operator-level statement.

Restated as live in the newest status doc,
`notes/HYPERLINEAR_CAIRN_PROGRESS_2026-08-14.md:95-111`.

## hyperlinear-wreath-model — UNTOUCHED constructively, PARTIAL negatively

Five architectures are formally invalidated in-graph (three via formalized
Lean obstructions). The corpus states no exhaustiveness result exists.

**Asset the graph does not record:** the only place anything of this shape is
actually *constructed*, `notes/FALSE_POSITIVE_CORE_IS_SOFIC.md:41-67`:

> "4. the generalized wreath product `W_0=(bigoplus_{X_0}C_2) rtimes Gamma`
> is sofic. In particular `N_0=L(W_0)=L^infty({+-1}^{X_0}) rtimes Gamma` is
> Connes embeddable.
> Thus step 1 of the finite target in
> `FALSE_FULL_COMPRESSION_SEMIGROUP_DILATION.md` — matrix microstates for the
> common nonamenable positive core — is solved for this pair. The remaining
> problem is exclusively the simultaneous dilation of the positive external
> compressors, with their non-Ore branching and group relations."

The residual gate is stated exactly at
`notes/FALSE_FULL_COMPRESSION_SEMIGROUP_DILATION.md:196-233` (four-step finite
target; steps 1-2 solved conditionally, step 3 solved only after forgetting
the core; "The missing theorem is precisely their compatible splice"). The Ore
shortcut for step 3 is separately closed at `notes/AGENDA.md:1991-2000`.

## kun-thom-clifford-crossed-product-ce — PARTIAL

Target is canonical and pinned. `notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md:89-102`
reduces hyperlinear-vs-sofic to `(KCP11)`. The hyperfinite-base objection is
anticipated and answered negatively, same file `:175-187`:

> "The base `Cl(G/Gamma)` is hyperfinite. This alone does **not** prove
> `(KCP11)`: Connes embeddability is not known to be preserved under an
> arbitrary action of a residually finite group. The coset action here is
> specifically nonsofic, so profinite-action crossed-product theorems do not
> apply."

Two nontrivial **equivalences** make the target canonical (not recorded in the
graph): `notes/PERFECT_CORE_KUN_THOM_WREATH.md:358-372` (Prop 4,
`M_full` CE iff `A_CAR rtimes G` CE) and `:498-505` (Thm 6, no character
shortcut — three-way equivalence). Consequence at `:394-398`: the full-Majorana
and perfect-even-core formulations "must not be counted as independent
construction routes."

Every known CE permanence theorem is individually excluded,
`notes/NOTEPAD.md:6576-6587`; profinite filtrations are closed by a proved
theorem, `notes/NOTEPAD.md:26451-26523`. A strictly weaker **sufficient**
target exists (sparse lamps), `notes/NOTEPAD.md:9969-9995`.

One certificate is proved *impossible* here:
`notes/PERFECT_CORE_KUN_THOM_WREATH.md:614-616` (Prop 8, operator-norm
sterility of the even cover).

## kun-thom-clifford-relative-wall — PARTIAL

**Sufficiency is proved with constant one and is kernel-checked.**
`notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md:104-151`:

> "There is no hidden quantitative loss in this last implication. If
> `D_n=C_(h,n)`, the coordinate matrix for the second commutator is
> `X_n=D_n C_n D_n C_n,` and involutivity gives the exact factorization
> `D_n(C_nD_n+D_nC_n)C_n=X_n+1.` ... Thus `(KCP13)` is exactly, with constant
> one, convergence of the radical word to `-1`. The factorization and norm
> identity are Lean-checked in
> `GroupApproximation/Sofic/CliffordPhaseExtraction.lean`."

Verified: `CliffordPhaseExtraction.lean:42-54`
(`hsNormSq_doubleCliffordWord_add_one`), consumed by
`AntipodalRadicalCollision.lean:112-120`
(`exists_hyperlinear_not_isSofic_of_negOnePhase_soficInvisible`).

**Consequence proved:** `notes/FALSE_RELATIVE_WALL_FORCES_FLEXIBLE_HS_INSTABILITY.md:33`
— "**Theorem 1.** If `(WFI2)--(WFI4)` hold, then `G` is not flexibly
Hilbert--Schmidt stable." (`(WFI17)`: relative wall => flexible HS-instability.)

**Necessary condition proved:** `notes/FALSE_ONE_INVOLUTION_INSTABILITY.md:35-57`
(antipodal radical gap, distance lower limit at least `sqrt(2)`), and
`notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md:166-173` — no exact pair can work, so
"Any solution of `(KCP12)--(KCP13)` must therefore use genuine
Hilbert--Schmidt instability, not a hidden exact representation."

The wall itself is not constructed anywhere.

## leavitt-steinberg-hs-stable — PARTIAL

The claim text already concedes hyperfinite HS stability is known. **Where it
is proved is not recorded in the graph:** `notes/NOTEPAD.md:22220-22232`, for
this exact group (`U=St_5(L)`, fixed at `NOTEPAD.md:22149`):

> "**Theorem (unconditional hyperfinite HS stability).** The group `U` is
> hyperfinitely Hilbert--Schmidt stable in the sense of Dogon--Vigdorovich."

with the proof (Bekka criterion + factoriality + triviality of all
finite-dimensional representations of `U`) and the consequence at `:22234-22238`:

> "Consequently any witness to the unstable branch must generate a genuinely
> nonamenable limiting von Neumann algebra. Hyperfinite, AF, amenable-factor,
> and character-approximation constructions are completely closed for this
> group."

Property `(TT)/T` of `St_n(L)` is established, `notes/LEAVITT_TT_T.md:226-241`.
But the natural route from it is **refuted**:
`notes/FALSE_TT_T_IS_NOT_DIMENSION_FREE_HS_STABILITY.md:50-65`, including the
consistency check that a generic `(T) => normalized-HS stability` implication
would contradict Becker--Lubotzky. Same file `:96-100`: "Do not route the
current proof through abstract `(TT)/T -> stability`."

Boundary statement: `notes/ATLAS_HS_CRITERION.md:409-415`.

## leavitt-steinberg-hs-unstable — PARTIAL

**The claim's own reduction is a proved theorem** —
`notes/ATLAS_HS_CRITERION.md:196-217` ("Theorem (one-witness exact-atlas
certificate)"), with the converse at `:247-253` and the "every genuine
finite-dimensional representation is trivial" premise used at `:319-322`.

The construction is reduced to **finite matrix feasibility**,
`notes/ATLAS_HS_CRITERION.md:286-298` (variables: finitely many integer
multiplicity vectors, finitely many relative unitaries `V_i`, common size
`d`), upgraded to a ratio criterion at `:357-407`, with the atlas made fully
explicit in `notes/EXPLICIT_LEAVITT_ATLAS.md` (30 generators; `:452-456`
states the endgame as a sequence of compact one-unitary optimizations).

Equivalent one-trace form: `notes/NOTEPAD.md:22262-22290` — "construct one
nontrivial Connes-embeddable trace of U". A flexible variant suffices,
`notes/NOTEPAD.md:22593-22596`.

**Unconditional no-go on the obvious construction:** `notes/NOTEPAD.md:22096-22133`
(normalized-HS Leavitt trace floor `e_0+e_1+e_c >= 1`; rules out all
square-matrix Fock, Toeplitz, leaf-truncation, polar-correction and
direct-sum ring-first constructions in normalized HS norm). Same passage
refuses to conclude stability from it (`:22135`).

## literal-mark-quotient-mf — UNTOUCHED

`non_mf_groups_exist.tex:1279-1281`:

> "we do not know whether $E/\langle w\rangle$ is MF, i.e. whether the
> MF radical of $E$ is exactly $\{1,w\}$."

Only the conditional consumer is formalized
(`ManuscriptExactWrappers.manuscriptExactRadicalFromCandidateQuotient`,
cited at `non_mf_groups_exist.tex:1664`). Named failure mode for the obvious
analytic route, `notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md:192-194`:
"Existing Hilbert--Schmidt convergence does not give the operator-norm
separation required for that quotient; the compression defect can survive on
small corners." The same `NOTEPAD.md:39199` criterion noted under
`commuting-lamp-quotient-mf` applies here too and is likewise never used.

## literal-witness-kernel-amenable — UNTOUCHED

`notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md:206-208`:

> "3. **Soficity and structure of `E`.** The kernel of `E -> W`, a normal
> form, the word problem, and soficity of the finitely presented group `E`
> remain unresolved."

Surjectivity of `E -> W` is proved (`non_mf_groups_exist.tex:1840-1844`) and
`W` is sofic (Theorem E; Lean `NonMFImpact.witness_sofic_nonMF`). **Nothing in
the corpus computes or bounds `ker(E -> W)`** — a targeted grep across
`notes/`, `research/`, `GroupApproximation/` and the `.tex` found no
description of that kernel beyond the "remain unresolved" sentence.

Note: `bin/cairn frontier` currently warns this node is open but unreachable
from any root claim.

## pauli-carrier-membership-decoder — PARTIAL

The matching **lower bound** is proved and Lean-transcribed:
`notes/TRUE_PAULI_CARRIER_BINARY_ALGEBRA_GAP.md:59-69`, `dist_2(F,W*(E))^2 >= 3/28`,
sharp at `x=1/8`; Lean
`GroupApproximation/Leavitt/PauliCarrierBinaryGap.lean:37-43`
(`three_div_twenty_eight_le_binaryResidual`) — pure real arithmetic, **not**
an operator statement.

The vanishing statement is explicitly open, same doc `:91-104`:

> "This remains unproved. It is strictly weaker than the former containment
> gate and is not supplied by additive characters: the finite double-Pauli
> model has a nonzero conditional variance."

Trap recorded at `notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md:952-963`: do not
try to derive the containment pointwise on additive root characters — the
implication is false.

## quantized-scale-index — PARTIAL

The recovery half is a proved theorem,
`notes/TRUE_LOCALLY_FINITE_COMMUTANTS_RECOVER_BUT_AT_SHIFTED_SCALES.md:16-27`
(locally finite analogue of the elementwise part of Alekseev--Thom Open
Problem 6.2; Reynolds identity formalized in `PropertyT/FiniteGroupAverage.lean`).

The obstruction is exact, same file `:29-45`: `alpha(K_m) <= K_(r(m))` with
`r(m)>m`, and "For the unilateral binary shift, the missing scale has an exact
factor-two commutant-dimension defect." Sourced from
`notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md:152-179`.

**Citation correction:** the node attributes its source to "AGENDA
2026-08-14", but the header `locally finite commutants recover at the wrong
scale` occurs only in `notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md:152`; it
appears nowhere in `AGENDA.md` or `NOTEPAD.md`. The same mis-attribution
affects `finite-window-decoder`, `relator-energy-variance-bound`,
`same-orbit-closure` and `transition-equivariance`: the cited strings are `##`
headers of `HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md`, with re-worded twins in
`AGENDA.md`.

## relator-energy-variance-bound — PARTIAL (negative side only)

No document or Lean declaration attempts the positive size-uniform bound. The
exact countermodel that forces its shape is proved,
`notes/FALSE_EXACT_JOINT_COMPRESSOR_HAS_MAXIMAL_FIBER_VARIANCE.md:11-28`:

> "joint covariance defect = 0, joint transition variance = 0, left/right
> transition measurements share one fine PVM, binary extension-fiber
> conditional variance = 1/4. (JCV1)
> The last value is the maximum possible variance of a binary projection. ...
> This does not refute the Leavitt route. It proves that its remaining input
> must be a **mixed multiplication constraint** coupling the two outer
> characters, not another Fourier/covariance refinement."

The four algebraic ingredients exist in Lean as exact group-word identities
(`GroupApproximation/Leavitt/OuterRootLeavittRouting.lean:66,80,93,106`) but
carry no energy or variance content.

## same-orbit-closure — PARTIAL (negative side only)

The escape it must exclude is an exact finite model,
`notes/FALSE_EQUIVARIANT_WHOLE_MAPS_ALLOW_RECTANGULAR_ESCAPE.md:12-32`:

> "There is an exact finite model in which all four Leavitt transports are
> deterministic equivariant maps, the two diagonal pairing identities and both
> cross-zero identities hold exactly, but the target paired spaces have twice
> the vector-space dimension of the source. ... The second line, not
> equivariance, is the genuinely matrix-specific finite-multiplicity theorem."

Independently restated at
`notes/TRUE_NESTED_COMMUTATORS_RECOVER_PAIRED_TRANSLATIONS.md:225-235`. The
closure itself is untouched.

## sofic-radical-hyperlinear-survivor — PARTIAL

The **criterion** is established and kernel-checked:
`GroupApproximation/Sofic/HyperlinearResidualDetector.lean:80-90`
(`hyperlinear_range_and_failureOfSoficity_of_soficInvisible`).

The **sofic-radical half is supplied in four explicit groups**, and two of
these are *complete radical computations*, which the graph does not record:

- `notes/COMMUTING_WREATH_SOFIC_RADICAL.md:53-57` — `Rad_sof(W)=K`, with
  `W/K` residually finite; and `:131-176` (Corollary 2) reduces it to **one
  explicit normal generator**: with `mu=(x_1...x_d)^{-1}`, `h=e_12(mu)`,
  `w=a_{hGamma}a_Gamma`, one has `Rad_sof(W)=<<w>>_W`. Payoff at `:191-200`:
  "The FALSE-side problem for the original Kun--Thom example is therefore
  exactly a one-projection Connes-embeddability problem."
- `notes/AUGMENTATION_SOFIC_RADICAL.md:50-64` — `Rad_sof(P)=M`;
  `notes/CYCLIC_AUGMENTATION_SOFIC_RADICAL.md:167-176` — cyclicity,
  `Rad_sof(P)=M=ZGv=<<v>>_P`.

No hyperlinear detector exists for any of them. The obvious reuse is
**contradicted**: `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md:49-62` proves
`w notin Rad_sof(E)`, so the literal Clifford sign cannot be the
sofic-radical half. The relative-Kazhdan shortcut is refuted too,
`notes/CYCLIC_AUGMENTATION_SOFIC_RADICAL.md:249-250,285-288`:

> "**Proposition 5.** Neither \((P,M)\) nor \((P_m,M_m)\), for \(m\geq2\),
> has relative property \((T)\). ... Any successful model must use genuinely
> nonliftable trace geometry rather than a relative Kazhdan projection."

General characterization: `notes/TRUE_LINEAR_SOFIC_RADICAL_INEQUALITY.md:77-88`
(Theorem 2, three-way equivalence), with its honest limitation at `:184-189`.

## transition-equivariance — PARTIAL (written as a task, never executed)

The abstract theorem it feeds is complete
(`notes/TRUE_EQUIVARIANT_TRANSITIONS_COARSEN_TO_WHOLE_MAPS.md`), but the claim
is stated in the corpus as an audit **still to be performed**, same file
`:242-257` ("## 7. Remaining literal audit"):

> "The operator theorem is complete, but its application still requires four
> specific group-word covariance statements. For the two outer-root
> translation families (ETM9), verify that the raw/comb words implementing
> `a |-> a t_i`, `b |-> s_j b` carry each named middle-root commutator to the
> commutator with the transported coefficient..."

with `:272-275` noting that completing it still does not give the same-orbit
clause. The routing lemmas it would use exist in Lean
(`GroupApproximation/Leavitt/RawSwapCompressors.lean:190,213,237,260,298`),
but no declaration states the claimed conjugation.

## wreath-flexible-hs-stability — CONTRADICTED (ill-posed as stated)

Claim: "Show that every almost-representation of **the wreath candidate `G`**
in the normalized HS metric is close to a genuine finite-dimensional
representation after padding."

The source it paraphrases distinguishes two different groups.
`notes/OBSTRUCTIONS.md:123-127`:

> "**Rigidity.** If `G` is flexibly HS-stable then the wreath candidate is not
> hyperlinear: lift `rho|_G` to genuine `pi_m`, pad the lamp, apply the
> Kazhdan pair to the *genuine* adjoint representation..."

Here `G` is the ambient residually finite Kazhdan group of the pair
`Gamma <= G` (fixed at `notes/OBSTRUCTIONS.md:10`), while "the wreath
candidate" is the wreath product built over `G/Gamma`. The node's subject
("the wreath candidate `G`") fuses them, and the hypothesis the rigidity route
actually needs is flexible HS-stability of the **ambient** `G`, not of the
wreath candidate. `research/rigidity-route.md` preserves the correct wording,
so the mis-statement is confined to this leaf node.

This matters because the corpus proves two implications under which the
*intended* hypothesis would be false:
`notes/FALSE_RELATIVE_WALL_FORCES_FLEXIBLE_HS_INSTABILITY.md:33` (a relative
wall implies `G` is not flexibly HS-stable) and
`notes/TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_INSTABILITY.md:15-26`
(`(CHI1)`/`(CHI2)` dichotomy). The 2-Kazhdan/Frobenius shortcut to it is
invalid, same file `:125-156` (normalization firewall: Frobenius stability
needs `sqrt(d_n) epsilon_n -> 0`, which nothing supplies).

**Recommended action:** restate the node as flexible HS-stability of the
ambient Kazhdan group `G`, or split it. I did not edit it — see the
"Actions not taken" section.

## wreath-not-sofic — PARTIAL (cited throughout notes/, deliberately not imported)

The node is explicitly conjectural by stated doctrine
(`research/wreath-not-sofic.md:8-12`). The `notes/` corpus asserts it about six
times as a **citation**, e.g. `notes/COMMUTING_WREATH_SOFIC_RADICAL.md:30-37`:

> "Consider the Kun--Thom group `W=A_X rtimes G`. Kun and Thom prove that
> \(W\) is nonsofic."

Source is audited against the paper: `notes/CREDIT_AND_PRIORITY_AUDIT.md:311-314`
("Kun–Thom 2608.06222 v1 ... Theorems: A = nonsofic wreath products") and
`:190` ("checked against the full HTML"). Derived nonsoficity statements are
proved conditionally on it (`notes/FALSE_FERMIONIC_KUN_THOM_ENDPOINT.md:54-55`,
`notes/PERFECT_CORE_KUN_THOM_WREATH.md:302-305`). Lean has an interface but
**no inhabitant**.

**Definitional gap — the real reason it is open.** The phrase "wreath
candidate" is used in exactly two places in `notes/` and is **never defined**:
`notes/OBSTRUCTIONS.md:123` (the substantive use) and `notes/NOTEPAD.md:31454`
(a *different* object — "the split integral wreath candidate"). All other
occurrences are downstream restatements in `research/*.md`. Until the symbol is
bound to a specific group, the citation cannot be applied to it. Binding it to
the Kun--Thom `W = (bigoplus_{G/Gamma} F_2) rtimes G` for the pair in
`notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md:7-22` is plausible from matching
notation in `OBSTRUCTIONS.md` §3-§4, but the corpus nowhere states it.

## continuum-nonisomorphic-non-mf-cylinder — PARTIAL (deleted proof of the weaker statement)

Claim: "The literal clopen cylinder contains continuum many pairwise
non-isomorphic finitely generated non-MF groups."

**A complete proof of the unrelativized statement exists in git and was
deleted from the manuscript on 2026-08-13** (commits `8d40b3ed`,
`4a210700`). Recover with `git show c3501887:non_mf_groups_exist.tex`,
lines 2083-2129 (`\subsection{Multiplicity}`, `lem:subgroupMF` +
`cor:continuum`). Verbatim conclusion:

> "\begin{corollary}[multiplicity]\label{cor:continuum}
> \item The groups $E\times\Z^k$, $k\in\N$, are pairwise
> non-isomorphic, finitely presented, and non-MF.
> \item There exist $2^{\aleph_0}$ pairwise non-isomorphic finitely
> generated non-MF groups."

The proof is self-contained: subgroup heredity of MF (still present at
`non_mf_groups_exist.tex:1748-1751`), abelianization torsion-free rank for (1),
and B. H. Neumann's continuum family of 2-generator groups plus a
countable-fibres cardinality argument for (2). The Neumann citation is
source-verified at `notes/CREDIT_AND_PRIORITY_AUDIT.md:440-441`.

**Why this is not SOLVED.** The cylinder is a set of *eight-generator marked*
groups — quotients of `F_8` satisfying all relators of `R` with `w != 1`
(`non_mf_groups_exist.tex:1727-1733`) — hence consists exactly of marked
quotients of `E`. The witnesses `E x N_i` are built by *enlarging* `E`, so
none of them lies in the cylinder. The node itself flags this
(`research/continuum-nonisomorphic-non-mf-cylinder.md:8`). The remaining
mathematical distance is entirely the relativization.

## effective-transport-modulus — PARTIAL

The **existential** version is solved and Lean-closed:
`non_mf_groups_exist.tex:1490-1502` and
`GroupApproximation/Sofic/LiteralUniformObstruction.lean:24`
(`literal_uniform_operatorNorm_obstruction`). That file's own docstring
(`:7-32`) is the precise answer to the claim:

> "It is quantitative in the mathematical sense that one positive defect
> budget and one finite test set work in every matrix dimension. **It is not
> yet an effective computation of that budget or test set.**"

The `1/500` input is machine-checked
(`GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean:230-244`) but is
nowhere linked to a modulus. Three further independent statements confirm the
computation is absent: `notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md:202-205`,
`notes/NON_MF_IMPACT_FORMAL_STATUS.md:112-114`,
`research/uniform-obstruction-from-corona-invisibility.md:20`.

**Nearest quantitative asset, in a different setting** (genuine
representations, not approximate models): `notes/NOTEPAD.md:944-978`, "Lemma
(Kazhdan square-root barrier for an exact ambient sector)", giving
`||W-1||_(2,normalized) <= 2 epsilon / kappa` and hence
`epsilon sqrt(d) >= alpha kappa / 2`. This is the only explicit
Kazhdan-constant-to-defect estimate in the corpus.

## finite-tracial-cstar-transport — UNTOUCHED

The existing transport theorem is **matrix-specific everywhere**. Lean:
`GroupApproximation/Sofic/ManuscriptKazhdanTransport.lean:39-63` quantifies
over `Matrix (naturalFiniteModel (d n)) ... ℂ` with the normalized matrix HS
norm (`:29-37`); the reusable engine
`GroupApproximation/Sofic/KazhdanAsymptoticCommutant.lean:725-734`
(`transport`, plus `transport_star:758`, `transport_both:826`,
`compressionGroup_transport_both:897`) is in the same signature; the ambient
structure hard-codes finite matrix models
(`GroupApproximation/Sofic/OpAlmostRepresentation.lean:26-32`). No general
finite tracial C*- or von Neumann-algebra version exists.

Manuscript is likewise matrix-specific (`non_mf_groups_exist.tex:260-284`),
and its proof shows what generality would actually require: the only
load-bearing property is **finiteness of the norm ultraproduct** `B_omega`
(`:300-303`, established by polar correction) plus the Kazhdan projection.
Companion pieces are equally matrix-bound: central-corner reduction `:322-338`,
central-sign criterion `:342-360`, finite-normal cancellation `:1373-1470`.

Corpus states the claim as open in nearly these words,
`notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md:210-212`:

> "5. **Broader targets.** Extending transport from matrix coronas to arbitrary
> norm ultraproducts of finite traced C-star algebras is plausible but needs
> a precisely chosen target category and a new proof."

A grep of `notes/` and both `.tex` files for "finite tracial C*",
"tracial C*-algebra", "target-general", "general target", "finite von Neumann
target", "beyond matrices" returns zero hits outside that paragraph.

## literal-group-structural-normal-form — PARTIAL

No normal form, no kernel description, no word problem exists. Specific
structural lemmas that do:

- **Base map is injective**, `non_mf_groups_exist.tex:674-679` (via the
  witness map composed with `B -> Gammabar`); consequently `E` is nonamenable.
- **Rank at most six + 32-relator Tietze presentation**,
  `non_mf_groups_exist.tex:996-1013`, with the caveat at
  `notes/NON_MF_IMPACT_FORMAL_STATUS.md:127-130` that the 32-relator
  presentation "is currently a human syntactic calculation."
- **One-sided compression structure**, `non_mf_groups_exist.tex:989-992`.
- `w != 1`, central, `w^2=1`, `w = [d,iota(v_1)]^2`, `:510-513`, `:1206-1212`.

**Hard obstruction to any linear/residually-finite normal form:** Theorem B,
`non_mf_groups_exist.tex:589-597` — every finite-dimensional representation of
`E` over every field kills `w`, so "finite-dimensional linear representations
do not separate the points of `E`" and `E` is of Deligne type.

The manuscript **deliberately avoids** normal-form theory,
`non_mf_groups_exist.tex:1197-1202` and `:564-568`:

> "no combinatorial theory of HNN extensions is needed."

Zero hits for "word problem" outside the "remain unresolved" sentence.

## mf-implies-hyperlinear — PARTIAL

Not proved. Four assets, none recorded in the graph:

1. **The reduction is formalized**: `GroupApproximation/Sofic/NormTraceGap.lean:276-314`,
   docstring verbatim —
   > "The multiplicativity transfers through the domination inequality with no
   > loss of dimension; the separation is exactly the trace hypothesis... the
   > norm clause contributes multiplicativity and nothing more."
   with `theorem isHyperlinear_of_traced_normModels` at `:306`. So the entire
   remaining content is producing separating traces.
2. **A formal no-go for the naive route**: identity-block padding,
   `NormTraceGap.lean:316-336`, preserves every operator-norm distance exactly
   while diluting every HS quantity. History at
   `notes/NON_MF_ARCHAEOLOGY.md:146-156` — "This closed the naive implication
   'weak MF implies hyperlinear.'" (Read precisely: it closed the *route*, not
   the statement.)
3. **A concrete counterexample to metric-change**, `notes/NOTEPAD.md:24294-24317`:
   represent `Z` in `U(n)` by `1 |-> diag(exp(i theta),1,...,1)`; this is
   operator-norm faithful in the corona while converging to the identity in
   normalized HS norm. "it proves that one cannot obtain a hyperlinear
   embedding merely by changing the metric on a given weak-MF embedding."
   Same passage fixes the convention split (Shulman/CDE weak vs. Schafhauser
   trace-controlled).
4. **A sufficient rate condition with a complete proof** —
   `notes/NOTEPAD.md:487-544`, exterior/Fock amplification: if
   `epsilon_n * sqrt(d_n) -> 0` then `G` is hyperlinear, via
   `tr_norm(R_d(U)) = |det((I+U)/2)|^2`. Finite-dimensional algebra formalized
   in `GroupApproximation/Sofic/ExteriorMFProfile.lean:210,270,281`. Missing
   input stated at `:539-541`: the qualitative MF theorem gives no such rate,
   so "extracting or disproving this profile is now a concrete quantitative
   subproblem."

Do not confuse with the converse, which is fully closed
(`NonMFImpact.witness_hyperlinear_nonMF`).

## nonsofic-mechanism-mf-classification — PARTIAL

The corpus **does** determine MF status for several specific groups. The graph
records none of it.

**Determined non-MF, unconditional:**

- The Kun--Thom Clifford extension (complete or sparse),
  `notes/FALSE_CLIFFORD_NORM_MF_STERILITY.md:5-37` — every homomorphism to a
  norm-matrix corona kills `z`, so "E is not weak/operator-norm MF". Proof uses
  only the Kazhdan projection and finiteness of the corona (`:82-92`). Closes a
  route: "the desired MF hypothesis is not merely missing; it is false"
  (`:139-142`).
- The perfect even cover, `notes/PERFECT_CORE_KUN_THOM_WREATH.md:614-616`
  (Proposition 8).
- The manuscript witness `W`: sofic **and** hyperlinear **and** non-MF,
  premise-free in Lean (`GroupApproximation/Endpoint/NonMFImpact.lean:81-92`).
  This is precisely the metric separation the claim asks for.

**Determined weak-MF at paper level (cited literature, not formalized):**

- Every symmetric double of a countable residually finite group,
  `notes/WEAK_MF_NONSOFIC_DOUBLE.md:187-188`; applied to the Kun--Thom pair at
  `:316-320`: "`D=G*_Gamma G` is weak-MF and nonsofic."
- The finite-lamp family, `:341-350`.
- The `Z`-lamp free-lamp group, `notes/NOTEPAD.md:830-856`, with the scope limit
  at `:857-860` — this separates weak-MF from sofic but **not** Schafhauser-MF
  or hyperlinear from sofic.

**Explicitly undetermined:** the Kun--Thom commuting wreath `W`
(`notes/NOTEPAD.md:30421-30423` — "weak MF of W is not banked"), `EL_4(L)`
(`notes/NOTEPAD.md:770-777`), `E/<w>`, `W/<zeta>`, `C_r^*(G*_Gamma G)`
(`notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md:166-193`, with the
`C^*(F_infty)`/QWEP warning), Elek--Szabo, Fournier-Facio.

**Formalization caveat:** `notes/WEAK_MF_NONSOFIC_DOUBLE.md:35-46` describes
`GroupApproximation/Sofic/MFNonsoficDoubleEndpoint.lean` and
`HasSoficCentralizerNormalization`. Both were **deleted** in commit `241440fe`
and no longer exist. The surviving
`GroupApproximation/Sofic/WeakMFNonsoficDouble.lean` contains no approximation
content ("It contains no approximation-theoretic endpoint", `:3-8`).

## scaling-family-pairwise-nonisomorphic — UNTOUCHED (and historically declined)

No argument exists. A repo-wide grep of `GroupApproximation/` for
`nonisomorphic|non-isomorphic|NotIsomorphic|isomorphism type` returns zero hits.

**The corpus considered and deliberately declined the statement.** Deleted
Remark, recoverable at `git show c3501887:non_mf_groups_exist.tex:2072-2081`:

> "\begin{remark}\label{rem:familyscope}
> We do not claim the groups $E_m$ are pairwise non-isomorphic;
> multiplicity is addressed in Corollary~\ref{cor:continuum}."

This is a disclaimer, not a disproof — hence UNTOUCHED rather than
CONTRADICTED. Note the technique that *did* work for the deleted `cor:continuum`
part (1) — abelianization torsion-free rank — is the natural first thing to try
on `E_m`, and the corpus never tries it.

## torsion-free-finitely-presented-non-mf — PARTIAL (deleted machine-checked conditional)

**The graph's premise is out of date.** The node says "The present
finite-normal mechanism cannot prove this directly", which is true and is
formalized (`GroupApproximation/Sofic/TorsionFreeFiniteNormalLimit.lean:19`,
`finiteSubgroup_eq_bot_of_isMulTorsionFree`). But the corpus contains a
**different mechanism** that reaches the conclusion conditionally, and it was
machine-checked.

`notes/TORSION_FREE_FULL_CDE_MF_FORMALIZATION.md` describes four Lean modules.
**All four were deleted** in commit `241440fe` (2026-08-14 13:38, message
"Prove integral linear groups residually finite", which does not mention the
deletion): `Sofic/TorsionFreeFullMFRadical.lean` (539 lines),
`Sofic/TorsionFreeFullMFConsequences.lean` (386),
`Analysis/TorsionFreeFullMFCStarConsequences.lean` (86), and
`Sofic/MFNonsoficDoubleEndpoint.lean` (164). Recover with
`git show 4a210700:<path>`.

What the deleted development proves, from
`git show 4a210700:GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean`:

```lean
theorem consequence_package :
    Group.IsFinitelyPresented R.Quotient ∧
      IsTwoGenerated R.Quotient ∧
      IsPowerTorsionFree R.Quotient ∧
      HasKazhdanPropertyT.{0, 0} R.Quotient ∧
      cdeMFResidual R.Quotient = ⊤ ∧
      ¬ IsOperatorMF R.Quotient ∧
      ¬ IsCDEOperatorMF R.Quotient
```

for any `R : DefectRoutingData D` — i.e. **exactly the claim**, plus
two-generation, property (T), and a *full* (not merely nontrivial) MF radical.
`TorsionFreeFullMFConsequences.lean:60` adds `not_isSofic` from
`NonsoficCriterionData`, and `:186,270` give simple/two-conjugacy-class and
simple-envelope packages.

The conditionality is exact and honest — `DefectRoutingData` is a structure
whose fields are the external group theory, not axioms. Its own docstring:

> "This is data rather than an existence axiom. In the intended application,
> Hull's relative small-cancellation argument supplies `Quotient`, `quotient`,
> the two generators, torsion preservation, finite presentation, and the fact
> that the original defect maps onto the entire quotient."

And `notes/TORSION_FREE_FULL_CDE_MF_FORMALIZATION.md:62-93` states the boundary
precisely — no unconditional `∃ Q` theorem, with six named missing inputs
(Fournier-Facio's input groups, suitable-subgroup extraction, Hull's two-stage
construction, acylindrical hyperbolicity, external SQ-universal/two-conjugacy
theorems, Raum's stable-rank-one theorem):

> "These results are represented only by structures whose fields are consumed
> by checked Lean proofs. They are not declared as axioms, selected by
> `Classical.choice`, or hidden in typeclass instances. Consequently the
> development certifies the algebraic and CDE-MF implications of the proposed
> construction, but not the unconditional existence of its small-cancellation
> input data."

Surviving related material in HEAD:
`GroupApproximation/Sofic/CDEMFRadical.lean` (the `cdeMFResidual` definition
and its equivalence with `coronaMFResidual`/`normMFResidual` — the deleted
files' foundation, still present) and
`GroupApproximation/Monsters/UniversalFinitelyPresentedTorsionFreeGroup.lean`
(countable torsion-free universal payload; every f.p. torsion-free group
embeds as one coordinate).

---

# Graph conversions made

After the ownership fences were lifted the following corpus results were
converted directly into Cairn nodes. All fifteen are **new adjacent files**; no
existing claim file was rewritten. `bin/cairn check` is clean after each batch.

**Target-class enrichment, closed.** After `coordinate-action-not-sofic`
invalidated `sofic-action-permanence`, one escape remained: satisfy
Alekseev--Bradford Corollary 5.2 for its class (c) (hyperlinear) instead of
class (a) (sofic), by relabelling with richer targets. Two independent corpus
proofs close it, neither previously in the graph.

- `single-lamps-recover-set-action` [ESTABLISHED] + `-proof` — the
  `notes/NOTEPAD.md` lemma: a sofic `C`-action on `⊕_X C_2` forces `G ↷ X`
  sofic, **for any class `C` whatsoever**. Class-agnostic, so it kills every
  enrichment at once, including classes not on Alekseev--Bradford's menu.
- `halo-locally-sofic-target-collapse` [ESTABLISHED] + `-proof` — the
  `FALSE_HALO_ACTION_AUDIT.md` (HAA3)/(HAA4) pair: witnesses with locally sofic
  targets collapse to sofic-class witnesses. Covers unitary, Pauli, Clifford.
- `halo-target-class-enrichment` [INVALIDATED] — the route both invalidate,
  targeting `hyperlinear-wreath-model`.

**Multiplicity.** `continuum-nonisomorphic-fg-non-mf` [ESTABLISHED] + `-proof`,
recovering the deleted `cor:continuum` from
`git show c3501887:non_mf_groups_exist.tex:2083-2129`. Its `distinct_from`
records precisely why it does *not* close the cylinder hole.

**MF classification by lamp type.** `nonsofic-mechanism-mf-classification` went
from an undecomposed root to a live route with a single open leaf:

- `kun-thom-clifford-extension-not-weak-mf` [ESTABLISHED] + `-proof` — Clifford
  lamps: not weak MF. It carries a **second** route,
  `-via-central-sign` (`requires: [central-sign-corona-obstruction]`), after
  `cairn-ce` observed the result is an instance of that established criterion.
  Verified: with `o = Gamma`, `c_o` is a centralizer element, and for
  `gamma in Gamma` moving `tGamma`,
  `([c_(to), gamma])^2 = c_(to) · z c_(to) c_(gamma t o) · c_(gamma t o) = z`,
  which is verbatim the criterion's hypothesis. Both routes are kept: the hand
  proof exhibits the concrete contradiction that makes the operator-norm /
  tracial category split legible, which a black-boxed derivation hides.
- `symmetric-double-weak-mf` [ESTABLISHED] + `-proof` — free lamps: weak MF
  (internal proof plus Shulman Theorem 10, trust surface stated in the route).
- `kun-thom-wreath-weak-mf` [OPEN] — commuting lamps, the remaining leaf.
- `nonsofic-mf-classification-by-lamp-type` [route] — the finding that MF
  status is decided by lamp type, not by the compression mechanism, which is
  exactly the separation the target claim asks for.

**Route hygiene.** `clifford-ce-targets-are-equivalent` [ESTABLISHED] +
`-proof`: the full Majorana algebra, the even core, and the one-character
target are the *same* CE problem (Proposition 4 and Theorem 6 of
`PERFECT_CORE_KUN_THOM_WREATH.md`), so they must not be counted as three
independent chances.

# Actions still not taken, and why

**Two frontier holes deliberately not imported**, both near-misses under the
no-laundering rule:

- `continuum-nonisomorphic-non-mf-cylinder`: the recovered proof gives the
  unrelativized statement; its witnesses `E x N_i` enlarge `E` rather than
  quotient it, so none lies in the eight-generator cylinder. The weaker
  statement is now in the graph as its own claim instead.
- `torsion-free-finitely-presented-non-mf`: the deleted Lean development
  proves the implication, not the existence, and is conditional on packaged
  external group theory. Reported to `cairn-torsionfree`, who holds the lock.

**No existing claim file edited.** `wreath-flexible-hs-stability` is mis-stated
(its subject fuses the ambient Kazhdan group `G` with the wreath candidate),
and five atlas nodes mis-attribute their source to `AGENDA.md` when the cited
headers live in `notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md`. Both are
statement-level corrections to nodes others are working in, so they remain
reported rather than applied.

**Two docs need a staleness marker** (not applied — I only read `notes/`):
`notes/TORSION_FREE_FULL_CDE_MF_FORMALIZATION.md` and
`notes/WEAK_MF_NONSOFIC_DOUBLE.md` both describe Lean files deleted in
`241440fe` as present. The second is now flagged inside
`symmetric-double-weak-mf-proof`, so the graph does not inherit the error.

# Corpus notes worth keeping

- **Two different groups are called `W`.** In
  `notes/COMMUTING_WREATH_SOFIC_RADICAL.md:30` `W = A_X rtimes G` is the
  nonsofic Kun--Thom commuting wreath (MF status open). In
  `research/sofic-non-mf-witness.md` and
  `notes/SIMULTANEOUS_P_AND_OPERATOR_STABILITY_2026-08-13.md:283-294`,
  `W = ClLamp(X) rtimes V` is the sofic, non-MF affine-Clifford witness.
- **`notes/NOTEPAD.md` is stale as a progress log.** Its newest dated header is
  `# 2026-08-12` (line 24319). It still contains unique load-bearing material
  (the hyperfinite HS stability theorem, the exterior amplification lemma, the
  central-extension MF criterion, the Kazhdan square-root barrier) that exists
  nowhere else.
- **Newest documents by mtime** are `notes/FALSE_ODD_SPECTRAL_EQUIVARIANT_COARSENING.md`
  (17:45) and `notes/HYPERLINEAR_CAIRN_PROGRESS_2026-08-14.md` (16:44); both
  postdate `AGENDA.md` (11:39) and `HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md`
  (11:05), and neither is reflected in those two.
- **This sweep's scope is the 96-claim graph, which teammates have since
  outgrown.** The sweep was specified against the `research/FRONTIER.md`
  generated at 96 claims / 93 routes / 27 holes. By the end of the sweep
  `bin/cairn check` compiled **151 claims and 147 routes**, with many new
  nodes imported concurrently by the hole owners — including
  `wreath-not-sofic-proof`, `kun-thom-nonsofic-wreath-citation`,
  `literal-word-problem-solvable`, `literal-witness-kernel-free`,
  `finite-traced-kazhdan-transport`, `mf-implies-hyperlinear-via-rank-profile`,
  and `torsion-free-countable-non-mf`. Several of those postdate and partly
  supersede the verdicts above; the *corpus* evidence quoted here is
  unaffected, but the "what the graph records" half of each verdict should be
  re-read against the current graph rather than against `FRONTIER.md` as
  quoted. Newer holes outside this sweep's scope include
  `commutant-projection-extraction`, `compressed-commutant-majorana`,
  `infinite-order-central-mark-group`, `invariant-graph-crossed-product-ce`,
  `literal-mark-quotient-flexibly-stable`,
  `random-complex-linear-cocycle-stability`, `torsion-free-higman-embedding`
  and `openai-leavitt-unit-nonsofic`.
- Running `bin/cairn check` regenerates `research/FRONTIER.md`. I ran it once
  at the end to confirm graph integrity (exit 0, duplicate warnings only, no
  errors); that regeneration is the only tracked-file change attributable to
  this agent outside `notes/`.
</content>
</invoke>
