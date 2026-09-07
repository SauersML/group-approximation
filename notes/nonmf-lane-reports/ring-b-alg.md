# Lane `ring-b-alg`

## Task 1 — the algebraic core of `thm:full-defect-ring`

Task: the compressor, the centralizer element, the printed defect and its
normal generation, over an arbitrary unital ring, at rank 4 and at every rank
`n ≥ 4`.  Printed source: `non_mf_groups_exist.tex`, section
`sec:one-sided-inverses`.

## Landed on origin/main

| commit | module | jobs |
|---|---|---|
| `d07ca27a69543d05cc1f448422c789ab3c1bef40` | `GroupApproximation/Leavitt/OneSidedInverse.lean` | 1227 |
| `c6c5fdbcb6f91ce77588672959a2fae760843b78` | `GroupApproximation/Leavitt/OneSidedCompressor.lean` | 2093 |
| `1ead28fc06db6c8eb40d46017a44881fc1eb9582` | `GroupApproximation/Leavitt/OneSidedCompressorDefect.lean` | 4056 |
| `6175d1cc29bbb90f9bc3711ed3f020df2386a0a8` | `GroupApproximation/Leavitt/FullIdempotentNormalGeneration.lean` | 4060 |
| `5563234074de9d9a0d06d3317aaab7d92681ea5b` | `GroupApproximation/Leavitt/OneSidedCompressorStabilized.lean` | 4062 |
| `3f69392c93f894d012ea05f5f2a2ab544d241ba0` | `GroupApproximation/Leavitt/FullDefectRingAtFixedRing.lean` | 4263 |
| `a94570768398f483b37c568d7102cdc62096a56d` | `GroupApproximation/Leavitt/OneSidedCompressorStrict.lean` | 4277 |

### `OneSidedInverse.lean` — namespace `GroupApproximation.OneSidedCompressor`

`structure OneSidedInverse R` with fields `s`, `t`, `t_mul_s : t * s = 1`;
`OneSidedInverse.e := 1 - s * t` with `e_eq`, `e_add_st`, `s_mul_t`,
`e_mul_s`, `t_mul_e`, `e_mul_e`, `t_pow_mul_e`, `e_mul_s_pow`; the telescoping
identities `s_sq_mul_t_sq`, `s_cube_mul_t_cube` and their consequence
`sum_four : e + set + s²et² + s³t³ = 1`.  Leavitt bridge: `ofLeavittFamily`
and `e_ofLeavittFamily : (ofLeavittFamily L).e = L.p1`.

### `OneSidedCompressor.lean` — same namespace

0-indexed `Fin 4`: `coreIdx : Fin 3 → Fin 4` is `Fin.castSucc`, `lastIdx = 3`.

* `core R : Subgroup (elementaryGroup (Fin 4) R)`, the printed `L = EL₃(R)`.
* `coreEmbedding`, `coreEmbedding_range : range = core R`,
  `coreEmbeddingToCore`, `coreEmbeddingToCore_surjective`,
  `core_hasKazhdanPropertyT`.
* `compressorPiece P i` and `compressorPiece_val` — the printed
  `uᵢ = e₄ᵢ(t-1)eᵢ₄(1)e₄ᵢ(s-1)eᵢ₄(-t)` and its block `(s e; 0 t)`.
* `compressor P`, `compressor_val`, `compressor_inv_val` — the two printed
  displays; `compressorMatrix_mul_inv`, `compressorInvMatrix_mul`.
* `compressor_conj_root : u eᵢⱼ(a) u⁻¹ = eᵢⱼ(s a t)` and
  `compressor_compresses_core`, the printed `uLu⁻¹ ≤ L`.

### `OneSidedCompressorDefect.lean` — same namespace

* `centralMark P` (the printed `c`), `centralMark_eq_commutator`,
  `centralMark_val : c = diag(1,1,1,1+et)`, `centralMark_commute_core`.
* `compressor_conj_centralMark : u c u⁻¹ = e₀₁(e)`.
* `printedEll R = e₁₂(1)`, `printedDefectRoot P = e₀₂(e)`,
  `defect_eq : ⁅u c u⁻¹, ℓ⁆ = d`.
* `compressor_mem_compressionSet`, and the milestone
  `printedDefectRoot_mem_printedDefect :
   printedDefectRoot P ∈ Manuscript.OneSidedMFRadical.printedDefect (core R)`.

### `FullIdempotentNormalGeneration.lean` — namespace `GroupApproximation.FullIdempotent`

`exists_two_further_indices`, `commutator_mem_of_right`,
`commutator_mem_of_left`, `elementaryRoot_sum_mem`, and the theorem

    elementaryGroup_normal_eq_top_of_full
      (hcard : 4 ≤ Fintype.card ι) (N : Subgroup (elementaryGroup ι R)) [N.Normal]
      {i j : ι} (hij : i ≠ j) {x : R}
      (hmem : elementaryRoot i j hij x ∈ N)
      (hfull : ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * x * b k = 1) : N = ⊤

with `normalClosure_elementaryRoot_eq_top_of_full` and the rank-four corollary
`printedDefect_eq_top`.

### `OneSidedCompressorStabilized.lean` — namespace `GroupApproximation.OneSidedCompressor`

`blockIndexEquiv`, `bigIdx`, `bigIdx_injective`, `blockEmbedding`,
`blockEmbedding_elementaryRoot`, `blockEmbedding_injective`; the printed data
at rank `n` as `coreOf`, `compressorOf`, `centralMarkOf`, `printedEllOf`,
`printedDefectRootOf`; the transported identities
`elementaryRoot_mem_coreOf`, `compressorOf_compresses_coreOf`,
`compressorOf_mem_compressionSet`, `centralMarkOf_commute_coreOf`,
`printedEllOf_mem_coreOf`, `defectOf_eq`,
`printedDefectRootOf_mem_printedDefect`; the saturation
`printedDefectOf_eq_top`; the property-`(T)` transport `coreEmbeddingOf`,
`coreEmbeddingOf_range`, `coreEmbeddingOfToCore`,
`coreEmbeddingOfToCore_surjective`, `coreOf_hasKazhdanPropertyT`; and the
closed endpoint `PrintedFullDefectSaturation` proved by
`manuscriptPrintedFullDefectSaturation`, whose `#audit_closed_axioms` report
is `[propext, Classical.choice, Quot.sound]`.

### `FullDefectRingAtFixedRing.lean` — namespace `GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing`

`theorem fullDefectAtFixedRing : FullDefectAtFixedRing`, the seam requested by
lane `ring-b-end`.  Its proof joins `printedDefectOf_eq_top`,
`coreOf_hasKazhdanPropertyT` and `FullDefectRing.countable_elementaryGroup`
into the hypotheses of `FullDefectRing.manuscriptSaturatedPrintedDefectRadical`
and takes its third clause.  `#audit_closed_axioms` reports
`[propext, Classical.choice, Quot.sound]`.

### `OneSidedCompressorStrict.lean` — namespaces `GroupApproximation.OneSidedCompressorStrict` and `…FullDefectRing`

`theorem oneSidedCompressorStrictContainment : OneSidedCompressorStrictContainment`,
the compressor half of the first sentence of `cor:one-sided-ring-maximal`.
That sentence is *not* a consequence of `thm:full-defect-ring`: it uses no
ideal condition on `1 - st` and no saturation of the printed defect.

`Γ` is the copy of `EL₃(S)` on the core coordinates of `Fin n`, for `S` the
subring generated by `s` and `t`; `u` is the printed compressor.  Containment
is `u e_{ij}(a) u⁻¹ = e_{ij}(sat)`, which stays inside `S`.  Strictness is a
**left probe**: the units fixing `x E_{II}` under left multiplication form a
subgroup `probeStabilizerUnits x I`; a root off row `I` is in it for free and
`e_{IJ}(a)` on row `I` is in it exactly when `x a = 0`.  With `x = e` on the
middle core row, every `e_{IJ}(sat)` is in it because `es = 0` and `e_{IJ}(1)`
is not, because `e ≠ 0`.  A subgroup is needed rather than an entrywise
argument so that the closure induction goes through.

Supporting: `probeStabilizer`, `mem_probeStabilizer_iff`,
`elementaryRoot_mem_probeStabilizer`,
`elementaryRoot_mem_probeStabilizer_of_row_ne`,
`elementaryRoot_mem_probeStabilizer_of_mul_eq_zero`,
`elementaryRoot_one_not_mem_probeStabilizer`,
`elementaryGroupMap_elementaryRoot`, `coreEmbeddingOf_elementaryRoot`,
`compressorOf_conj_root`, `subringCoreEmbedding`,
`subringCoreEmbedding_elementaryRoot`, `subringCompressor`,
`subringCompressor_conj_root`, `conj_subringCoreEmbedding_mem`.

## Interfaces for other lanes

The fullness hypothesis is stated exactly as lane `ring-b-end` produces it in
`Manuscript/OneSidedMFRadical/FullDefectRingFullIdeal.lean`:

    ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * x * b k = 1

with `x = P.e`, and `P.e` is definitionally `1 - P.s * P.t`.

## Open obligations

None.  Every deliverable of the brief is landed, and both named Props that
lane `ring-b-end` was waiting on are discharged: `FullDefectAtFixedRing` and
`OneSidedCompressorStrictContainment`.
The two hypotheses that remain inside `FullDefectAtFixedRing` itself are the
printed ones and are supplied elsewhere: fullness of `e` by `ring-b-end`
(`FullDefectRing.exists_sum_eq_one_of_isSimpleRing`, `leavittFamily_full`,
`completeMatrixFamily_full`) and property `(T)` for `EL₃(R)` and `EL_n(R)` by
`ejz-integral`.


## Task 2 — `prop:locally-rf-by-z-trace`, amenable extensions

Assigned after task 1, when the tex owner generalized the proposition
(`e51f655d2`) to: for every extension `1 → N → G → A → 1` of countable groups
with `N` locally residually finite and `A` amenable, the canonical trace of
`C*_max(N)` is quasidiagonal and the canonical trace of `C*_max(G)` is
amenable.  Namespace for everything new: `GroupApproximation.AmenableExtensionTrace`.

| commit | module | jobs |
|---|---|---|
| `88ba267526f1b2ca896fe61dbb53fcbf4889a5a5` | `GroupApproximation/Analysis/QuasidiagonalTraceGeneratorDense.lean` | 3184 |
| `d4e4c824a95725de53b17fe67790699f468dede1` | `GroupApproximation/Analysis/LocallyRFQuasidiagonalTrace.lean` | 3197 |
| `cb11520d8944b0a7cdd0615559bc2f89e8b43f24` | `GroupApproximation/Analysis/AmenableExtensionWindow.lean` | 3313 |
| `2a7488abaf306fe8ba322a4027dac2425850c9a1` | `GroupApproximation/Analysis/AmenableExtensionAmenableTrace.lean` (+ window fix) | 3314 |
| `17a2fc794862853a83f3895dfdade0b34ea22a29` | `GroupApproximation/Analysis/AmenableExtensionIntCorollary.lean` | 3315 |

### The closed endpoints

* `PrintedLocallyRFCanonicalTraceQuasidiagonal` /
  `manuscriptPrintedLocallyRFCanonicalTraceQuasidiagonal` — clause (i).
* `PrintedAmenableExtensionCanonicalTraceAmenable` /
  `manuscriptPrintedAmenableExtensionCanonicalTraceAmenable` — clause (ii).
* `PrintedAmenableExtensionTrace` / `manuscriptPrintedAmenableExtensionTrace`
  — the printed proposition, both clauses.

All three carry `#audit_closed_axioms` with the classical closure.

### Three things worth knowing

* Clause (i) needs asymptotic multiplicativity in **operator** norm, and the
  corpus only had the Hilbert--Schmidt propagation.  The missing propagation is
  `AmenableExtensionTrace.tendsto_mul_op_of_dense_generators`, landed first; it
  reuses the existing bilinear defect lemmas and
  `Quasidiagonal.norm_denseGeneratorDefect_sub_le`, which was already stated in
  operator norm.
* Clause (i) is *exact* twice over: once the right-hand generator is tested
  nothing escapes the selected window, and a tested nonidentity element fixes
  no selected coset because the packet kernel is normal in the stage subgroup.
  No Følner set appears in clause (i) at all.
* `extModel` must **not** be `@[reducible]`.  Reducibility makes instance search
  unfold it to the underlying product and then fail to find `DecidableEq`,
  because the Følner factor lives in a quotient group with no decidable
  equality.  With the model opaque, the `FiniteModel` instances apply and the
  classical equality packaged in the model is the one used.

### Reused rather than rebuilt

The printed section `σ` and cocycle `b(g,x)` are
`SoficByAmenablePermanence.sect` and `esCocycleN`; the Følner set is
`AmenableActionSofic.exists_folner` at tolerance `1/(n+1)`; the residual packet
and finite quotient are `ResidualFinitePacket.Packet` and
`LocallyRFByIntAmenableTrace.exists_packet_of_fg`; the compression and its
escape estimate are `QuasiRegularCompression`.  No existing module was edited.

### Open obligations

None.


## Task 3 — `thm:mf-quotient-units`, MF quotients of unit groups

Namespace for everything new: `GroupApproximation.MFQuotientUnits`.

| commit | module | jobs |
|---|---|---|
| `2e991ef50eb121433c3fa42093205485fc57e22a` | `GroupApproximation/Algebra/PurelyInfiniteSimpleRing.lean` | 968 |
| `4ad72a2780398b46331a74d9fd90f119c55b2a44` | `GroupApproximation/Manuscript/OneSidedMFRadical/MFHomKernel.lean` | 4280 |
| `b4c2533508b665e1ff026a76e041552e284c9e9f` | `GroupApproximation/Algebra/CornerRing.lean` | 975 |
| `6a9aaf05fcd2b441b3ab83e56efd6b1f28702d1e` | `GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnits.lean` | 4282 |
| `e4e2f12d85191ddaa0f951529776e4fe4af9d8f3` | `GroupApproximation/Algebra/FinitelyGeneratedAbelianResiduallyFinite.lean` (+ endpoint discharge) | 2810 / 4283 |

The printed theorem is `PrintedMFQuotientUnits`, proved by
`printedMFQuotientUnits_of_inputs` from five named hypotheses:
`AGPMatrixReduction`, `AGPUnitK1`, `AGPMenalMoncasiReduction`, `AGPStepOne`,
`CountableAbelianMF`.  `eq:corner-units` is
`cornerUnitSubgroup_le_mfHomKernel`, which is where
`thm:full-defect-ring` enters, through its rank-two form.

### Two places this is weaker than the print, both recorded in docstrings

* The quotient is "some countable abelian MF group" rather than `K_1(R)` on the
  nose.  Naming it needs the colimit `lim GL_n/EL_n`, which is not built and is
  used nowhere else in the printed proof.  The rank reduction needs no Morita
  step: `M_n(R)` is again purely infinite simple and its unit group *is*
  `GL_n(R)`, so the `n = 1` argument applies to it directly.
* `IsPurelyInfiniteSimpleUnitalRing` (PartialClosureAnalysis) names the same
  class of rings by a different, equivalent definition.  Neither predicate is
  stated in terms of the other and no bridge is assumed, because the printed
  proof needs none.

### The countable-abelian clause, closed

`CountableAbelianMF` is no longer a hypothesis: `countableAbelianMF` proves it,
and `printedMFQuotientUnits_of_agp` is the endpoint depending only on
`thm:full-defect-ring` in its rank-two form and the four Ara--Goodearl--Pardo
propositions.

The print argues analytically (`C*_max(A)` commutative and separable, hence
residually finite-dimensional and MF, citing Brown--Kirchberg).  The proof used
instead is group-theoretic and quotes nothing: countable abelian implies LEF
implies MF.  Mathlib has residual finiteness for finite groups, subgroups and
binary products but not for finitely generated abelian groups, and the
structure theorem is additive while the target is multiplicative, so everything
runs on the class-free predicate `AddSeparated` and converts once at the end.
The free part needs no induction: a nonzero element of `Fin n →₀ ℤ` is nonzero
in some coordinate, separated in `ℤ` by reduction modulo `|g i| + 1`.

### Open obligations

None.

### One landed module that nothing imports

`Algebra/CornerRing.lean` (`b4c2533508b665e1ff026a76e041552e284c9e9f`) was
built on an explicit instruction, and a later instruction --- which crossed with
the build --- said it was not needed after all, because
`range_le_mfHomKernel` is the whole content of `eq:corner-units` and the corner
never has to be constructed.  The module is correct and self-contained, its
import has been removed from `MFQuotientUnits.lean`, and nothing else in the
tree uses it.  It is reusable infrastructure (the plain algebraic corner `eRe`
as a `Ring` with unit `e`, which the tree otherwise has only for C⋆-algebras at
a projection), so it is left in place rather than deleted; that is the lead's
call, not this lane's.


## Task 4 — sentence carriers for the two printed proofs

| commit | module | jobs |
|---|---|---|
| `1fe5908303fb4efc742f664f674de6edf7f696e6` | `GroupApproximation/Analysis/AmenableExtensionSentences.lean` | 3315 |
| `6625282d2f13d0d6b060f79614c64898b1a4735e` | `GroupApproximation/Manuscript/OneSidedMFRadical/MFQuotientUnitsSentences.lean` | 4284 |

Pattern followed: `Manuscript/OneSidedMFRadical/NormalKazhdanPrintedRoute.lean`
— one `manuscriptSentence_*` per printed sentence, the sentence quoted verbatim
in its docstring, proved from already-landed pieces.  No new mathematics.

### `prop:locally-rf-by-z-trace` (proof) → `Analysis/AmenableExtensionSentences.lean`

All unconditional.  Namespace `GroupApproximation.AmenableExtensionSentences`.

| printed sentence | carrier |
| --- | --- |
| 1. "let `E ⊆ N` be finite, put `N₀ = ⟨E⟩`, and choose a finite quotient `θ`… put `H = ker θ`" | `manuscriptSentence_stagePacketSeparates` |
| 2. "the finite-dimensional subspace `ℓ²(N₀/H)` is `N₀`-invariant, and compression to it is a u.c.p. map `φ_E`… that restricts to a representation of `C*_max(N₀)`" | `manuscriptSentence_stageCompressionUCP` |
| 3. "`x` fixes no coset `nH`… by normality of `H` in `N₀`; so `tr(φ_E(u_x)) = 0`" | `manuscriptSentence_stageTraceZero` |
| 4. "Along an exhaustion… density of the group algebra and contractivity extend both limits" | `manuscriptSentence_stageLimitsExtend` |
| 5. "fix a finite set `E`, a finite Følner set `F`, and a section `σ`… put `b(g,x) = σ(ḡx)⁻¹gσ(x) ∈ N`" | `manuscriptSentence_cocycleValues` |
| 6. "The subgroup `N₀`… is residually finite; choose a finite quotient `θ`… representatives `r_q`" | `manuscriptSentence_cocyclePacketSeparates` |
| 7. "The cosets `σ(x)r_qH`… are pairwise distinct… let `T` be their set… put `Φ(b) = Pλ(b)P`" | `manuscriptSentence_cosetsDistinct` |
| 8. "This map is u.c.p., and for `g ∈ E` and `ḡx ∈ F`, `gσ(x)r_qH = σ(ḡx)r_{θ(b(g,x))q}H ∈ T`" | `manuscriptSentence_compressionUCPAndTranslation` |
| 9. "the rank of `(1-P)λ(h)P`, at most `\|{x ∈ F : h̄x ∉ F}\|·\|Q\|`, give `‖·‖₂² ≤ …`" | `manuscriptSentence_rankBoundGivesHS` |
| 10. "The normalized trace of `Φ(u_g)` is the fraction of points of `T` fixed by `g`… it is zero" | `manuscriptSentence_traceIsFixedPointFraction` |
| 11. "Taking Følner sets with… → 0… density and contractivity extend both limits" | `manuscriptSentence_folnerLimitsExtend` |

Sentence 10's printed case split (`ḡ ≠ 1` versus `ḡ = 1`) is not reproduced:
`ext_no_fixed_coset` shows a fixed coset forces `w⁻¹g⁻¹w ∈ H ≤ N`, and reading
that in `G/N` already gives `ḡ = 1`, so the first printed case cannot occur.
The carrier has the sentence's conclusion, not its case structure.

### `thm:mf-quotient-units` (proof) → `Manuscript/OneSidedMFRadical/MFQuotientUnitsSentences.lean`

Namespace `GroupApproximation.MFQuotientUnitsSentences`.

| printed sentence | carrier | conditional on |
| --- | --- | --- |
| 1. "`M_n(R)` is again countable, purely infinite, and simple… so it suffices to treat `n = 1`" | `manuscriptSentence_matrixRingAgainPurelyInfinite` | `AGPMatrixReduction` |
| 2. "`κ` is surjective with kernel `[H,H]`" | `manuscriptSentence_kappaSurjectiveKernelCommutator` | `AGPUnitK1` |
| 3. "A countable abelian group `A` is MF" | `manuscriptSentence_countableAbelianIsMF` | — |
| 4. "So `κ` is a homomorphism to an MF group, and `N ≤ ker κ`" | `manuscriptSentence_radicalLeKerKappa` | — |
| 5. "every homomorphism from `EL_m(eRe)`, `m ≥ 2`, to an MF group is trivial" | `manuscriptSentence_cornerElementaryKillsMFTargets` | `thm:full-defect-ring`, rank-two form |
| 6. `eq:corner-units` | `manuscriptSentence_cornerUnitsLieInRadical` | — |
| 7. "`u = PvQ`… `v = e_1 + (1-e_1)v(1-e_1)`" | `manuscriptSentence_menalMoncasiReduction` | `AGPMenalMoncasiReduction` |
| 8. "…products of an element of `EL_{m-1}(T)` and a conjugate of its inverse, so they lie in the normal subgroup `N`" | `manuscriptSentence_normalAbsorbsConjugateOfInverse` (reason only) | — |
| 9. "Hence `u ≡ v` modulo `N`, and `κ(v) = κ(u) = 0`" | `manuscriptSentence_kappaVEqOne` | — |
| 10. "…`v = 1 - P + θ(diag(v,1,…,1)) ∈ N`… Hence `ker κ ≤ N`" | `manuscriptSentence_stepOneGivesKerKappaLeRadical`, `manuscriptSentence_conclusion` | `AGPStepOne` (body only) |

Two clauses have no carrier, by design and stated in the docstrings: the Morita
half of sentence 1 (the conclusion never names `K_1(R)`, so nothing has to
identify `K_1(M_n R)` with it), and the identification in sentence 8 of the two
Steinberg displays with elements of `EL_{m-1}(T)`, which is internal to
`AGPMenalMoncasiReduction`.

### A stale census row

The census work order lists `thm:mf-quotient-units` (23 sentences) as
"**no Lean carrier at all** — genuinely open formalization… The largest real
gap found this round."  That was true when written and is not now: the
statement landed at `6a9aaf05f`, the countable-abelian input at `e4e2f12d8`,
and the sentence carriers above.  What remains quoted is four
Ara--Goodearl--Pardo propositions, each a named Prop with provenance, not an
open formalization.  `cor:leavitt-mf-quotient` is rank-four's and is unblocked
by this.


## Task 5 — sentence carriers for `thm:factorization-nonmf-trace`

`e60d09eb21f7062d6c8b35fd5dbffe95c5dafdec` —
`GroupApproximation/Manuscript/OneSidedMFRadical/FactorizationTraceSentences.lean`,
3942 jobs, namespace `GroupApproximation.FactorizationTraceSentences`, six
carriers each with `#audit_axioms` reporting the classical closure.

| printed sentence | carrier | status |
| --- | --- | --- |
| 1. "Suppose that `τ_G` is quasidiagonal, and let `φ_n` be u.c.p. maps as in the definition, with the first limit in operator norm." | `manuscriptSentence_quasidiagonalModel` | unconditional |
| 2a. "`φ_n(u_g)^*φ_n(u_g)` and `φ_n(u_g)φ_n(u_g)^*` converge to `1` in operator norm" | `manuscriptSentence_nearIsometry` | partial — star-free form, see below |
| 2b. "so for large `n` the unitary part `V_n(g)` of the polar decomposition of `φ_n(u_g)` satisfies `‖V_n(g) − φ_n(u_g)‖ → 0`" | none | **route-different** |
| 2c. "and `V_n(1) = 1` because `φ_n` is unital" | `manuscriptSentence_unitalAtIdentity` | unconditional (unitality clause only) |
| 3. "The maps `V_n : G → U(d_n)` are asymptotically multiplicative in operator norm." | none | **route-different** |
| 4a. "If `g ≠ 1` and `‖V_n(g) − 1‖ → 0`, then `tr_{d_n}(φ_n(u_g)) → 1`" | none | **route-different** |
| 4b. "contradicting `tr_{d_n}(φ_n(u_g)) → τ_G(u_g) = 0`" | `manuscriptSentence_traceTendsToZero` | unconditional |
| 5a. "So `limsup_n ‖V_n(g) − 1‖ > 0` for every `g ≠ 1`" | none | **route-different** |
| 5b. "and `G` is MF, contrary to the hypothesis." | `manuscriptSentence_quasidiagonalGivesMF` | unconditional |
| 6. "The last assertion follows." | `manuscriptSentence_lastAssertion` | unconditional |

### Why the four `V_n` clauses have no carrier

The printed proof is constructive in the unitaries: polar-decompose `φ_n(u_g)`,
keep the unitary part.  The tree proves the same theorem without ever forming
`V_n` — `Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` then
`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal`, which restricts the
maps to the canonical group unitaries and reads off one late index.  The two
routes rejoin only at sentence 5b.

Constructing `V_n` would mean constructing the polar decomposition first, and
the tree already records that it is unavailable: `Analysis/CalkinSchauder.lean`
states that "Mathlib has no polar decomposition of a bounded operator; neither
`polarDecomposition` nor `polar_decomposition` occurs in the library".  So this
is a **route difference**, not a formalization gap: the theorem is closed, and
what is missing is a second proof of it along the printed lines.

### The substitution in sentence 2a

The printed adjoint is of the matrix `φ_n(u_g)`.  Identifying it with
`φ_n(u_{g⁻¹})` needs `φ_n` to be `⋆`-preserving, which
`Quasidiagonal.QuasidiagonalTraceModel` does not assert: its
complete-positivity field is a form-positivity condition, and
`Analysis/QuasidiagonalTrace.lean`'s own docstring says nothing in that file
consumes it.  The carrier therefore proves the star-free
`φ_n(u_{g⁻¹})φ_n(u_g) → 1` and `φ_n(u_g)φ_n(u_{g⁻¹}) → 1`, which is what the
model gives and what the printed sentence means.
