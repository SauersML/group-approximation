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

### THE ONE OPEN OBLIGATION

    def CountableAbelianMF : Prop :=
      ∀ (A : Type) [CommGroup A] [Countable A], IsOperatorMF A

Provable, not a literature input.  rank-four confirmed they have not started it
and handed it over.  The route, so it need not be re-derived:

1. `isOperatorMF_of_isLEF` (Algebra/AmenableMFProof) reduces it to LEF.
2. `isLEF_of_forall_finset_residuallyFinite` (Sofic/LEFSofic) reduces LEF to:
   every finite subset lies in a residually finite subgroup.  Take
   `Subgroup.closure ↑s`, which is finitely generated abelian.
3. So the whole content is: **a finitely generated abelian group is residually
   finite**, which is NOT in Mathlib at the pin.  Mathlib has only
   `Finite ⇒ ResiduallyFinite`, `ResiduallyFinite` for subgroups, for binary
   products, and `residuallyFinite_of_forall_exists_finite_monoidHom`.
4. It has to go through the structure theorem
   `AddCommGroup.equiv_free_prod_directSum_zmod` (Mathlib
   `GroupTheory/FiniteAbelian/Basic.lean`): transport along the additive
   equivalence, note the torsion factor is finite hence residually finite, and
   get the free factor `Fin n →₀ ℤ` by induction on `n` from residual
   finiteness of `ℤ` (via `ZMod (|g|+1)`) and the binary product instance.
   Additive-to-multiplicative transport goes through `Multiplicative` and the
   repository's `residuallyFinite_of_mulEquiv`.

Estimated at 120--200 lines with several Mathlib names to pin down
(`DirectSum` finiteness over a `Fintype`, `Finsupp.equivFunOnFinite`, the
additive form of the transport).  Isolated as a hypothesis so that nothing else
waits on it.
