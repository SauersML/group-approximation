# Lane `ring-b-alg` — the algebraic core of `thm:full-defect-ring`

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

## Interfaces for other lanes

The fullness hypothesis is stated exactly as lane `ring-b-end` produces it in
`Manuscript/OneSidedMFRadical/FullDefectRingFullIdeal.lean`:

    ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * x * b k = 1

with `x = P.e`, and `P.e` is definitionally `1 - P.s * P.t`.

## Open obligations

None.  Every deliverable of the brief is landed, and the seam
`FullDefectAtFixedRing` that lane `ring-b-end` was waiting on is discharged.
The two hypotheses that remain inside `FullDefectAtFixedRing` itself are the
printed ones and are supplied elsewhere: fullness of `e` by `ring-b-end`
(`FullDefectRing.exists_sum_eq_one_of_isSimpleRing`, `leavittFamily_full`,
`completeMatrixFamily_full`) and property `(T)` for `EL₃(R)` and `EL_n(R)` by
`ejz-integral`.
