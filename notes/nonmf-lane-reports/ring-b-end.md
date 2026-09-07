# Lane `ring-b-end` — the endpoint of Theorem 2 and its two corollaries

Scope: `thm:full-defect-ring`, `cor:simple-infinite-ring`,
`cor:one-sided-ring-maximal` of `non_mf_groups_exist.tex`.
Sub-namespace: `GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing`.

## Landed

| commit | jobs | modules, all under `Manuscript/OneSidedMFRadical/` |
|---|---|---|
| `8c21918e938f952350c45afa440040cefb700935` | 4070 | `FullDefectRingCore.lean` |
| `bc49957918c4f4cb5d768d190c65a4d59ef7d92c` | 3444 | `FullDefectRingDescent.lean`, `FullDefectRingFullIdeal.lean` |
| `443c2e380b9a9092d2ba40f92c9195c08b340798` | 4253 | `FullDefectRingCountable.lean` |
| `36b7fb0010b1b677c3ba58a311f1f04ca6007e1d` | 4257 | `FullDefectRingSimple.lean` |
| `1dd5b6630fcab4116b709f1d0625e8c718be6b5a` | 4257 | `FullDefectRingMaximal.lean` |
| `0c2cfacd517265f4df77bb30863b356694dbb881` | 4262 | `FullDefectRingEndpoints.lean` |
| `aabd8e02b344687e0de71d79fe4c478d512d0700` | 4267 | `FullDefectRingProperIsometry.lean` |

## The printed clauses, and what each still assumes

`fullDefectAtFixedRing` (lane `ring-b-alg`,
`Leavitt/FullDefectRingAtFixedRing.lean`, commit `3f69392c9`) discharged the
compression calculation, so every clause below is either unconditional or
carries a single named hypothesis.

| printed | proposition | hypothesis-free form |
|---|---|---|
| `thm:full-defect-ring` | `PrintedFullComplementaryIdempotents` | over prime characteristic |
| sentence after it | `PrintedFullnessHolds` | yes, always |
| `cor:simple-infinite-ring`, 1st | `PrintedSimpleInfiniteRing` | over prime characteristic |
| `cor:simple-infinite-ring`, 2nd | `PrintedLeavittAlgebraFullDefect` | over prime characteristic |
| `cor:one-sided-ring-maximal`, 2nd | `PrintedOneSidedRingMaximalReducedCStar` | over prime characteristic |
| `cor:one-sided-ring-maximal`, 1st | `PrintedOneSidedRingMaximalIsometry` | no; see below |

Outside prime characteristic each carries exactly one leading hypothesis,
`FinitelyGeneratedRingGeneralRankElementaryPropertyT`, which is lane
`ejz-integral`'s.

## Module by module

### `FullDefectRingCore`

* `SaturatedPrintedDefectRadical` / `manuscriptSaturatedPrintedDefectRadical`
  (`#audit_closed_axioms`) — the last step of the printed proof, with no ring in
  it: countable `G`, `L ≤ G` with `(T)`, `(T)` for `G`, and
  `printedDefect L = ⊤` give the full MF radical in both readings, triviality
  of every homomorphism to an MF group, and `¬ IsCDEOperatorMF G` for
  nontrivial `G`.  This is the interface `ring-b-alg` consumes.
* `countable_elementaryGroup`.

### `FullDefectRingDescent`

The printed "general countable `R`" paragraph, as pure group theory.
`subringElementary`, `subringElementary_le_map`,
`elementaryGroup_le_finiteCoefficientSubgroup`,
`exists_finset_elementaryGroup_le_map`,
`isFinitelyGeneratedRing_subringClosure`.

### `FullDefectRingFullIdeal`

`exists_sum_eq_one_of_isSimpleRing`, `isSimpleRing_full_of_not_directlyFinite`,
`leavittFamily_full`, `completeMatrixFamily_full`.

### `FullDefectRingCountable`

`FullDefectAtFixedRing`;
`PrintedFullComplementaryIdempotentsOverSubrings` (the sharpest form, property
`(T)` asked only of the finitely generated subrings);
`PrintedFullComplementaryIdempotents`;
`PrintedFullComplementaryIdempotentsPrimeChar`.

### `FullDefectRingSimple`

`exists_oneSidedInverse_of_not_isDedekindFinite`; `PrintedSimpleInfiniteRing`,
`PrintedLeavittAlgebraFullDefect` and their `...PrimeChar` forms.

### `FullDefectRingMaximal`

`nontrivial_elementaryGroup`, `not_isCDEOperatorMF_of_killsMFTargets`;
`PrintedOneSidedRingMaximalReducedCStar` and its `...PrimeChar` form.

### `FullDefectRingProperIsometry`

`properIsometry_of_strictCompression`,
`OneSidedCompressorStrictContainment`, `PrintedOneSidedRingMaximalIsometry` and
its `...PrimeChar` form.

### `FullDefectRingEndpoints`

`PrintedFullnessHolds` / `manuscriptPrintedFullnessHolds`
(`#audit_closed_axioms`); `PrintedFullDefectRingProgramme` and its
`...PrimeChar` form.

### `FullDefectRingUnconditional`

Spends `fullDefectAtFixedRing` once, and names each printed clause in its two
remaining forms: `manuscript...PrimeCharUnconditional` (hypothesis-free, all
audited closed) and `manuscript...FromEJZ` (one hypothesis).

## Open obligations

Two, and neither is this lane's mathematics.

1. `FinitelyGeneratedRingGeneralRankElementaryPropertyT`, lane `ejz-integral`.
   Every clause outside prime characteristic carries it.

2. The strictness of the compression, which is the first sentence of
   `cor:one-sided-ring-maximal` and is *not* a consequence of
   `thm:full-defect-ring`:

```lean
def OneSidedCompressorStrictContainment : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] (s t : R), t * s = 1 → s * t ≠ 1 →
    (∀ (S : Subring R), IsFinitelyGeneratedRing ↥S → ∀ (k : ℕ), 3 ≤ k →
        HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin k) ↥S)) →
      ∀ (n : ℕ), 4 ≤ n →
        ∃ (Γ : Subgroup (elementaryGroup (Fin n) R))
          (u : elementaryGroup (Fin n) R),
          HasKazhdanPropertyT.{0, 0} ↥Γ ∧
            Γ.map (MulAut.conj u).toMonoidHom < Γ
```

   At rank four the whole content is
   `(core R).map (MulAut.conj (compressor P)).toMonoidHom < core R` when
   `P.e ≠ 0`; the `≤` half is `compressor_compresses_core`.  A route for the
   strict half: the units `u` with `E * u = E`, for `E = diag(e,e,e,0)`, form a
   subgroup (from `E u = E` and `E v = E` one gets `E (u v) = E`, and
   `E = E u⁻¹`); every conjugated core root `e_{ij}(sat)` lies in it because
   `E * single i j c = single i j (e c)` and `es = 0`; and `e_{01}(1)` does not,
   because `E * (1 + single 1) = E + single e ≠ E` exactly when `e ≠ 0`.

## Coordination note

`ring-b-alg` and this lane both wrote the rank-four-to-rank-`n` extension and
the seam that discharges `FullDefectAtFixedRing`.  Theirs landed; the copy
written here was deleted unlanded rather than renamed, because a same-content
declaration under a different name is what the duplicate scan cannot see.
