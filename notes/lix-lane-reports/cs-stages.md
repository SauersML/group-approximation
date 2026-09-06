# cs-stages

Owns `Analysis/LIXBlockProjections.lean`, `Analysis/LIXCornerAlgebra.lean`,
`Analysis/LIXStageAlgebra*.lean`, `Analysis/LIXConnectingMap*.lean`.

Written by the Opus lane after its third probe (2026-09-05, ~19:00 CDT).  While the lane
was out, the lead handed the four files to `cs-stages-s`; from that point this lane is a
reviewer and does not edit them.  Everything below is measured, not expected.

## 1. GREEN

| module | evidence |
|---|---|
| `Analysis/LIXBlockProjections` | `Build completed successfully (2966 jobs)`, `ERROR_LINES=0`, `PROBE GREEN`, `✔ Built … LIXBlockProjections (13s)` — built, not replayed. Commit bfc4fce7f. |
| `Analysis/LIXCornerAlgebra` | `Build completed successfully (2975 jobs)`, `ERROR_LINES=0`, `PROBE GREEN`, `✔ Built … LIXCornerAlgebra (13s)`. Commit c598f543c. |
| `Analysis/LIXConnectingMapPoints` | same run, `✔ Built … LIXConnectingMapPoints (9.3s)`. Commit c598f543c. |

The two counts differ only because the target sets differ: 2966 for the block file alone,
2975 for the three together.  No `sorry`, `admit`, `axiom` or `opaque`; no warnings, under
`-DwarningAsError=true`.

## 2. AUTHORED, UNVERIFIED

| module | state |
|---|---|
| `Analysis/LIXStageAlgebra` | owned by `cs-stages-s` since the 20:10 roster; `A_i` as a unital C⋆-algebra, `stageEval`, `toFunctionMatrix` |
| `Analysis/LIXConnectingMap` | `cs-stages-s`, 404 lines, no `sorry`, `connect` and `connect_injective` complete; reviewed by this lane against the draft, architecture correct |
| the fullness theorem | drafted at `/private/tmp/claude-501/-Users-user-nonsofic-existence/0d670c23-df04-42d0-9de1-e659ef71184e/scratchpad/LIXConnectingMap_draft.lean`, waiting for the files to come back |

## 3. What is delivered, and the exported vocabulary

Peers should build against these names.  The index design is what makes the connecting map
free, so it is spelled out.

### Base spaces and index types (`LIXBlockProjections`, green)

```lean
stageRank i = 2 ^ (i + 1)                    -- r_i
hrank : ℕ → ℕ                                -- rank H_i, hrank i + 2 = stageRank i
baseY i = ∀ j : Fin i, CP (stageRank j)      -- Y_i
baseX i = ↥sphereFour × baseY i              -- X_i, CompactSpace + Nonempty instances
basePr (h : k ≤ i) : C(baseX i, baseX k)     -- π_{k,i}; basePr_comp, basePr_self,
                                             -- basePr_surjective
baseProj i = basePr (Nat.le_succ i)          -- π_i
NIdx i = Fin (stageRank i) × Fin (stageRank i + 1)
HIdx : ℕ → Type                              -- HIdx 0 = Empty, HIdx (i+1) = HIdx i ⊕ NIdx i
EIdx i = Fin 2 ⊕ HIdx i
eIdxSucc i : EIdx i ⊕ NIdx i ≃ EIdx (i + 1)  -- the fixed Equiv.sumAssoc
Hproj i, Eproj i                             -- H_i, E_i = 𝟏² ⊕ H_i, as
                                             -- Matrix (·) (·) C(baseX i, ℂ)
trace_Hproj, trace_Eproj, trace_matEval_Eproj -- ranks: hrank i, stageRank i
Eproj_succ i : Eproj (i+1) = Matrix.reindex (eIdxSucc i) (eIdxSucc i)
                 (Matrix.fromBlocks (pullMat (baseProj i) (Eproj i)) 0 0 (newBlock i))
newLine i, newBlock i = 1 ⊗ₖ newLine i       -- L_{i+1}, L_{i+1}^{⊕ r_i}
exists_frame                                 -- a star projection of trace k over ℂ is s sᴴ
                                             -- for an isometry s : ℂ^k → ℂ^n
eq_zero_of_trace_conjTranspose_mul_self      -- trace (Aᴴ A) = 0 → A = 0
Eproj_ne_zero                                -- so Nontrivial (StageAlgebra i)
blockUnitary i u = fromBlocks u 0 0 (Hproj i)   -- the manuscript's w_i = u ⊕ 1_H, with
   blockUnitary_mem_corner, blockUnitary_star_mul, blockUnitary_mul_star, blockUnitary_one
HprojY i : Matrix (HIdx i) (HIdx i) C(baseY i, ℂ)   -- H_i over Y_i alone, for Lemma 2
   Hproj_eq_pullMat : Hproj i = pullMat (baseYproj i) (HprojY i)
   isStarProjection_HprojY, trace_HprojY, lineProjY, newLineY, newBlockY, baseYtrunc
pullMat_comp, pullMat_kronecker, fromBlocks_diag_mul
pullMat f, constMat X, and their mul/one/star/trace lemmas
Fproj, hopfProj, hopfCol, murrayVonNeumannEquiv_Fproj   -- for cs-clutching, unchanged
isLocallyConstant_trace
```

`Eproj_succ` is the manuscript's `E_{i+1} ≅ π_i^* E_i ⊕ (E_i(x_i) ⊗ L_{i+1})` with the
second summand written `𝟏_{r_i} ⊗ L_{i+1}` under the identification `E_i(x_i) ≅ ℂ^{r_i}`
of `exists_frame`.  The equivalence is a fixed reindexing, not a unitary: that is the whole
point of making `HIdx` recursive.

**For cs-clutching**: `EIdx i = Fin 2 ⊕ HIdx i` and `Eproj i = Matrix.fromBlocks 1 0 0 (Hproj i)`
are definitional, so `w_i := Matrix.fromBlocks u 0 0 (Hproj i)` is the block sum you want,
and `F ⊕ p_H` over `S⁵ × Y_i` lives on `Fin 3 ⊕ HIdx i`.

### Stage algebras (`LIXStageAlgebra`, unverified)

```lean
stageProj i : SectionAlgebra (baseX i) (EIdx i)   -- ofFunctionMatrix (Eproj i)
StageAlgebra i = Corner (stageProj i) (isStarProjection_stageProj i)   -- A_i
   -- CStarAlgebra / Ring / StarRing / NormedAlgebra ℂ instances, unit E_i
sectionEval w a, stageEval i w a : Matrix (EIdx i) (EIdx i) ℂ
   -- ⋆-hom to the fibre; stageEval_mul/_add/_star/_one are all `rfl`
stageAlgebra_eq_zero_iff : a = 0 ↔ ∀ w, stageEval i w a = 0
stageEval_mem_corner, trace_stageEval_one
toFunctionMatrix / ofFunctionMatrix : mutually inverse, `rfl` both ways
```

### The points (`LIXConnectingMapPoints`, unverified)

```lean
baseXinf = ↥sphereFour × (∀ j : ℕ, CP (stageRank j))   -- X_∞
truncate i : C(baseXinf, baseX i), truncate_surjective, basePr_truncate (rfl)
stagePoint i : baseX i                                  -- the manuscript's x_i
exists_stagePoint_mem_of_isOpen : IsOpen U → U.Nonempty →
    ∃ (i : ℕ) (h : k ≤ i), basePr h (stagePoint i) ∈ U
dense_stagePoint_tail (k) : Dense {y | ∃ i (h : k ≤ i), basePr h (stagePoint i) = y}
```

The repetition is the Cantor pairing, and the dense sequence lives on the FIXED space
`X_∞`, so that `(Nat.unpair (Nat.pair k n)).2 = n` is only ever used in the index of a
sequence and never has to be transported across a dependent type.  That is the difference
between a ten-line proof and a cast swamp.

### The connecting map (drafted, handed to cs-stages-s)

```lean
exists_stageFrame i, stageFrame i, stageFrame_isometry, stageFrame_range
stageCompress i M = (stageFrame i)ᴴ * matEval (stagePoint i) M * stageFrame i
connectBlock i M = constMat _ (stageCompress i M) ⊗ₖ newLine i
connectMat i M = Matrix.reindex (eIdxSucc i) (eIdxSucc i)
                   (Matrix.fromBlocks (pullMat (baseProj i) M) 0 0 (connectBlock i M))
connectMat_Eproj : connectMat i (Eproj i) = Eproj (i + 1)     -- Eproj_succ backwards
connect i : StageAlgebra i →⋆ₐ[ℂ] StageAlgebra (i + 1)
connect_injective i : Function.Injective (connect i)
```

### Fullness, for cs-simplicity

The shape in `notes/lix-lane-reports/cs-simplicity.md` is met, and **positivity is not
needed anywhere**:

1. `a ≠ 0` in `A_k` gives a nonempty open `U = {w | stageEval k w a ≠ 0}`;
   `exists_stagePoint_mem_of_isOpen` gives `i ≥ k` with `π_{k,i}(x_i) ∈ U`; the pulled-back
   block of `connect` gives `stageEval i (stagePoint i) (climb i k a) ≠ 0`.
2. `stageEval_connect_ne_zero`: if `b(x_i) ≠ 0` then `connect i b` is nonzero in **every**
   fibre, because the new block is `sᴴ b(x_i) s ⊗ taut(w)`, the compression is injective on
   the fibre corner (`b(x_i) = s sᴴ b(x_i) s sᴴ`), and `taut(w)` is a rank-one projection.
3. `isFull_of_forall_stageEval_ne_zero`: nonzero in every fibre implies full, by the
   matrix-unit averaging `∑_{s,t} (P E_{st} P) X (P E_{ts} P) = Tr(X) • P` applied to
   `X := aᴴ a`, whose trace is the nowhere-zero continuous function
   `w ↦ ∑_{s,t} |a(w)_{st}|²`, invertible in `C(X_{i+1}, ℂ)`.  Scaling the left coefficients
   by that inverse produces `∑ x_l * a * y_l = 1` exactly, so `LIX.isFull_of_sum_eq_one`
   closes it with no ε.

So `fullness (k) (a) (h0 : 0 ≤ a) (hne : a ≠ 0) : ∃ j, k ≤ j ∧ IsFull (T.climb j k a)`
holds with `h0` unused; cs-simplicity can keep it in the signature.

## 4. NEEDS

Nothing from a peer.  Two things from the lead:

* the two `example` deletions in `LIXCornerAlgebra` (lines 313 and 321), or the file back
  for sixty seconds;
* the four files back after `cs-stages-s` lands `connect`, for the composites `φ_{k,i}`,
  the fullness theorem, and the `w_i`/`v_i` export for cs-clutching.

## 5. TRAPS

1. **`C(X, CStarMatrix ι ι ℂ)` breaks `mul_add`, `star_mul` and (before abstraction)
   `mul_assoc`.**  A bare instance search for `Mul`/`Star` returns `ContinuousMap.instMul` /
   `ContinuousMap.instStar`, which are not the instances inside `Semiring`/`StarRing`; the
   lemma then fails to apply, with either "failed to synthesize LeftDistribClass" or a
   `@star _ ContinuousMap.instStar` versus `@star _ StarMul.toInvolutiveStar.toStar`
   mismatch.  This cost about thirty errors in one probe.  **Fix**: develop the corner over
   an abstract `{A : Type*} [CStarAlgebra A]`, where every instance comes from one chain, and
   cross to `SectionAlgebra` exactly once, by application (`ofFunctionMatrix_mul` and
   friends).  This is a sharper form of the `CStarMat` trap cs-endpoint reported: the seam is
   not only `CStarMat`, it is any `C(X, -)` over a `CStarMatrix`.
2. **A recursive `def` index type makes `rw` fail at successor indices.**  `HIdx` is
   semireducible, so `Fintype (HIdx (i+1))` elaborates to `instFintypeHIdx (i+1)` and not to
   `Sum.instFintype`; a `rw` with a block lemma then dies with "not type-correct under the
   instances transparency level".  **Fix**: cross by application, never by `rw` —
   `have h : Matrix.trace (Hproj (i+1)) = _ := trace_fromBlocks _ _ _ _`.  Making `HIdx`
   reducible does not fix it (it moves the mismatch, because a general-`i` lemma still
   carries `instFintypeHIdx`).
3. **`IsStarProjection.one` and `.zero` take the carrier explicitly** at this pin
   (`variable (R) in` before them in `Mathlib/Algebra/Star/StarProjection.lean`), so it is
   `IsStarProjection.one _`, never `IsStarProjection.one`.
4. **`rw [Fin.succ_inj]` inside an `ite` fails** with "motive is not type correct", because
   the `Decidable` instance depends on the rewritten term.  Case-split with `by_cases` and
   use `Matrix.one_apply_eq` / `Matrix.one_apply_ne` instead.
5. **`rw [h]` with `h : ∀ a, f a = g a` rewrites every occurrence with the same
   instantiation**, so a second `rw [h]` for the same argument errors.  Pass the argument
   explicitly (`rw [hs0 a, hs0 b]`) whenever two different instantiations are in play.
6. **The first `ccprobe.sh` run on a fresh clone died with "Argument list too long"** after
   the clone step, exit 0, no build.  The lead has fixed the helper; if you see it, rerun.
