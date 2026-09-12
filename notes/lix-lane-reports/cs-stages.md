# cs-stages

Owns `Analysis/LIXBlockProjections.lean`, `Analysis/LIXCornerAlgebra.lean`,
`Analysis/LIXStageAlgebra*.lean`, `Analysis/LIXConnectingMap*.lean`.

**Status: COMPLETE.**  All eight owned modules are green and rooted, every deliverable is
landed, and nothing is authored-unverified.  The last one, `isFull_climb_of_ne_zero`
(`Analysis/LIXConnectingMapFullnessTower.lean`, 2986 jobs, 5fa1c8f8c), is verified on main and
wired; cs-endpoint consumes it as
`lixLimit_isSimpleCStar (isFull_climb_of_ne_zero (T := lixTower) (fun _ => rfl))`.

Modules, all `Build completed successfully (N jobs)` with `ERROR_LINES=0`, built and not
replayed, no `sorry`/`admit`/`axiom`/`opaque`: `LIXBlockProjections` 2966, `LIXCornerAlgebra`
2973, `LIXConnectingMapPoints` 2975, `LIXStageAlgebra` and `LIXConnectingMap` 2977,
`LIXStageAlgebraSeparable` 2978, `LIXConnectingMapFullness` 2980,
`LIXConnectingMapFullnessSum` 2981, `LIXConnectingMapFullnessTower` 2986.

`LIXStageAlgebraSeparable` (5195146e5) is the bonus conjunct: `SeparableSpace (StageAlgebra i)`
and its family form, the hypothesis of `CStarTower.separableSpace_limit`.  Twelve lines of
instance plumbing, no proof — `X_n` second countable, `CStarMatrix`'s topology
`inferInstanceAs` the entrywise one, `ContinuousMap.instSecondCountableTopology` for the
function space, then the subtype.  Going through second countability rather than separability
is what makes the subtype step work, since separability is not hereditary.  The step that
could have failed is that `C(X, Y)` carries the compact-open topology while the C-star
structure on `C(X, A)` for compact `X` is the uniform one; Mathlib builds the metric so the
instances agree.

Everything builds in under fifteen seconds except `LIXConnectingMapFullnessSum`, which needs
`set_option maxHeartbeats 4000000` and takes about 115 seconds; it is alone in its file so
that nothing else waits behind it.

This report supersedes the earlier draft below the fold (kept for its vocabulary tables and
traps, both still accurate).

## 1. GREEN

**`Build completed successfully (2977 jobs)`**, probe targets

```
GroupApproximation.Analysis.LIXBlockProjections
GroupApproximation.Analysis.LIXCornerAlgebra
GroupApproximation.Analysis.LIXStageAlgebra
GroupApproximation.Analysis.LIXConnectingMapPoints
GroupApproximation.Analysis.LIXConnectingMap
```

with `ERROR_LINES=0` and `✔ [2977/2977] Built GroupApproximation.Analysis.LIXConnectingMap
(12s)` — genuinely built in this probe, not replayed.  Landed at `451a97231` (this session's
`LIXStageAlgebra` additions and the new `LIXConnectingMap.lean`) on top of `3e640942b` /
`bfc4fce7f` / `c598f543c` (`LIXBlockProjections`, `LIXCornerAlgebra`,
`LIXConnectingMapPoints`, landed earlier in the shared tree by the parallel `cs-stages`
session — same lane, same ownership, no conflict).  No `sorry`/`admit`/`axiom`/`opaque`;
`-DwarningAsError=true`.

### The connecting map, as delivered

```lean
-- Analysis/LIXConnectingMap.lean
STW59.connect (i : ℕ) : StageAlgebra i →⋆ₐ[ℂ] StageAlgebra (i + 1)
STW59.connect_injective (i : ℕ) : Function.Injective (connect i)
STW59.connect_apply (i : ℕ) (a : StageAlgebra i) : connect i a = connectFun i a  -- @[simp], rfl
```

This is exactly `cs-limit`'s NEEDS (`notes/lix-lane-reports/cs-limit.md` §3): unital by
construction (`StarAlgHom`), injective, and `CStarTower.ofInjective connect connect_injective`
should build directly against it.  `connect_apply` being `rfl` is deliberate and load-bearing
(a downstream peer flagged this): it lets `stageEval (i+1) w (connect i b)` unfold
definitionally to `matEval w (connectMatrix i (toFunctionMatrix ↑b))`, which the fullness
argument below needs.

Also delivered, all in the `STW59` namespace:

```lean
Nontrivial (STW59.StageAlgebra i)              -- instance, all i, not just i = 0
STW59.toFunctionMatrix_mem_corner {i} (a : StageAlgebra i) :
    Eproj i * toFunctionMatrix ↑a * Eproj i = toFunctionMatrix ↑a
STW59.stageFrame, .stageFrame_isometry, .stageFrame_mul_conjTranspose
STW59.compressMat, .compressMat_add/_smul/_mul/_Eproj/_conjTranspose
STW59.connectMatrix, .connectMatrix_add/_smul/_mul/_Eproj/_conjTranspose
STW59.eproj_mul_connectMatrix_mul_eproj      -- the membership lemma
STW59.connectFun, .connectFun_one/_mul/_add/_smul/_star/_injective
STW59.pullMat_injective_of_surjective         -- generic; injectivity's engine
```

`STW59.StageAlgebra i` continues to satisfy exactly the NEEDS recorded by `cs-limit`:
`Type` (not `Type*`), `CStarAlgebra` instance, and now `Nontrivial` for every stage rather
than only stage `0`.

### The tower-level fullness, the last deliverable (green, 2986 jobs, 5fa1c8f8c)

`Analysis/LIXConnectingMapFullnessTower.lean`, `Build completed successfully (2986 jobs)`,
`ERROR_LINES=0`, all of `LIXStageAlgebra`, `LIXConnectingMap`, `LIXConnectingMapFullness`,
`LIXConnectingMapFullnessSum` and `LIXConnectingMapFullnessTower` genuinely built.

```lean
theorem STW59.isFull_climb_of_ne_zero {T : LIX.CStarTower STW59.StageAlgebra}
    (hT : ∀ i, T.succHom i = STW59.connect i) (k : ℕ) (a : STW59.StageAlgebra k) (hne : a ≠ 0) :
    ∃ j, k ≤ j ∧ GroupApproximation.LIX.IsFull (T.climb j k a)
```

This is the hypothesis of `LIX.CStarTower.isSimpleCStar_limit_of_ne_zero` verbatim: raw
`T.climb` with the target index first, `IsFull` the finite-sum predicate, no positivity.
cs-limit's `lixTower_succHom` discharges `hT` by `rfl`, so their `hfull` is
`STW59.isFull_climb_of_ne_zero lixTower_succHom`.  The tower is a parameter rather than
`lixTower` itself so that this file does not import cs-limit's and there is no cycle.

Supporting: `STW59.stageEval_climb_ne_zero` carries nonvanishing up the tower through the
pulled-back block; `continuous_stageEval` and `isOpen_stageEval_ne_zero` open the
nonvanishing set.  No transport appears anywhere, because `basePr h w = w` for `h : k ≤ k`
and `basePr h' (baseProj i w) = basePr h w` are both `rfl` by structure eta on `Fin.castLE`.

`LIXStageAlgebra` also gains `instCStarAlgebraStageAlgebraPi : ∀ n, CStarAlgebra (StageAlgebra n)`.
`LIX.CStarTower` binds that as a family and instance search does **not** assemble it from the
per-stage instance; without it `CStarTower STW59.StageAlgebra` fails to elaborate, which is a
trap cs-limit hits too.

### The fullness theorem, added after that probe

| module | job count | commit |
|---|---|---|
| `Analysis/LIXConnectingMapFullness` | 2980 | 9b447776c |
| `Analysis/LIXConnectingMapFullnessSum` | 2981 | 6b4b704d3 |

Both `Build completed successfully (N jobs)`, `ERROR_LINES=0`, `PROBE GREEN`, built and not
replayed.  What they deliver, in the shape `notes/lix-lane-reports/cs-simplicity.md` asked
for:

```lean
-- Analysis/LIXConnectingMapFullness.lean
compressMat_eq_zero_iff          -- the frame compression is injective on the corner
stageEval_connect_inl            -- the (1,1) block of φ_i(a) at w is a at π_i(w)
stageEval_connect_ne_zero_of_pull -- nonvanishing travels up the tower
stageEval_connect_ne_zero        -- φ_i(b) vanishes in NO fibre once b(x_i) ≠ 0
sum_single_conj                  -- ∑_{s,t} (P E_st P) X (P E_ts P) = Tr X • P
-- Analysis/LIXConnectingMapFullnessSum.lean
isFull_of_forall_stageEval_ne_zero  -- nonzero in every fibre ⇒ LIX.IsFull
isFull_connect_of_stageEval_ne_zero -- b(x_i) ≠ 0 ⇒ IsFull (connect i b)
```

**Positivity is not used anywhere.**  The manuscript takes `a ≥ 0` so that the fibre traces
are nonzero; instead the argument runs on `aᴴ a`, whose trace at `w` is `∑_{s,t} |a(w)_{st}|²`
(`eq_zero_of_trace_conjTranspose_mul_self`, green in `LIXBlockProjections`).  So
cs-simplicity's `0 ≤ a` hypothesis is spare.  And the conclusion is exact: the matrix units
of the ambient homogeneous algebra are global, so `∑ x_l * a * y_l = 1` holds on the nose and
`LIX.isFull_of_sum_eq_one` applies with no ε.

`LIXConnectingMapFullnessSum` needs `set_option maxHeartbeats 4000000` and takes about 110
seconds; it is alone in its file so that nothing else waits on it.

## 2. AUTHORED, UNVERIFIED

Nothing.  All five owned modules build.

The **fullness input for `cs-simplicity`** (§4 of the earlier draft below) is designed but
not yet landed in this lane's files: a peer session drafted it against `connect`/`connect_apply`
while this session was closing out `LIXConnectingMap`, and it is expected back for wiring
next (composites `φ_{k,i}` are not needed from this lane — `cs-limit`'s
`CStarTower.climb`/`climbHom` already supplies them generically once `connect` is in hand).

## 3. NEEDS

Nothing blocking.  For whoever wires the fullness theorem next: the recipe already sketched
(matrix-unit averaging on `Tr(aᴴa) • P = ∑ P E_{st} P · aᴴa · P E_{ts} P`, applied after using
`connect_apply`'s `rfl` to reduce a fibre value of `connect i b` to `connectMatrix i
(toFunctionMatrix b)`) needs no positivity hypothesis and should be provable entirely inside
`Analysis/LIXConnectingMap.lean` or a sibling `LIXConnectingMapFullness.lean`, both owned by
this lane.

## 4. TRAPS

**A red dependency may be another lane's uncommitted edit, not a real error** (cs-limit's
finding).  `ccprobe.sh` rsyncs the whole shared working tree at the start of a run, so an
in-flight edit by another lane can red a green import for the duration of one probe.  Re-run
before reporting a peer's module broken.


New, from assembling `connect`:

* **Kronecker/fromBlocks distributivity lemmas run in *both* directions across Mathlib, and
  guessing wrong compiles as a `rw` pattern-match failure, not a type error.**
  `Matrix.mul_kronecker_mul : (A*B) ⊗ₖ (A'*B') = A ⊗ₖ A' * B ⊗ₖ B'` — going from a *product of
  Kronecker terms* to a *Kronecker of products* needs `←`, not the forward direction (the
  forward direction goes the other way).  `Matrix.fromBlocks_add : fromBlocks A B C D +
  fromBlocks A' B' C' D' = fromBlocks (A+A') …` is forward-oriented the way its name suggests
  (sum of blocks → block of sums), but `Matrix.fromBlocks_smul : x • fromBlocks A B C D =
  fromBlocks (x•A) …` has the smul *outside* on the LHS — so distributing a smul *into* the
  blocks is the forward direction too, the opposite of what the `add`/`mul_kronecker_mul`
  pattern would suggest.  Read the actual `:=`-body before choosing `←`; the signature line
  alone (as returned by a `grep -n` truncated to the `theorem` line) does not show which side
  states which.
* **`Matrix.zero_add`/`Matrix.add_zero` do not exist.**  `Matrix`'s additive structure is the
  generic `AddCommMonoid`, so the cleanup after `fromBlocks_multiply`/`_add` introduces
  `0 + 0`-shaped cross terms that only the *unprefixed* `zero_add`/`add_zero` close;
  `Matrix.mul_zero`/`Matrix.zero_mul` (the rectangular-multiplication ones) **do** need the
  prefix, since those are restated for `HMul` and not derivable from a generic monoid lemma.
* **Generic `mul_smul_comm`/`smul_mul_assoc` at the *matrix* type can fail to find their
  instance chain even though the fact is true.**  Asking for `SMulCommClass ℂ (Matrix n n ℂ)
  (Matrix n n ℂ)` directly is a different (and apparently less reliably found) search than
  asking for `Matrix.mul_smul`/`Matrix.smul_mul` (`Mathlib/Data/Matrix/Mul.lean`), which are
  stated with the scalar acting on the *entry* ring (`[DistribMulAction R α]`, `α` = the
  matrix's entries) rather than on the whole matrix type, and resolve without incident. Prefer
  the `Matrix.`-namespaced versions over the bare `Algebra`/`Group.Action` ones whenever both
  sides of a smul-through-multiplication identity are matrices.
* **`rw`'s automatic trailing `rfl` does not always fire across a `def` unfold.**  Closing a
  goal of the shape `reindex (…) (block-diagonal literal 1 ⊗ₖ L) = reindex (…) (newBlock i)`
  (or `ofFunctionMatrix (Eproj (i+1)) = stageProj (i+1)`) needs an explicit trailing `rfl`
  after the `rw` chain even though the two sides are definitionally equal by unfolding a
  plain, non-irreducible `def` (`newBlock`, `stageProj`); `rw` did not discharge it on its own.
* **A bare `ext` after `Matrix.ext`-shaped goals over `C(X, ℂ)`-valued entries recurses one
  level too far**, additionally invoking `ContinuousMap.ext` and landing on a goal about point
  values rather than about the matrix entries (`C(X, ℂ)` elements) — which then does not match
  a hypothesis stated as an equality of the entries themselves.  Use `refine Matrix.ext fun x y
  => ?_` to stop exactly at the entry level.

Everything from the previous draft (vocabulary tables for `LIXBlockProjections`,
`LIXStageAlgebra`, `LIXConnectingMapPoints`, and traps 1–6) remains accurate and is kept
below.

---

## Earlier draft (2026-09-05, ~19:00–20:20 CDT), kept for its vocabulary tables

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
blockUnitary i u = fromBlocks u 0 0 (Hproj i)   -- the manuscript's w_i = u ⊕ 1_H, with
   blockUnitary_mem_corner, blockUnitary_star_mul, blockUnitary_mul_star, blockUnitary_one
HprojY i : Matrix (HIdx i) (HIdx i) C(baseY i, ℂ)   -- H_i over Y_i alone, for Lemma 2
   Hproj_eq_pullMat : Hproj i = pullMat (baseYproj i) (HprojY i)
   isStarProjection_HprojY, trace_HprojY, lineProjY, newLineY, newBlockY, baseYtrunc
pullMat_comp, pullMat_kronecker, fromBlocks_diag_mul
pullMat f, constMat X, and their mul/one/star/add/smul/trace lemmas,
  pullMat_injective_of_surjective (new: pullback along a surjection is injective)
reindex_add/_smul/_mul/_conjTranspose (new: `Matrix.reindex e e'` compatibility lemmas)
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

### Stage algebras (`LIXStageAlgebra`, green)

```lean
stageProj i : SectionAlgebra (baseX i) (EIdx i)   -- ofFunctionMatrix (Eproj i)
StageAlgebra i = Corner (stageProj i) (isStarProjection_stageProj i)   -- A_i, a `Type`
   -- CStarAlgebra / Ring / StarRing / NormedAlgebra ℂ / Nontrivial instances, unit E_i
sectionEval w a, stageEval i w a : Matrix (EIdx i) (EIdx i) ℂ
   -- ⋆-hom to the fibre; stageEval_mul/_add/_star/_one are all `rfl`
stageAlgebra_eq_zero_iff : a = 0 ↔ ∀ w, stageEval i w a = 0
stageEval_mem_corner, trace_stageEval_one
toFunctionMatrix / ofFunctionMatrix : mutually inverse, `rfl` both ways;
   toFunctionMatrix_add/_mul/_star/_smul and toFunctionMatrix_injective (new)
toFunctionMatrix_mem_corner (new): the corner condition read back at the matrix level
```

### The points (`LIXConnectingMapPoints`, green)

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
sequence and never has to be transported across a dependent type.

## Traps from the earlier draft (all still accurate)

1. **`C(X, CStarMatrix ι ι ℂ)` breaks `mul_add`, `star_mul` and (before abstraction)
   `mul_assoc`.**  A bare instance search for `Mul`/`Star` returns `ContinuousMap.instMul` /
   `ContinuousMap.instStar`, which are not the instances inside `Semiring`/`StarRing`; the
   lemma then fails to apply, with either "failed to synthesize LeftDistribClass" or a
   `@star _ ContinuousMap.instStar` versus `@star _ StarMul.toInvolutiveStar.toStar`
   mismatch.  **Fix**: develop the corner over an abstract `{A : Type*} [CStarAlgebra A]`,
   where every instance comes from one chain, and cross to `SectionAlgebra` exactly once, by
   application (`ofFunctionMatrix_mul` and friends).  Confirmed again live: the two
   `Diagnostics` `example`s that tried this directly on `SectionAlgebra` are now documented
   (not deleted) as the negative case, since `LIXCornerAlgebra`'s own `Corner`/`StageAlgebra`
   construction never needs it.
2. **A recursive `def` index type makes `rw` fail at successor indices.**  `HIdx` is
   semireducible, so `Fintype (HIdx (i+1))` elaborates to `instFintypeHIdx (i+1)` and not to
   `Sum.instFintype`; a `rw` with a block lemma then dies with "not type-correct under the
   instances transparency level".  **Fix**: cross by application, never by `rw`.
3. **`IsStarProjection.one` and `.zero` take the carrier explicitly** at this pin, so it is
   `IsStarProjection.one _`, never `IsStarProjection.one`.
4. **`rw [Fin.succ_inj]` inside an `ite` fails** with "motive is not type correct".
   Case-split with `by_cases` and use `Matrix.one_apply_eq` / `Matrix.one_apply_ne` instead.
5. **`rw [h]` with `h : ∀ a, f a = g a` rewrites every occurrence with the same
   instantiation**, so a second `rw [h]` for the same argument errors.  Pass the argument
   explicitly whenever two different instantiations are in play.
6. **The first `ccprobe.sh` run on a fresh clone died with "Argument list too long"** after
   the clone step, exit 0, no build.  Fixed upstream; rerun if seen.
