# cs-clutching

Owns `Analysis/LIXClutching.lean`, `Analysis/LIXGeneratorUnitary.lean`,
`Analysis/LIXObstructionComplementUnitary.lean`, `Analysis/LIXLemmaSix*.lean`.

**The lane is closed.** Corollary 4 and the endpoint are proved and pushed; the
only thing between `LemmaTwoHolds` and `HasK1InjWitness LIXLimit` is
`Analysis/LIXLemmaSixCor4.lean`, which is green.

## 1. THE ENDPOINT

```lean
theorem lixLimit_hasK1InjWitness_of (h : LemmaTwoHolds) : HasK1InjWitness LIXLimit
theorem climb_genUnitary_notMem (h : LemmaTwoHolds) (j : ℕ) (hj : 0 ≤ j) :
    unitaryHom (lixTower.climbHom hj) genUnitary ∉ unitaryComponentOne (STW59.StageAlgebra j)
```

both in `Analysis/LIXLemmaSixCor4.lean`, namespace `GroupApproximation.LIX`.
The second is Corollary 4 and is the `hstage` hypothesis of
`lixLimit_hasK1InjWitness`; the first feeds it and `hdiag_genUnitary` to that
theorem. No `sorry`, no `axiom`, no `opaque` anywhere in the lane.

## 2. GREEN

Measured on this lane's own clone; every count comes with a `Built` line for the
module itself, so no green here rests on a replay.

| module | jobs |
|---|---|
| `LIXClutching`, `LIXGeneratorUnitary`, `LIXObstructionComplementUnitary` | 8658 (jointly) |
| `LIXLemmaSixGenerator` | 2981 |
| `LIXLemmaSixShape` | 2982 |
| `LIXLemmaSixClimb` | 3023 |
| `LIXLemmaSixGlue` | 2983 |
| `LIXLemmaSixDiagPath`, `LIXLemmaSixStageZero` | 2982 |
| `LIXLemmaSixDiag` | 3021 |
| `LIXLemmaSixDiagEnd` | 3022 |
| `LIXLemmaSixSouth` | 2984 |
| `LIXLemmaSixEquator` | 2985 |
| `LIXLemmaSixCompare` | 8682 |
| `LIXLemmaSixField` | 2986 |
| `LIXLemmaSixHIdx` | 8672 |
| `LIXLemmaSixCor4` | 8711 |

## 3. HOW COROLLARY 4 IS PROVED

Four modules, in dependency order.

**`LIXLemmaSixField.lean` — the unitary field.** Abstract in the `H` block: for a
continuous field of projections `P` over any base `Y`, a continuous path `W` of
unitaries of the corner `E = 𝟏² ⊕ P` running from `E` to `u ⊕ c` produces a
continuous unitary field `G` over `S⁵ × Y` with
`G · (𝟏³ − e₃e₃ᴴ) ⊕ P · Gᴴ = (𝟏³ − x xᴴ) ⊕ P`. Northern cap: the northern frame
padded by `𝟏_H`. Southern cap: the southern frame, corrected by `W` read at the
cone coordinates, and by the constant `H`-block unitary. On the equator the
correction is the seam discrepancy itself, so the two agree and
`continuous_if_le` glues them.

**No analysis at the pole, and no quotient map.** The cone radius is
`capTime x = max 0 (1 + 2 Re x₂)`, which is **clamped**: it vanishes on the whole
collar `{Re x₂ ≤ −1/2}`, where the correction is therefore the constant `W 0 = 1`
whatever the direction is. So the southern field is continuous on the collar
because it is locally the southern frame alone, and continuous off the collar
because the direction `dirPt` is continuous there; those two open sets cover the
cap. That removes the quotient-map descent, the surjectivity of the cone, the
`arcsin`, *and* the `continuousAt_of_norm_le` damping estimate that was the
approved route: none of them is needed.

**`ext3`.** The homotopy lives in `M_{Fin 2 ⊕ H}` and the field has to be a
unitary of `M_{Fin 3 ⊕ H}`. With `jIncl = incl ⊕ 𝟏`,
`ext3 P y A = jIncl A jInclᴴ + (1 − bigE P y)` carries corner unitaries to
unitaries, is multiplicative on them, and commutes with the constant complement.
`ext3` of the endpoint is `genU x ⊕ 𝟏` times a block-diagonal `𝟏³ ⊕ (c + 1 − P)`,
and those two commute, which is exactly what makes the seam close.

**`LIXLemmaSixHIdx.lean` — the two `H`-indexings.** The manuscript indexes `H` by
a sigma type `Σ (i,k), Fin (r_i + 1)` and the tower by an iterated `⊕`.
`hIdxEquiv j` is the reindexing, defined by the recursion the two sides are
defined by (`Fin.lastCases` on the block index), and `hMatY_reindex` says the two
projections agree. The only step with content is `hMatY_castSucc`: weakening a
block index does not change the entry.

**`LIXLemmaSixCor4.lean` — the assembly.** The path from
`unitaryComponentOne` is clamped to `ℝ` by `Set.projIcc`, evaluated fibrewise
(`stageEval`), and transported along `hIdxEquiv`; `HasGeneratorShape` at
`lixTower.climb j 0 genStage` identifies its endpoint as
`genU2 ⊕ c`; the field theorem produces `G`; `LIXLemmaSixCompare`'s
`not_exists_unitary_field` contradicts Lemma 2.

## 4. NEEDS

Nothing. Every input this lane was waiting on has landed:
`cs-stages`' `HprojY` and the `S⁴`-constancy of `connect`'s new block,
`cs-limit`'s flattening and second Fubini, `cc-lix-odd`'s `LemmaTwoHolds`.

Lemma 6 was **deleted**, not proved: `lixTower.climb j 0 genStage = u ⊕ c_j` is an
equality (`HasGeneratorShape`), so no path between `v_i` and `w_i` is needed, and
the unitary group of `M_r(ℂ)` is never asked to be path connected — which is just
as well, since Mathlib does not know it at pin `81a5d257`.

## 5. TRAPS

**Instance search runs at reducible transparency, so a coercion through a
non-reducible abbreviation fails.** `((y b.1 : CP (lixDD j b.1)) : Matrix …)`
does not elaborate: the subtype coercion produces
`Matrix (Fin (stageRank ↑b.1 + 1)) …`, and unifying that with the ascribed
`Matrix (Fin (lixDD j b.1 + 1)) …` needs `lixDD` unfolded, which instance search
will not do. Cure: never coerce across such a boundary — use the reducible
`CPn.entry`, or name the block family in a `def` and let `rfl` do the work.

**`ContinuousAt.mul` is the Pi-product `f * g`, and needs `Mul` on the
codomain.** Rectangular matrix products have only `HMul`, so `ContinuousAt.mul`
cannot state them at all, and for square ones it produces `(f * g)` where the
goal has a lambda — which unifies only when no metavariable is left. For a
constant-times-variable product, build the continuous map once
(`(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`) and
`comp` it.

**`rw [h] at h1 h2` rewrites the first occurrence only.** Conjugating a
`fromBlocks` gives *two* `0ᴴ`s; `rw [Matrix.conjTranspose_zero]` clears one and
the next rewrite then fails to match. Use `simp only` for anything that appears
more than once.

**`Matrix.blockDiagonal'_apply_ne`'s block indices are not determined by the
row/column arguments.** State the wrapper with the `≠` hypothesis *before* the
two indices, so the implicit block indices are fixed by it; otherwise every call
site fails with "expected `Fin (lixDD (j+1) ?b.fst + 1)`".

**An ambiguous numeral picks up `CStarMatrix`'s `HMul`.** `incl * 1 * inclᴴ`
elaborates the `1` at `ℕ`, and the error surfaces as
`HMul (Matrix (Fin 3) (Fin 2) ℂ) ℕ ?m` followed by a `CStarMatrix.instHMul…`
mismatch. Annotate the unit.

**`rw` closes a goal by `rfl` only at reducible transparency.** Chains that end
in a definitional identity (`matEval y (HprojY j) a b` versus
`matEval y (HprojY (j+1)) (inl a) (inl b)`, or `baseYtrunc j y i` versus
`y (castSucc i)`) need an explicit `rfl` after the `rw`.

**`injection` on `⟨a, k⟩ = ⟨a, k'⟩` gives `k = k'`, not `HEq k k'`,** when the
first components are syntactically equal, so `eq_of_heq` is a type error there.
And do not reach for `simp [hk]`: `lixDD_apply` is a simp lemma, so simp rewrites
the *type* `Fin (lixDD (j+1) …)` to `Fin (2 ^ (j+1))` and the hypothesis no
longer applies.

**`Set.projIcc_left` takes the order proof explicitly**, and its right-hand side
must be ascribed at `unitInterval`: `(0 : ↥(Set.Icc (0:ℝ) 1))` finds no `Zero`
instance, because the instance is stated for `unitInterval` and that def is not
reducible.

**`ring` inside `first` never fails.** Mathlib's `ring` falls back to `ring_nf`
and *succeeds* without closing the goal, so later alternatives are never tried.
Use `ring1`.

**`Fin 3 → ℂ` carries the sup norm.** `‖x‖ = 1` is the wrong condition; state
everything with `dotProduct`. `sum_star_mul_self` is the bridge from
`unitVectors` membership, and `rankOneProj` is already the rank-one primitive.

**A name clash reads as a cascade of type errors.** A clashing `seamCorrection`
produced 27 error lines that all looked like instance-synthesis failures, with
the one informative line first and easy to miss. Check every new name against
the modules you import before the first probe.

**`Continuous.smul` mis-unifies against `continuous_const`**, producing a scalar
action on the *function*. Bind the constant with a `have` first.

**`congrFun` does not elaborate on an equality of `Matrix` values**, because the
type is not syntactically a Pi; `congrFun₂` is the idiom Mathlib itself uses.

**A bare lambda for a `Matrix` value breaks entry-level `simp`.** Matrix apply
lemmas are stated through `Matrix.of`. Use it.

**`clutchingObstruction_of_equiv` was unusable as stated** — its hypotheses were
jointly contradictory. Repaired to take `∀ x, IsClutchDatum (t x) (coneMat Ω (ν x))`.

**The shared scratchpad is shared.** Two lanes wrote `scratchpad/probe1.log` and
truncated each other. Use a lane-specific directory; this lane's probe is
`scratchpad/cs-clutching/ccprobe2.sh`, which ships the changed-file list in a
file rather than on the command line.
