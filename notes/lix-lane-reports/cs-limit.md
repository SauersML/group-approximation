# Lane `cs-limit`

## 1. GREEN

| module | job count | note |
|---|---|---|
| `Analysis/LIXFiniteStageNullHomotopy` | 2978 | **Lemma 7** verified (one repair, see TRAPS) |
| `Analysis/LIXLimitTower` | 2999 | new: `CStarTower`, `climb`, the algebraic colimit as a pre-C⋆-algebra |
| `Analysis/LIXLimitCompletion` | 2999 | new: `Limit`, `limIota`, `stage`, **persistence** |
| `Analysis/LIXLimitMatrixTransport` | 2999 | new: `M_n(−)` functorial, `diag(u,1)` transport, the witness |
| `Analysis/LIXLimitSeparable` | 2999 | new: separability of the limit (bonus item 4) |

The last four were built together in one probe, `Build completed successfully
(2999 jobs)`, each with its own `Built …` line.

Peer modules that also built clean inside cs-limit probes:
`Analysis/CStarCompletion`, `Analysis/CStarCompletionCoe`,
`Analysis/CStarKOne`, `Analysis/CStarKOneInjectivityCriterion`,
`Analysis/LIXEndpointStatement`.

### What the lane delivers, as Lean signatures

```lean
-- Analysis/LIXLimitTower
structure CStarTower (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)] where
  succHom : ∀ n, A n →⋆ₐ[ℂ] A (n + 1)
  norm_succHom : ∀ n a, ‖succHom n a‖ = ‖a‖
CStarTower.ofInjective : (∀ n, A n →⋆ₐ[ℂ] A (n+1)) → (∀ n, Injective (φ n)) → CStarTower A
T.climb (i k : ℕ) : A k → A i          -- total; no `k ≤ i` proof inside
T.climbHom (h : k ≤ i) : A k →⋆ₐ[ℂ] A i
T.Colim                                 -- pre-C⋆-algebra: Ring, NormedRing, StarRing,
                                        -- NormedStarGroup, CStarRing, Algebra ℂ,
                                        -- NormedAlgebra ℂ, StarModule ℂ, Nontrivial
T.iota (i : ℕ) : A i →⋆ₐ[ℂ] T.Colim     -- isometric, injective
T.iota_climb (h : k ≤ i) : T.iota i (T.climb i k a) = T.iota k a
T.exists_iota : ∀ z, ∃ i a, z = T.iota i a

-- Analysis/LIXLimitCompletion
T.Limit                     -- = UniformSpace.Completion T.Colim; a `CStarAlgebra`,
                            -- `Nontrivial` as soon as `A 0` is
T.limIota (i : ℕ) : A i →⋆ₐ[ℂ] T.Limit         -- isometric, injective
T.limIota_climb (h : k ≤ i) : T.limIota i (T.climb i k a) = T.limIota k a
T.limIota_succHom : T.limIota (i+1) (T.succHom i a) = T.limIota i a   -- ι_{i+1} ∘ φ_i = ι_i
T.stage (i : ℕ) : StarSubalgebra ℂ T.Limit     -- = (T.limIota i).range
T.isClosed_stage, T.stage_mono, T.dense_iUnion_stage
LIX.unitaryHom (f : B →⋆ₐ[ℂ] C) : unitary B →* unitary C   -- continuous
T.notMem_unitaryComponentOne_limit :
  (∀ j (hj : k ≤ j), unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j)) →
    unitaryHom (T.limIota k) u ∉ unitaryComponentOne T.Limit

-- Analysis/LIXLimitMatrixTransport
LIX.matrixHom (n : ℕ) (f : B →⋆ₐ[ℂ] C) : CStarMat n B →⋆ₐ[ℂ] CStarMat n C
LIX.diagOne_mem_unitaryComponentOne_map (f : B →⋆ₐ[ℂ] C) :
  diagOne u ∈ unitaryComponentOne (CStarMat 2 B) →
    diagOne (unitaryHom f u) ∈ unitaryComponentOne (CStarMat 2 C)
T.exists_unitary_witness (u : unitary (A k))
  (hstage : ∀ j (hj : k ≤ j), unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (A j))
  (hdiag : diagOne u ∈ unitaryComponentOne (CStarMat 2 (A k))) :
  ∃ v : unitary T.Limit, v ∉ unitaryComponentOne T.Limit ∧
    diagOne v ∈ unitaryComponentOne (CStarMat 2 T.Limit)

-- Analysis/LIXLimitSeparable
T.separableSpace_colim, T.separableSpace_limit   -- given `∀ n, SeparableSpace (A n)`
```

`T.exists_unitary_witness` is exactly the hypothesis of
`LIXEndpointStatement.not_k1Inj_of_witness`.

## 2. AUTHORED, UNVERIFIED

(none)

## 3. NEEDS

From `cs-stages` (`Analysis/LIXStageAlgebra*`, `Analysis/LIXConnectingMap*`), in the
`STW59` namespace it is already using:

```lean
STW59.StageAlgebra : ℕ → Type                       -- exists, with `CStarAlgebra` instance
instance : Nontrivial (STW59.StageAlgebra 0)
STW59.connect : ∀ i, STW59.StageAlgebra i →⋆ₐ[ℂ] STW59.StageAlgebra (i + 1)
STW59.connect_injective : ∀ i, Function.Injective (STW59.connect i)
```

Then the tower is `CStarTower.ofInjective STW59.connect STW59.connect_injective`, and nothing
else about the stages is used by this lane.  Unitality is free (`→⋆ₐ[ℂ]` is unital by
definition) and isometry is derived from injectivity by `NonUnitalStarAlgHom.norm_map`, so a
separate norm hypothesis is *not* needed.

From `cs-clutching` / `cs-simplicity`, for `T.exists_unitary_witness` at `k = 0`:

```lean
u : unitary (STW59.StageAlgebra 0)
hstage : ∀ j (hj : 0 ≤ j),
  LIX.unitaryHom (T.climbHom hj) u ∉ unitaryComponentOne (STW59.StageAlgebra j)
hdiag  : diagOne u ∈ unitaryComponentOne (CStarMat 2 (STW59.StageAlgebra 0))
```

`T.climbHom hj` is the composite connecting map `φ_{0,j}`; `hstage` is manuscript Corollary 4
plus Lemma 6.

For `cs-endpoint`: `T.exists_unitary_witness`'s `diagOne` is elaborated under the local
instances `LIX.instSpectralPartialOrder` / `LIX.instSpectralStarOrderedRing`, both of which
unfold to `CStarAlgebra.spectralOrder` / `CStarAlgebra.spectralOrderedRing`.  They are therefore
`rfl`-equal to the endpoint file's own local instances, but they are *different constants*, so
composition must go through `exact`/`apply` (defeq), not `rw`.

## 4. TRAPS

* **`ring` is commutative-only.**  `LIXFiniteStageNullHomotopy` closed a noncommutative
  expansion `ey·w − ex·P = ey·(w − P) + (ey − ex)·P` with `ring`, which reports
  `` `ring_nf` made no progress ``.  Fix: `rw [mul_sub, sub_mul]` then `abel`.  This was the
  *only* defect in that file.
* **`CStarTower.mk` collides with the structure constructor.**  A `def mk` in the namespace of
  a `structure` is a duplicate declaration, and the resulting `T.mk` then resolves to the
  constructor with the misleading error "Function `mk` does not have a usable parameter of type
  `CStarTower …`".  The colimit constructor is called `mkAt`, as in
  `Analysis/SequentialGroupColimit`.
* **`AddMonoid.nsmul` / `SubNegMonoid.zsmul` have no default value.**  Building `AddCommGroup`
  with `where add := … ; zero := … ; neg := …` fails with "Fields missing: `nsmul`, `zsmul`";
  supply `nsmul := nsmulRec`, `zsmul := zsmulRec`.  `npow`, `natCast`, `intCast` *do* have
  defaults.
* **A section variable the body never mentions is not a parameter.**  `unAux` does not mention
  `T`, so `T.unAux` is not valid dot notation even though it sits under `variable (T)`.
* **`rw` leaving `0 = T.mkAt 0 0`.**  The trailing `rfl` of `rw` does not unfold the `Zero`
  instance; finish with `exact T.mkAt_zero i` instead of rewriting.
* **The unitary API is `Unitary`, not `unitary`.**  `unitary R` is the subgroup; the lemmas
  live in the capitalised namespace: `Unitary.mem_iff`, `Unitary.map_mem`,
  `Unitary.mem_pathComponentOne_iff`, `Unitary.joined`.  `((1 : unitary R) : R) = 1` is
  `OneMemClass.coe_one`.
* **`Path.cast` takes the *new* endpoint on the left**: `Path.cast (γ : Path a b) (ha : a' = a)
  (hb : b' = b) : Path a' b'`.  The obvious orientation fails with a `show`-pattern mismatch.
* **Do not pipe `ccprobe.sh` through `tail`.**  The script already prints the first 60 error
  lines followed by the last 150 lines of the log; an outer `tail -180` silently drops the
  earliest (and usually causal) errors, which cost one probe cycle here.
* **`ccprobe.sh` argument-list overflow** on the very first sync (every module counts as
  changed).  The lead has rewritten the script to ship the change list as a file; a first probe
  against a fresh clone still costs ~12 min of `cp -al`.
