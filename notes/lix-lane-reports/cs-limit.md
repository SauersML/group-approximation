# Lane `cs-limit`

## 1. GREEN

| module | job count | note |
|---|---|---|
| `Analysis/LIXFiniteStageNullHomotopy` | 2978 | **Lemma 7** verified (one repair, see TRAPS) |
| `Analysis/LIXLimitTower` | 2978 | new: `CStarTower`, `climb`, the algebraic colimit as a pre-C⋆-algebra |

`Analysis/CStarCompletionCoe` (and hence `Analysis/CStarCompletion`) also built
clean in a cs-limit probe, so `CStarCompletion.completionCStarAlgebra`,
`coeStarAlgHom`, `norm_coeStarAlgHom`, `denseRange_coeStarAlgHom` are usable.

## 2. AUTHORED, UNVERIFIED

(none yet — `Analysis/LIXLimitCompletion` in progress)

## 3. NEEDS

From `cs-stages` (`Analysis/LIXStageAlgebra*`, `Analysis/LIXConnectingMap*`):

```lean
A : ℕ → Type          -- the stage algebras
instance : ∀ i, CStarAlgebra (A i)
instance : Nontrivial (A 0)
φ : ∀ i, A i →⋆ₐ[ℂ] A (i + 1)
hφ : ∀ i, Function.Injective (φ i)
```

Then `GroupApproximation.LIX.CStarTower.ofInjective φ hφ : CStarTower A` is the
only input this lane needs; everything downstream is a field or theorem of that
tower.  Unitality is free (`→⋆ₐ[ℂ]` is a unital hom) and isometry is derived from
injectivity by `NonUnitalStarAlgHom.norm_map`.

## 4. TRAPS

* **`ring` is commutative-only.**  `LIXFiniteStageNullHomotopy` closed a
  noncommutative expansion `ey·w − ex·P = ey·(w − P) + (ey − ex)·P` with `ring`,
  which reports `` `ring_nf` made no progress ``.  Fix: `rw [mul_sub, sub_mul]`
  then `abel`.  This was the *only* defect in that file.
* **`CStarTower.mk` collides with the structure constructor.**  A `def mk` in the
  namespace of a `structure` shadows nothing — it is a duplicate declaration, and
  the resulting `T.mk` resolves to the constructor with the misleading error
  "Function `mk` does not have a usable parameter of type `CStarTower …`".
  The colimit constructor is therefore called `mkAt` (as in
  `Analysis/SequentialGroupColimit`).
* **`AddMonoid.nsmul` / `SubNegMonoid.zsmul` have no default value.**  Building
  `AddCommGroup` with `where add := … ; zero := … ; neg := …` fails with
  "Fields missing: `nsmul`, `zsmul`"; supply `nsmul := nsmulRec`,
  `zsmul := zsmulRec`.  `npow`, `natCast`, `intCast` *do* have defaults.
* **A section variable that the body never mentions is not a parameter.**
  `unAux` does not mention `T`, so `T.unAux` is not valid dot notation even
  though it sits under `variable (T)`.  Written as plain `unAux`.
* **`rw` leaving `0 = T.mkAt 0 0`.**  The trailing `rfl` of `rw` does not unfold
  the `Zero` instance; finish with `exact T.mkAt_zero i` instead of rewriting.
* **`ccprobe.sh` argument-list overflow** on the very first sync (every module
  counts as changed).  The lead rewrote the script to ship the change list as a
  file; a first probe against a fresh clone still costs ~12 min of `cp -al`.
