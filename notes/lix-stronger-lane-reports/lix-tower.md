# lix-tower — the k-indexed Corollary 4 at rank n (successor of sp-tower)

Clone lix-a (shared with lix-powers, lix-oddside-n).  Owns `Analysis/LIX*` except `LIXPowers*`,
`CharClass/LIXShape*`, and the new `Analysis/LIXCor4Powers*`.

## STEP 0
All 20 sp-tower files, including the 7 generic leaves, were byte-identical on origin/main, so there
was nothing to preserve.  `Gen.equatorEmb/incl/genU2/genSphere` (scope item 1) were already on main
in `Analysis/LIXGenericEquator`.

## Design rulings used
* Family (lead, 21:35): exponent k ↔ the degree-k section `KGen.bVecK n (k − 1)`.  joinC k has degree
  k+1, so `ũ^{k} ≃ ũ ∘ ψ_{k−1}`.
* Sphere (lead): lix-powers' `IsSphereUnitary`, `exists_homotopy_pow_comp_genSphere n hn k`, and the
  ball extension `ballWall` of the wall part (A).

## The chain (all `Analysis/`)
| module | content | status |
|---|---|---|
| `LIXCor4PowersShape` | `Gen.HasSphereShape` for any continuous top block, stable under connect, climb, products, powers; `Gen.sphereUnitary` | COMPILED 0911-215816-84275 |
| `LIXCor4PowersField` | `Gen.exists_unitary_field_of_nullHomotopy_gauged` (gauge g, pullback ξ, seam pointwise on the equator); `equatorInv`, `capTime`, `dirPt`, `extTop` | COMPILED 0911-215816-84275 |
| `LIXCor4PowersStage` | `Gen.climb_pow_notMem_gauged` (concatenated null-homotopy `concatW`), `Gen.lixLimit_pow_notMem` | COMPILED 0911-222130-47938, landed 15fbf0bdc |
| `LIXCor4PowersAssembly` | witness ũ = Aᴴu, gauge `A(ψ(equatorInv x))`, `Gen.corollary4Powers_of_diag` | blocked: lix-powers' `LIXPowersSphere:332` linter red |
| `LIXCor4PowersDiagChain` | rank-n chain Γ(X₀, End(𝟏ⁿ⊕𝟏ⁿ)) → M₂(A₀); `diagChainN_sectionBlock`; `diagOne_sphereUnitary_mem` | COMPILED 0911-222603-77508 (878b6b5f2) |
| `LIXCor4PowersDiag` | `sectionBlock_genU2_mem` (seamPath in rearranged 𝟏^{n+1}⊕𝟏^{n−1}), `wallBlock_one_mem`, `diagWitnessNullHomotopic`, **`Gen.corollary4Powers n hn : Corollary4Powers n (degreeFamily n)`** | authored; waits on Assembly |

## NEEDS
* lix-powers: fix `normGen_eq_ballWall_mul` (`rw [...] <;> rfl` is a linter error).

## TRAPS
* `have h : ∀ m, P (EHmat n m)` with an implicit `dd`: binder type of `m` is a metavariable, so
  `Fintype (VIdx n ?dd)` is stuck.  Annotate `∀ m : CharClass.Gen.baseM n dd`.
* `rw [a, a]` with the same zero lemma twice fails: `rw` already rewrote every occurrence.
* `(1 : CStarMatrix ..) i j` needs `CStarMatrix.one_apply`, not `Matrix.one_apply`, in `simp`.
* `rw [hr, e1, e2]` with `e1 : 2 * (1/2) = 1`, `e2 : 2 * (1/2) - 1 = 0`: e1 rewrites inside e2's pattern
  first.  Rewrite the longer pattern first.
