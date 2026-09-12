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
| `LIXCor4PowersAssembly` | witness ũ = Aᴴu, gauge `A(ψ(equatorInv x))`, `Gen.corollary4Powers_of_diag` | COMPILED 0911-230636-19649 (46270ef0c) |
| `LIXCor4PowersDiagChain` | rank-n chain Γ(X₀, End(𝟏ⁿ⊕𝟏ⁿ)) → M₂(A₀); `diagChainN_sectionBlock`; `diagOne_sphereUnitary_mem` | COMPILED 0911-222603-77508 (878b6b5f2) |
| `LIXCor4PowersDiag` | `sectionBlock_genU2_mem` (seamPath in rearranged 𝟏^{n+1}⊕𝟏^{n−1}), `wallBlock_one_mem`, `diagWitnessNullHomotopic`, **`Gen.corollary4Powers n hn : Corollary4Powers n (degreeFamily n)`** | COMPILED 0911-232226-4184 (e60383ad3); all audits classical |

## Cartan groundwork for the odd-primary P^i (09-12, stopped by the LIX wind-down order)
| module | content | status |
|---|---|---|
| `CharClass/OddPWDiagonalRing` | `wdPhi`, `wdQSum`, `wdChain_identity`; reduced coefficients `wdPhi_one_one_even` (1), `wdPhi_one_one_odd_even` (1), `wdPhi_one_one_odd_odd (hp : Odd p) : wdPhi p a b (1 : ZMod p) 1 = 0` | COMPILED, on main |
| `CharClass/OddPWDiagonal` | `psiW p n : GroupRingZMod p →ₗ[ZMod p] WWAll p`; `psiW_chainMap : psiW p n (altCoeff (grS p) (grNorm p) n * x) = wwDAll p (psiW p (n + 1) x)`; `psiW_grGen_mul : psiW p n (grGen p * x) = wwDiagAct p (psiW p n x)` | COMPILED 0912-004039-92791, on main |
| `CharClass/OddPWDiagonalCounit` | `psiW_counitLeft : wwCounitLeft p (psiW p n x) = wdEmb p n x`, `psiW_counitRight` (mirror) | COMPILED 0912-004039-92791, on main |

Residual, NOT authored (no `OddPShuffle*` file exists).  `OddPShuffle` on the flat model of
`OddPTupleD`/`OddPTupleAction`, with x = slots 0..m−1 and y = slots m..2m−1:
* `tupRiffleAll K X m : Module.End K (tupAllMod K X (2 * m))`, x₁…x_m y₁…y_m ↦ x₁y₁…x_my_m with sign
  (−1)^{Σ_{j<m} |y_j| · Σ_{j<l<m} |x_l|}.  Put the sign in from the start: every property except the
  chain-map condition also holds for the unsigned grouping.
* `tupBlockRotAll K X m : Module.End K (tupAllMod K X (2 * m))` rotates each block with sign
  rotExp(x) + rotExp(y), and there is no cross sign.
* `tupRiffleAll_mul_tupDAll : tupRiffleAll K X m * tupDAll K X (2 * m) = tupDAll K X (2 * m) * tupRiffleAll K X m`
* `tupRiffleAll_conj : tupRiffleAll K X m * tupBlockRotAll K X m = tupTAll K X (2 * m) ^ 2 * tupRiffleAll K X m`
* Degree-k twins `tupRiffle K X m k`, `tupBlockRot K X m k` with
  `tupIncl K X (2 * m) k ∘ₗ tupRiffle K X m k = tupRiffleAll K X m ∘ₗ tupIncl K X (2 * m) k`, the
  pattern of `tupIncl_comp_tupT` and `tupT_tupD`.
* Proof templates: `tupT_sign` and `tupTAll_tupDAll_single`.  The sign identity needed is
  pre(t, j) + riffleExp(update t j τ) ≡ riffleExp(t) + pre(riffle t, σ j) (mod 2).
* Model test: `notes/lix-stronger-lane-reports/tools/riffle_test.py` checks R∘D = D∘R and
  R∘B = T²∘R on 4368 tuples (m ≤ 3, degrees ≤ 3) with 0 failures.  The unsigned riffle fails the
  chain-map check, as a control should.
* The Cartan comparison consuming this (OddPCompA/B) belongs to lix-steenrod.

## NEEDS
* Nothing for the arrow.  `ClimbedPowersOutside n` = `Gen.corollary4Powers n hn` applied to Lemma 2 for
  `KGen.bVecK n (k-1)` at every p ∣ n, p ∤ k (Step C / Step D lanes).
* WIRE tops: `GroupApproximation.Analysis.LIXCor4PowersDiag` (reaches all five others).

## TRAPS
* `have h : ∀ m, P (EHmat n m)` with an implicit `dd`: binder type of `m` is a metavariable, so
  `Fintype (VIdx n ?dd)` is stuck.  Annotate `∀ m : CharClass.Gen.baseM n dd`.
* An unused `where`-field binder (`last x :=`) is a lint error; write `_`.
* `rw [a, a]` with the same zero lemma twice fails: `rw` already rewrote every occurrence.
* `(1 : CStarMatrix ..) i j` needs `CStarMatrix.one_apply`, not `Matrix.one_apply`, in `simp`.
* `rw [hr, e1, e2]` with `e1 : 2 * (1/2) = 1`, `e2 : 2 * (1/2) - 1 = 0`: e1 rewrites inside e2's pattern
  first.  Rewrite the longer pattern first.
