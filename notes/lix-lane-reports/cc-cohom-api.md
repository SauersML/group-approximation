# cc-cohom-api

Lane of `notes/LIX_FULL_PROGRAM_2026-09-05.md`.  Owns
`GroupApproximation/CharClass/Cohomology*.lean`, namespace
`GroupApproximation.CharClass`.

Everything is the **vendored** mod-2 singular cohomology
(`GroupApproximation/ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/`),
repackaged element-wise.  Spaces are `TopCat.{0}`; `Hmod2 X n` is a
`ModuleCat (ZMod 2)` and is *reducibly* the vendored `cohomologyZMod2 X n`, so a
peer may mix the two vocabularies freely.

## Module map

| module | contents |
|---|---|
| `CohomologyBasic.lean` | `Hmod2`, `cohCast`, `cup` (`⌣`), `one`, `pull`, bilinearity, right unitality, naturality, functoriality |
| `CohomologyAssoc.lean` | degree relabelling of simplices, `cochainCup_assoc`, `cup_assoc`, `one_cup` |
| `CohomologyBridge.lean` | `TopCat.of` plumbing for concrete `Type`s, subspace restriction, products, homotopy invariance, `H^*(X × [0,1])`, `H^*(X × ℝ^k)` |
| `CohomologySphere.lean` | `H^k(S^n; F₂)`: vanishing range, top-degree generator, `H^0` of a path-connected space |
| `CohomologyContractible.lean` | `H^k(pt) = 0` for `k ≥ 1`, hence `H^k(Y) = 0` for contractible `Y`, and `H^0(Y) ≃ₗ F₂` |
| `CohomologySphereComplement.lean` | `S^n ∖ {p}` is contractible (stereographic projection) and its cohomology |
| `CohomologyMayerVietoris.lean` | the cochain-level Mayer–Vietoris short exact sequence, `δ`, exactness, the connecting isomorphism |

## Exported signatures (stable; build against these)

```lean
namespace GroupApproximation.CharClass

abbrev Hmod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2)   -- = cohomologyZMod2 X n

def cohCast {X : TopCat.{0}} {m m' : ℕ} (h : m = m') (a : Hmod2 X m) : Hmod2 X m'
def cup {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) : Hmod2 X (p + q)
scoped infixl:70 " ⌣ " => cup
def one (X : TopCat.{0}) : Hmod2 X 0
def pull {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) (a : Hmod2 Y n) : Hmod2 X n
def pullLinear {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) : Hmod2 Y n →ₗ[ZMod 2] Hmod2 X n
def cupBilin (X : TopCat.{0}) (p q : ℕ) :
    Hmod2 X p →ₗ[ZMod 2] Hmod2 X q →ₗ[ZMod 2] Hmod2 X (p + q)

theorem exists_cocycle (a : Hmod2 X n) : ∃ φ hφ, cocycleClass X n φ hφ = a
theorem cup_mk       -- class of a cocycle ⌣ class of a cocycle = class of cochainCup
theorem cup_add_left / cup_add_right / cup_smul_left / cup_smul_right / zero_cup / cup_zero
theorem cup_one (a : Hmod2 X p) : cup a (one X) = a            -- STRICT, no cast
theorem one_cup (a : Hmod2 X p) : cup (one X) a = cohCast (Nat.zero_add p).symm a
theorem cup_assoc (a b c) :
    cup (cup a b) c = cohCast (Nat.add_assoc p q r).symm (cup a (cup b c))
theorem pull_id / pull_comp / pull_add / pull_zero / pull_smul / pull_congr / pull_mk
theorem pull_cup (f) (a b) : pull f (p+q) (cup a b) = cup (pull f p a) (pull f q b)
theorem pull_one (f) : pull f 0 (one Y) = one X
theorem cohCast_rfl / cohCast_cohCast / cohCast_add / cohCast_zero / cohCast_smul
theorem cohCast_injective / cohCast_eq_zero_iff / cohCast_eq_iff / cohCast_cocycleClass

-- cochain-level associativity machinery (CohomologyAssoc.lean)
def degHom {m m' : ℕ} (h : m = m') : (⦋m⦌ : SimplexCategory) ⟶ ⦋m'⦌
def simplexRelabel (X) (h : m = m') (σ : singularSimplices X m') : singularSimplices X m
theorem cochainCast_eval (h) (φ) (σ) :
    cochainEval m' (cochainCast h φ) σ = cochainEval m φ (simplexRelabel X h σ)
theorem cochainCup_assoc / cochainCup_one_left
theorem sset_map_comp -- restricting along two composable simplex maps

-- bridge (CohomologyBridge.lean)
abbrev cmap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    TopCat.of X ⟶ TopCat.of Y
def pullMap (f : C(X, Y)) (n : ℕ) : Hmod2 (TopCat.of Y) n → Hmod2 (TopCat.of X) n
theorem pull_eq_of_homotopic / pull_eq_of_homotopy / pullMap_eq_of_homotopic
def pullEquivOfHomotopyEquiv (e : X ≃ₕ Y) (n) : Hmod2 (of Y) n ≃ₗ[ZMod 2] Hmod2 (of X) n
def pullEquivOfHomeomorph (e : X ≃ₜ Y) (n) : Hmod2 (of Y) n ≃ₗ[ZMod 2] Hmod2 (of X) n
def pullEquivOfIso {X Y : TopCat.{0}} (e : X ≅ Y) (n) : Hmod2 Y n ≃ₗ[ZMod 2] Hmod2 X n
def inclSubtype (S : Set X) : TopCat.of S ⟶ TopCat.of X
def restrictTo (S : Set X) (n) : Hmod2 (of X) n → Hmod2 (of S) n
  -- with restrictTo_add / restrictTo_zero / restrictTo_cup / restrictTo_one
abbrev fstMap / sndMap / prodMap
instance contractibleSpace_unitInterval : ContractibleSpace unitInterval
def prodContractibleEquiv (X C) [ContractibleSpace C] : (X × C) ≃ₕ X
theorem prodContractibleEquiv_toFun : (prodContractibleEquiv X C).toFun = ContinuousMap.fst
def cohProdContractible (X C) [ContractibleSpace C] (n) :
    Hmod2 (of X) n ≃ₗ[ZMod 2] Hmod2 (of (X × C)) n         -- = pull (fstMap X C) n
def cohProdUnitInterval (X) (n) / cohProdEuclidean (X) (k n)

-- spheres (CohomologySphere.lean); Sphere n is the vendored model in ℝ^{n+1}
theorem sphereCohomology_eq (n k) : sphereCohomology n k = Hmod2 (TopCat.of (Sphere n)) k
theorem sphere_coh_isZero_of_gt / sphere_coh_isZero_of_lt / sphere_coh_isZero_of_ne
theorem sphere_coh_eq_zero_of_ne (n k) (k ≠ 0) (k ≠ n) (a) : a = 0
theorem sphere_coh_top_finrank (n) (1 ≤ n) : finrank (ZMod 2) (Hmod2 (of (Sphere n)) n) = 1
def sphereTopEquiv (n) (hn) : Hmod2 (of (Sphere n)) n ≃ₗ[ZMod 2] ZMod 2
def sphereTopClass (n) (hn) : Hmod2 (of (Sphere n)) n
theorem sphereTopClass_ne_zero / sphere_coh_top_eq_smul
theorem cohZero_finrank (X) [Nonempty X] [PathConnectedSpace X] : finrank (Hmod2 X 0) = 1
def cohZeroEquiv (X) [Nonempty X] [PathConnectedSpace X] : Hmod2 X 0 ≃ₗ[ZMod 2] ZMod 2
theorem sphere_pathConnectedSpace (n) (1 ≤ n) / sphere_nonempty
def sphereCohZeroEquiv (n) (hn) : Hmod2 (of (Sphere n)) 0 ≃ₗ[ZMod 2] ZMod 2

-- contractible (CohomologyContractible.lean)
theorem cohomology_unit_isZero (k) (1 ≤ k) : IsZero (Hmod2 (TopCat.of Unit) k)
theorem cohomology_isZero_of_contractible (Y) [ContractibleSpace Y] (k) (1 ≤ k) :
    IsZero (Hmod2 (TopCat.of Y) k)
theorem cohomology_eq_zero_of_contractible / nonempty_of_contractible
def cohZeroEquivOfContractible (Y) [ContractibleSpace Y] : Hmod2 (of Y) 0 ≃ₗ[ZMod 2] ZMod 2

-- punctured sphere (CohomologySphereComplement.lean)
def spherePunctureHomeo (hv : ‖v‖ = 1) : ↥((stereographic hv).source) ≃ₜ ((ℝ ∙ v)ᗮ)
theorem contractibleSpace_sphere_compl (n) (p : Sphere n) :
    ContractibleSpace ↥({p}ᶜ : Set (Sphere n))
theorem sphere_compl_cohomology_isZero (n) (p) (k) (1 ≤ k) :
    IsZero (Hmod2 (TopCat.of ↥({p}ᶜ : Set (Sphere n))) k)
def sphere_compl_cohZeroEquiv (n) (p) : Hmod2 (of ↥({p}ᶜ)) 0 ≃ₗ[ZMod 2] ZMod 2

-- Mayer–Vietoris (CohomologyMayerVietoris.lean), for U V : Opens X, hUV : U ⊔ V = ⊤
abbrev dualCxFunctor : (ChainComplex (ModuleCat (ZMod 2)) ℕ)ᵒᵖ ⥤ CochainComplex (ModuleCat (ZMod 2)) ℕ
def mvCoSC (U V) (hUV) : ShortComplex (CochainComplex (ModuleCat (ZMod 2)) ℕ)
def mvCoSplitting (U V) (hUV) (k) : (eval k of mvCoSC).Splitting
theorem mvCoSC_shortExact (U V) (hUV) : (mvCoSC U V hUV).ShortExact
def subCxDualIso (S : Set X) :
    dualCx (ZMod 2) (subChainComplex (ZMod 2) X S) ≅ cochainCxZMod2 (TopCat.of S)
def subCxDualHomologyIso (S) (n) / mvInterIso (U V) (hUV) (n) / mvAmbientIso (U V) (hUV) (n)
def mvDelta (U V) (hUV) (n) :
    Hmod2 (TopCat.of ((U : Set X) ∩ (V : Set X))) n ⟶ Hmod2 X (n + 1)
theorem mvExact_inter / mvExact_sum / mvExact_ambient
theorem isZero_mvCoX2 (U V) (hUV) (n) (hU) (hV) : IsZero ((mvCoSC U V hUV).X₂.homology n)
def mvConnectingIso (U V) (hUV) (n) (hUn) (hVn) (hUn') (hVn') :
    Hmod2 (TopCat.of ((U : Set X) ∩ (V : Set X))) n ≅ Hmod2 X (n + 1)

end GroupApproximation.CharClass
```

## 1. GREEN

Probe: `ccprobe.sh cc-cohom-api …`, `Build completed successfully (8769 jobs)`
on the run that built `CohomologyAssoc` and `CohomologyContractible`; the earlier
`CohomologyBasic`/`CohomologyBridge` run was 8767 jobs and the
`CohomologySphere` run 8769.

* `GroupApproximation/CharClass/CohomologyBasic.lean` (8767)
* `GroupApproximation/CharClass/CohomologyBridge.lean` (8767)
* `GroupApproximation/CharClass/CohomologySphere.lean` (8769)
* `GroupApproximation/CharClass/CohomologyAssoc.lean` (8769)
* `GroupApproximation/CharClass/CohomologyContractible.lean` (8769)

## 2. AUTHORED, UNVERIFIED

* `GroupApproximation/CharClass/CohomologySphereComplement.lean` — one error fixed
  since the last probe (`congr 1` already closed the goal), reprobe in flight.
* `GroupApproximation/CharClass/CohomologyMayerVietoris.lean` — first probe in
  flight.  It imports `cc-relative`'s `CharClass/RelativeDual.lean`, which was
  itself landed as *authored, unverified*; if that module is red, this one cannot
  be green either, and the lead should sequence `cc-relative` first.

## 3. NEEDS

* **`cc-cartan`: graded commutativity.**  The vendored Alexander–Whitney cup
  product is not commutative on the nose and the vendored tree has **no** chain
  homotopy between the AW diagonal and its transpose, so this lane does **not**
  provide `cup_comm`.  It needs the ℤ/2-equivariant acyclic-models theorem.
  Until it lands, state downstream lemmas for classes pulled back from
  *different* factors of a product, where the commutation follows from naturality
  alone.  Signature wanted:

  ```lean
  theorem cup_comm {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
      cup a b = cohCast (Nat.add_comm q p) (cup b a)
  ```

  Consequence for `cc-projective`: `ChernRelation.lean` wants a **`CommRing`**
  (`PowerBasis`), and `⨁ n, Hmod2 X n` cannot be given one before `cup_comm`.
  The non-commutative graded structure (`DirectSum.GSemiring`) is derivable from
  `cup_assoc` / `cup_one` / `one_cup` as they stand; say the word and this lane
  will add it.

* **Not yet delivered by this lane** (deliverable 4 of the roster):

  * the `H^*(X)`-linearity of the connecting map,
    `δ (a ⌣ b|_{U ⊓ V}) = δ a ⌣ b` for a global `b`.  `mvDelta` is currently
    produced by Mathlib's `ShortComplex.ShortExact.δ`, which is abstract; the
    linearity is a cochain-level statement about the explicit
    "`δα_U` on `U`, `δα_V` on `V`" representative and needs `δ` re-derived by
    hand from `mvCoSC`.
  * Künneth with spheres, `H^k(X × S^n) ≅ H^k(X) ⊕ H^{k-n}(X)` via `pr₁^*` and
    `(-) ⌣ pr₂^* σ_n`, natural in `X`.  The Mayer–Vietoris input it needs
    (`mvConnectingIso` on the two hemispheres) is now in place; what is missing
    is the two-hemisphere cover of `X × S^n` and the induction.
  * the middle term of Mayer–Vietoris as an explicit direct sum
    `H^n(U) ⊕ H^n(V)`.  Only the vanishing form `isZero_mvCoX2` is provided,
    which is what the connecting-isomorphism computations use.

## 4. TRAPS

* The `⦋n⦌` simplex notation is **scoped in the `Simplicial` locale**.  Without
  `open Simplicial` the parse error is a bare `expected token`, and every
  subsequent tactic in the file is reported as `'…' tactic does nothing` by the
  unused-tactic linter — which, under `-DwarningAsError=true`, buries the real
  error under forty spurious ones.  Read the *first* error, not the loudest.
* `ccprobe.sh` prints only `grep '^error' | head -60` plus `tail -n CC_TAIL`.
  With many errors the first (real) one can be off the end of the tail; raise
  `CC_TAIL` rather than guessing.
* `CategoryTheory.FunctorToTypes.map_id_apply` and `…map_comp_apply` are
  **deprecated** at this pin in favour of `CategoryTheory.Functor.map_id_apply`
  and `…Functor.map_comp_apply`; a deprecation is an error here.
* The vendored `CohomologyCupProduct.lean` **already** carries the
  cohomology-level product `cupZMod2`, the unit `oneZMod2`, `cupZMod2_mk`,
  `cohPullback` and `cohPullback_cupZMod2`.  Do not re-derive the descent; only
  bilinearity, associativity and unitality were missing.
* The vendored **Mayer–Vietoris is homological** (`mvShortExact`, `mvHomologyIso`
  over `ChainComplex (ModuleCat R) ℕ`).  The cohomology version in this lane is
  the `Hom(-, F₂)`-dual of it; that dualization is exact only because
  `cc-relative`'s `dualFunctorZMod2_preservesHomology` says so, and it is cheap
  only because the vendored `mvSplitting` gives an explicit **degreewise
  splitting** — a split short exact sequence survives any additive functor.
* `H^0(X; F₂)` for a path-connected `X` goes through the *general-coefficient*
  augmentation `H0Gen.H0aug`, in the sub-namespace `H0Gen` of
  `SingularH0General.lean`.  The unqualified `H0aug` in scope is the **integral**
  one from `SingularH0PathConnected.lean` and takes a `TopCat` where you expect a
  ring.
* `p + 0` reduces to `p` but `0 + p` does not, and `p + q + r` is not
  definitionally `p + (q + r)`.  Right unitality is therefore free; left
  unitality and associativity need `cohCast`.
* `Subspace.dual_finrank_eq` plus the vendored `kroneckerEquiv` is the cheap
  route to "this cohomology group is one dimensional": compute the *homology*
  rank and dualize, exactly as `SphereTopCohomologyRankOne.lean` does.
