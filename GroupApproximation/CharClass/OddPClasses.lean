import GroupApproximation.CharClass.KroneckerContractible
import GroupApproximation.CharClass.SteenrodCochain
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Natural cocycle operations descend to cohomology

The reduced powers `P^i` at an odd prime are built from the cochain operations `D_j` of
`OddPCochain.lean`.  Passing from `D_j` to cohomology uses exactly two of its properties:
it commutes with pullback along every continuous map, and it carries cocycles to cocycles.
It uses neither additivity nor linearity, which matters because `D_j` is a `p`-th power.

This file does the passage once, for any such operation, over any commutative ring.

* `exists_eq_add_coboundary_of_cocycleClassK_eq`, `eq_of_cocycleClassK_eq_deg_zero`: two
  cocycles with the same class differ by a coboundary, and in degree `0` they are equal.
* `NaturalCocycleOp`: an operation on the cochains of every space that is natural and
  carries cocycles to cocycles.
* `NaturalCocycleOp.class_add_coboundary`: the class of the output does not see a coboundary
  change of the input.  The proof is a cylinder.  On `X × [0,1]` the cocycle `pr^* u + δV`,
  where `V` is `w` on the slices at height `1` and `0` on every other simplex, restricts to
  `u` at height `0` and to `u + δw` at height `1`.  The two slices are homotopic, so they
  have the same pullback on cohomology.
* `NaturalCocycleOp.classMap`, `classMap_mk`, `classMap_natural`: the induced map on
  cohomology, its value on the class of any cocycle representative, and its naturality.
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

/-! ## 1. Exactness: equal classes differ by a coboundary -/

/-- **Two cocycles with the same class differ by a coboundary** (positive degree, any
commutative ring).  The homology object is the cokernel of `C^m → Z^{m+1}`, so the difference of
the two cycles lies in the range of that map. -/
theorem exists_eq_add_coboundary_of_cocycleClassK_eq (K : Type) [CommRing K] (X : TopCat.{0})
    (m : ℕ) {φ ψ : singularCochainGroup K X (m + 1)}
    (hφ : cochainCoboundary K X (m + 1) φ = 0) (hψ : cochainCoboundary K X (m + 1) ψ = 0)
    (h : cocycleClassK K X (m + 1) φ hφ = cocycleClassK K X (m + 1) ψ hψ) :
    ∃ w : singularCochainGroup K X m, φ = ψ + cochainCoboundary K X m w := by
  have hc : ((cochainCxK K X).homologyπ (m + 1)).hom
      ((cochainCxK K X).cyclesMk φ (m + 1 + 1) (by simp [ComplexShape.next]) hφ
        - (cochainCxK K X).cyclesMk ψ (m + 1 + 1) (by simp [ComplexShape.next]) hψ) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr h
  have hex : (ShortComplex.mk ((cochainCxK K X).toCycles m (m + 1))
      ((cochainCxK K X).homologyπ (m + 1))
      ((cochainCxK K X).toCycles_comp_homologyπ m (m + 1))).Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      ((cochainCxK K X).homologyIsCokernel m (m + 1) (CochainComplex.prev_nat_succ m))
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex _ hc
  have hi : ((cochainCxK K X).iCycles (m + 1)).hom (((cochainCxK K X).toCycles m (m + 1)).hom w)
      = ((cochainCxK K X).iCycles (m + 1)).hom
          ((cochainCxK K X).cyclesMk φ (m + 1 + 1) (by simp [ComplexShape.next]) hφ
            - (cochainCxK K X).cyclesMk ψ (m + 1 + 1) (by simp [ComplexShape.next]) hψ) :=
    congrArg ((cochainCxK K X).iCycles (m + 1)).hom hw
  rw [← ModuleCat.comp_apply, HomologicalComplex.toCycles_i, map_sub, iCycles_cyclesMkK,
    iCycles_cyclesMkK] at hi
  have hδ : cochainCoboundary K X m w = φ - ψ := hi
  exact ⟨w, by rw [hδ]; abel⟩

/-- **In degree `0` two cocycles with the same class are equal**: nothing maps into `C^0`, so
`homologyπ` is an isomorphism there. -/
theorem eq_of_cocycleClassK_eq_deg_zero (K : Type) [CommRing K] (X : TopCat.{0})
    {φ ψ : singularCochainGroup K X 0}
    (hφ : cochainCoboundary K X 0 φ = 0) (hψ : cochainCoboundary K X 0 ψ = 0)
    (h : cocycleClassK K X 0 φ hφ = cocycleClassK K X 0 ψ hψ) : φ = ψ := by
  have hinj : Function.Injective ((cochainCxK K X).homologyπ 0).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h2 := congrArg ((cochainCxK K X).iCycles 0).hom (hinj h)
  rwa [iCycles_cyclesMkK, iCycles_cyclesMkK] at h2

/-- A cocycle plus a coboundary is a cocycle. -/
theorem cochainCoboundary_add_coboundary_eq_zero {K : Type} [CommRing K] {X : TopCat.{0}}
    (m : ℕ) (u : singularCochainGroup K X (m + 1)) (hu : cochainCoboundary K X (m + 1) u = 0)
    (w : singularCochainGroup K X m) :
    cochainCoboundary K X (m + 1) (u + cochainCoboundary K X m w) = 0 := by
  have hadd : cochainCoboundary K X (m + 1) (u + cochainCoboundary K X m w)
      = cochainCoboundary K X (m + 1) u
        + cochainCoboundary K X (m + 1) (cochainCoboundary K X m w) := by
    unfold cochainCoboundary
    exact map_add _ _ _
  rw [hadd, hu, cochainCoboundary_cochainCoboundaryK, add_zero]

/-! ## 2. The cylinder -/

/-- The cylinder `X × [0,1]`. -/
abbrev oddCyl (X : TopCat.{0}) : TopCat.{0} := TopCat.of (X × unitInterval)

/-- The projection of the cylinder onto its base. -/
def oddCylPr (X : TopCat.{0}) : oddCyl X ⟶ X :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The slice of the cylinder at height `t`. -/
def oddCylIncl (X : TopCat.{0}) (t : unitInterval) : X ⟶ oddCyl X :=
  TopCat.ofHom ⟨fun x => (x, t), continuous_id.prodMk continuous_const⟩

/-- The two end slices of the cylinder are homotopic. -/
def oddCylHomotopy (X : TopCat.{0}) :
    ContinuousMap.Homotopy (oddCylIncl X 0).hom (oddCylIncl X 1).hom where
  toFun q := (q.2, q.1)
  continuous_toFun := continuous_snd.prodMk continuous_fst
  map_zero_left _ := rfl
  map_one_left _ := rfl

/-- Pushing a singular simplex forward along a map is postcomposition. -/
theorem toSSetObjEquiv_map_app_eq_comp {X Y : TopCat.{0}} (f : X ⟶ Y) (m : ℕ)
    (σ : singularSimplices X m) :
    Y.toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)) ((TopCat.toSSet.map f).app _ σ)
      = f.hom.comp (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)) σ) :=
  rfl

/-- A slice followed by the projection is the identity on simplices. -/
theorem oddCylPr_app_oddCylIncl_app (X : TopCat.{0}) (t : unitInterval) (m : ℕ)
    (σ : singularSimplices X m) :
    (TopCat.toSSet.map (oddCylPr X)).app _ ((TopCat.toSSet.map (oddCylIncl X t)).app _ σ) = σ := by
  apply (X.toSSetObjEquiv (Opposite.op (SimplexCategory.mk m))).injective
  rw [toSSetObjEquiv_map_app_eq_comp, toSSetObjEquiv_map_app_eq_comp]
  rfl

/-- A simplex in the slice at height `0` is not a simplex in the slice at height `1`. -/
theorem oddCylIncl_zero_app_ne (X : TopCat.{0}) (m : ℕ) (σ : singularSimplices X m) :
    (TopCat.toSSet.map (oddCylIncl X 0)).app _ σ
      ≠ (TopCat.toSSet.map (oddCylIncl X 1)).app _ σ := by
  intro h
  obtain ⟨z⟩ : Nonempty (stdSimplex ℝ (Fin (m + 1))) := inferInstance
  have h2 := congrArg
    (fun s => ((oddCyl X).toSSetObjEquiv (Opposite.op (SimplexCategory.mk m)) s z).2) h
  have h3 : ((0 : unitInterval) : ℝ) = ((1 : unitInterval) : ℝ) := congrArg Subtype.val h2
  norm_num at h3

/-- The pullback along a slice of a cochain pulled back from the base is that cochain. -/
theorem cochainPullback_oddCylIncl_oddCylPr {K : Type} [CommRing K] (X : TopCat.{0})
    (t : unitInterval) (n : ℕ) (φ : singularCochainGroup K X n) :
    cochainPullback (oddCylIncl X t) n (cochainPullback (oddCylPr X) n φ) = φ := by
  apply cochain_ext
  intro τ
  rw [cochainPullback_eval, cochainPullback_eval, oddCylPr_app_oddCylIncl_app]

open Classical in
/-- **The cylinder cochain** of `w`: the value of `w` on the projection of a simplex that lies in
the slice at height `1`, and `0` on every other simplex.  It is not continuous in any sense, and
it does not need to be: cochains are arbitrary functions on simplices. -/
def oddCylCochain {K : Type} [CommRing K] {X : TopCat.{0}} (m : ℕ)
    (w : singularCochainGroup K X m) : singularCochainGroup K (oddCyl X) m :=
  cochainOfFun m fun σ =>
    if σ = (TopCat.toSSet.map (oddCylIncl X 1)).app _ ((TopCat.toSSet.map (oddCylPr X)).app _ σ)
    then cochainEval m w ((TopCat.toSSet.map (oddCylPr X)).app _ σ) else 0

theorem cochainPullback_oddCylIncl_one_oddCylCochain {K : Type} [CommRing K] {X : TopCat.{0}}
    (m : ℕ) (w : singularCochainGroup K X m) :
    cochainPullback (oddCylIncl X 1) m (oddCylCochain m w) = w := by
  apply cochain_ext
  intro τ
  rw [cochainPullback_eval, oddCylCochain, cochainEval_cochainOfFun, oddCylPr_app_oddCylIncl_app,
    if_pos rfl]

theorem cochainPullback_oddCylIncl_zero_oddCylCochain {K : Type} [CommRing K] {X : TopCat.{0}}
    (m : ℕ) (w : singularCochainGroup K X m) :
    cochainPullback (oddCylIncl X 0) m (oddCylCochain m w) = 0 := by
  apply cochain_ext
  intro τ
  rw [cochainPullback_eval, oddCylCochain, cochainEval_cochainOfFun, oddCylPr_app_oddCylIncl_app,
    if_neg (oddCylIncl_zero_app_ne X m τ), cochainEval_zero]

/-! ## 3. Natural cocycle operations -/

/-- **A natural cocycle operation** from degree `q` to degree `N` over `K`: a function on the
`q`-cochains of every space, commuting with pullback along every continuous map, and carrying
cocycles to cocycles.  No additivity is asked. -/
structure NaturalCocycleOp (K : Type) [CommRing K] (q N : ℕ) where
  /-- The operation on the cochains of a space. -/
  op : ∀ X : TopCat.{0}, singularCochainGroup K X q → singularCochainGroup K X N
  /-- Naturality in the space. -/
  natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) (u : singularCochainGroup K Y q),
    cochainPullback f N (op Y u) = op X (cochainPullback f q u)
  /-- Cocycles go to cocycles. -/
  cocycle : ∀ (X : TopCat.{0}) (u : singularCochainGroup K X q),
    cochainCoboundary K X q u = 0 → cochainCoboundary K X N (op X u) = 0

/-- **A coboundary change of the input does not change the class of the output.** -/
theorem NaturalCocycleOp.class_add_coboundary {K : Type} [CommRing K] {m N : ℕ}
    (O : NaturalCocycleOp K (m + 1) N) (X : TopCat.{0})
    (u : singularCochainGroup K X (m + 1)) (hu : cochainCoboundary K X (m + 1) u = 0)
    (w : singularCochainGroup K X m) :
    cocycleClassK K X N (O.op X (u + cochainCoboundary K X m w))
        (O.cocycle X _ (cochainCoboundary_add_coboundary_eq_zero m u hu w))
      = cocycleClassK K X N (O.op X u) (O.cocycle X u hu) := by
  obtain ⟨U, hUdef⟩ : ∃ U : singularCochainGroup K (oddCyl X) (m + 1),
      U = cochainPullback (oddCylPr X) (m + 1) u
        + cochainCoboundary K (oddCyl X) m (oddCylCochain m w) := ⟨_, rfl⟩
  have hU : cochainCoboundary K (oddCyl X) (m + 1) U = 0 := by
    have hadd : ∀ a b : singularCochainGroup K (oddCyl X) (m + 1),
        cochainCoboundary K (oddCyl X) (m + 1) (a + b)
          = cochainCoboundary K (oddCyl X) (m + 1) a
            + cochainCoboundary K (oddCyl X) (m + 1) b := by
      intro a b
      unfold cochainCoboundary
      exact map_add _ _ _
    rw [hUdef, hadd, cochainPullback_cochainCoboundaryK, hu, cochainCoboundary_cochainCoboundaryK,
      add_zero]
    unfold cochainPullback
    exact map_zero _
  have hpadd : ∀ (t : unitInterval) (a b : singularCochainGroup K (oddCyl X) (m + 1)),
      cochainPullback (oddCylIncl X t) (m + 1) (a + b)
        = cochainPullback (oddCylIncl X t) (m + 1) a
          + cochainPullback (oddCylIncl X t) (m + 1) b := by
    intro t a b
    unfold cochainPullback
    exact map_add _ _ _
  have hz : cochainCoboundary K X m (0 : singularCochainGroup K X m) = 0 := by
    unfold cochainCoboundary
    exact map_zero _
  have h0 : cochainPullback (oddCylIncl X 0) (m + 1) U = u := by
    rw [hUdef, hpadd, cochainPullback_oddCylIncl_oddCylPr, ← cochainPullback_cochainCoboundaryK,
      cochainPullback_oddCylIncl_zero_oddCylCochain, hz, add_zero]
  have h1 : cochainPullback (oddCylIncl X 1) (m + 1) U = u + cochainCoboundary K X m w := by
    rw [hUdef, hpadd, cochainPullback_oddCylIncl_oddCylPr, ← cochainPullback_cochainCoboundaryK,
      cochainPullback_oddCylIncl_one_oddCylCochain]
  have hOU := O.cocycle (oddCyl X) U hU
  have key := pull_eq_of_homotopyOf K (oddCylHomotopy X) N
    (cocycleClassK K (oddCyl X) N (O.op (oddCyl X) U) hOU)
  rw [pull_eq_cohPullback, pull_eq_cohPullback, cohPullbackK_cocycleClassK,
    cohPullbackK_cocycleClassK] at key
  calc cocycleClassK K X N (O.op X (u + cochainCoboundary K X m w))
          (O.cocycle X _ (cochainCoboundary_add_coboundary_eq_zero m u hu w))
        = cocycleClassK K X N (cochainPullback (oddCylIncl X 1) N (O.op (oddCyl X) U))
            (cochainPullback_cocycleK K (oddCylIncl X 1) N _ hOU) :=
          cocycleClassK_congr K X N (by rw [O.natural, h1]) _ _
      _ = cocycleClassK K X N (cochainPullback (oddCylIncl X 0) N (O.op (oddCyl X) U))
            (cochainPullback_cocycleK K (oddCylIncl X 0) N _ hOU) := key.symm
      _ = cocycleClassK K X N (O.op X u) (O.cocycle X u hu) :=
          cocycleClassK_congr K X N (by rw [O.natural, h0]) _ _

/-- **The induced map on cohomology**: the class of the operation applied to the chosen cocycle
representative. -/
def NaturalCocycleOp.classMap {K : Type} [CommRing K] {q N : ℕ} (O : NaturalCocycleOp K q N)
    (X : TopCat.{0}) (x : Hmod K X q) : Hmod K X N :=
  cocycleClassK K X N (O.op X (classReprK K X q x)) (O.cocycle X _ (classReprK_isCocycle K X q x))

/-- **The computation rule**: on the class of any cocycle, the induced map is the class of the
operation applied to that cocycle. -/
theorem NaturalCocycleOp.classMap_mk {K : Type} [CommRing K] {q N : ℕ}
    (O : NaturalCocycleOp K q N) (X : TopCat.{0}) (u : singularCochainGroup K X q)
    (hu : cochainCoboundary K X q u = 0) :
    O.classMap X (cocycleClassK K X q u hu) = cocycleClassK K X N (O.op X u) (O.cocycle X u hu) := by
  unfold NaturalCocycleOp.classMap
  cases q with
  | zero =>
    exact cocycleClassK_congr K X N (congrArg (O.op X)
      (eq_of_cocycleClassK_eq_deg_zero K X (classReprK_isCocycle K X 0 _) hu
        (cocycleClassK_classReprK K X 0 _))) _ _
  | succ m =>
    obtain ⟨w, hw⟩ := exists_eq_add_coboundary_of_cocycleClassK_eq K X m
      (classReprK_isCocycle K X (m + 1) _) hu (cocycleClassK_classReprK K X (m + 1) _)
    exact (cocycleClassK_congr K X N (congrArg (O.op X) hw) _ _).trans
      (O.class_add_coboundary X u hu w)

/-- **Naturality of the induced map.** -/
theorem NaturalCocycleOp.classMap_natural {K : Type} [CommRing K] {q N : ℕ}
    (O : NaturalCocycleOp K q N) {X Y : TopCat.{0}} (f : X ⟶ Y) (x : Hmod K Y q) :
    pull f N (O.classMap Y x) = O.classMap X (pull f q x) := by
  obtain ⟨u, hu, rfl⟩ := cocycleClassK_surjective K Y q x
  rw [O.classMap_mk, pull_eq_cohPullback, cohPullbackK_cocycleClassK, pull_eq_cohPullback,
    cohPullbackK_cocycleClassK, O.classMap_mk]
  exact cocycleClassK_congr K X N (O.natural f u) _ _

end

end GroupApproximation.CharClass

open GroupApproximation.CharClass

#audit_axioms exists_eq_add_coboundary_of_cocycleClassK_eq
#audit_axioms eq_of_cocycleClassK_eq_deg_zero
#audit_axioms NaturalCocycleOp.class_add_coboundary
#audit_axioms NaturalCocycleOp.classMap_mk
#audit_axioms NaturalCocycleOp.classMap_natural
