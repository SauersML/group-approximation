import GroupApproximation.CharClass.CartanFourfold
import GroupApproximation.CharClass.SteenrodComparisonMap
import GroupApproximation.CharClass.SteenrodFourfoldAW

/-!
# The first composite of the internal Cartan comparison

`A = (Φ₀ ⊗ Φ₀) ∘ Φ`, as a natural transformation from `W ⊗ S(X)` to
`S(X)^{⊗4}` over the group ring.

Every ingredient is already proved.  `cc-steenrod` supplies `Φ` as a natural
transformation and `Φ₀` as a chain map that is natural in the space; this lane
supplies the tensor of two chain maps, its chain-map property, its functoriality
and its compatibility with the swap.  So the file is assembly, with one genuine
identification in it: the two lanes' pushforwards on the pair complex agree,
`cc-steenrod`'s written as a map of indices and this lane's as the tensor of two
singular pushforwards.

## Main results

* `awHom` — `Φ₀`, as a chain map of free `F₂`-complexes.
* `tenHom_singHom` — the two lanes' pushforwards on the pair agree.
* `compACx`, `compA` — **the first composite**, on one space and as a natural
  transformation.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-! ## 1. `Φ₀` as a chain map -/

/-- The Alexander–Whitney diagonal, as a chain map of free `F₂`-complexes. -/
noncomputable def awHom (X : TopCat.{0}) : FreeCxHom (singFreeCx X) (pairFreeCx X) where
  f k := Steenrod.awDiag X k
  comm k u := by
    rw [tensorD_eq_dTgt]
    exact (Steenrod.dTgt_awDiag X k u).symm

/-! ## 2. The two pushforwards on the pair complex agree -/

theorem tenHomGen_singHom {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (q : Steenrod.PairIdx X k) :
    tenHomGen (singHom f) (singHom f) k q
      = Finsupp.single (Steenrod.pairIdxPush f k q) 1 := by
  obtain ⟨⟨⟨a, b⟩, hab⟩, x, y⟩ := q
  have h1 : (singHom f).f a (Finsupp.single x (1 : ZMod 2))
      = Finsupp.single (pushSimplex f a x) (1 : ZMod 2) := Finsupp.mapDomain_single
  have h2 : (singHom f).f b (Finsupp.single y (1 : ZMod 2))
      = Finsupp.single (pushSimplex f b y) (1 : ZMod 2) := Finsupp.mapDomain_single
  show tenElt (singFreeCx Y) (singFreeCx Y) (⟨(a, b), hab⟩ : Steenrod.PairDeg k)
      ((singHom f).f a (Finsupp.single x 1)) ((singHom f).f b (Finsupp.single y 1)) = _
  rw [h1, h2]
  exact tenElt_single_single (singFreeCx Y) (singFreeCx Y) _ _ _

/-- **The two lanes' pushforwards on the pair complex are the same map.** -/
theorem tenHom_singHom {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (y : Steenrod.PairIdx X k →₀ ZMod 2) :
    tenHom (singHom f) (singHom f) k y = Steenrod.pairPushLin X Y f k y := by
  induction y using Finsupp.induction_linear with
  | zero =>
      calc tenHom (singHom f) (singHom f) k (0 : Steenrod.PairIdx X k →₀ ZMod 2)
          = 0 := map_zero _
        _ = Steenrod.pairPushLin X Y f k 0 := (map_zero _).symm
  | add u v hu hv =>
      calc tenHom (singHom f) (singHom f) k (u + v)
          = tenHom (singHom f) (singHom f) k u + tenHom (singHom f) (singHom f) k v :=
            map_add _ u v
        _ = Steenrod.pairPushLin X Y f k u + Steenrod.pairPushLin X Y f k v := by
            rw [hu, hv]
        _ = Steenrod.pairPushLin X Y f k (u + v) := (map_add _ u v).symm
  | single q c =>
      calc tenHom (singHom f) (singHom f) k (Finsupp.single q c)
          = c • tenHomGen (singHom f) (singHom f) k q :=
            tenHom_single (singHom f) (singHom f) k q c
        _ = c • Finsupp.single (Steenrod.pairIdxPush f k q) (1 : ZMod 2) :=
            congrArg (fun w => c • w) (tenHomGen_singHom f k q)
        _ = Finsupp.single (Steenrod.pairIdxPush f k q) c := by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        _ = Steenrod.pairPushLin X Y f k (Finsupp.single q c) :=
            (Steenrod.pairPushLin_single f k q c).symm

/-! ## 3. `Φ₀` is natural -/

theorem awDiag_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (u : singularSimplices X k →₀ ZMod 2) :
    Steenrod.pairPushLin X Y f k (Steenrod.awDiag X k u)
      = Steenrod.awDiag Y k (Finsupp.mapDomain (pushSimplex f k) u) := by
  induction u using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, Finsupp.mapDomain_zero, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, Finsupp.mapDomain_add, map_add]
  | single σ c =>
      rw [Steenrod.awDiag_single, map_smul, Finsupp.mapDomain_single,
        Steenrod.awDiag_single, Steenrod.phiZero_naturality]

theorem awHom_comp_singHom {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (awHom Y).comp (singHom f) = (pairHom f).comp (awHom X) := by
  refine FreeCxHom.ext (funext fun k => ?_)
  apply LinearMap.ext
  intro u
  show Steenrod.awDiag Y k (Finsupp.lmapDomain (ZMod 2) (ZMod 2) (pushSimplex f k) u)
    = tenHom (singHom f) (singHom f) k (Steenrod.awDiag X k u)
  rw [Finsupp.lmapDomain_apply, tenHom_singHom, awDiag_naturality]

/-! ## 4. `Φ₀ ⊗ Φ₀` over the group ring -/

/-- `Φ₀ ⊗ Φ₀`, as a map of modules over the group ring: it commutes with the
factor swap on the pair and with the block swap on the fourfold. -/
noncomputable def awTenLambda (X : TopCat.{0}) (k : ℕ) :
    (Steenrod.PairIdx X k →₀ ZMod 2) →ₗ[GroupRingZ2]
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) where
  toFun := tenHom (awHom X) (awHom X) k
  map_add' u v := map_add _ u v
  map_smul' c y :=
    galAlgHom_comm (Steenrod.swapEnd X k) (Steenrod.swapEnd_sq X k)
      (tenSwap (pairFreeCx X) k) (tenSwap_mul_self (pairFreeCx X) k)
      (tenHom (awHom X) (awHom X) k) (tenHom_tenSwap (awHom X) k) c y

/-! ## 5. The composite -/

/-- The first composite, degreewise. -/
noncomputable def compAHom (X : TopCat.{0}) (k : ℕ) :
    WTensorSMod X k →ₗ[GroupRingZ2]
      (TensorIdx (pairFreeCx X) (pairFreeCx X) k →₀ ZMod 2) :=
  (awTenLambda X k).comp (Steenrod.PhiHom X k)

/-- The first composite on one space, as a map of complexes. -/
noncomputable def compACx (X : TopCat.{0}) :
    srcComplex singularBoundary X ⟶ fourCx X where
  f k := ModuleCat.ofHom (compAHom X k)
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rw [srcComplex_d, fourCx_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    have h : tensorD (singFreeCx X) (singFreeCx X) j (Steenrod.PhiHom X (j + 1) y)
        = Steenrod.PhiHom X j (wDiff singularBoundary X j y) := by
      rw [tensorD_eq_dTgt]
      exact Steenrod.dTgt_PhiHom X j y
    show tensorD (pairFreeCx X) (pairFreeCx X) j
        (tenHom (awHom X) (awHom X) (j + 1) (Steenrod.PhiHom X (j + 1) y))
      = tenHom (awHom X) (awHom X) j (Steenrod.PhiHom X j (wDiff singularBoundary X j y))
    rw [← h, tenHom_tensorD]

/-- **The first composite of the Cartan comparison**, as a natural
transformation. -/
noncomputable def compA : src singularBoundary ⟶ four where
  app X := compACx X
  naturality {X Y} f := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    show tenHom (awHom Y) (awHom Y) k
        (Steenrod.PhiHom Y k (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) y))
      = tenHom (pairHom f) (pairHom f) k
        (tenHom (awHom X) (awHom X) k (Steenrod.PhiHom X k y))
    rw [← Steenrod.PhiHom_naturality f k y, ← tenHom_singHom, ← tenHom_comp,
      ← tenHom_comp, awHom_comp_singHom]

end

end GroupApproximation.CharClass
