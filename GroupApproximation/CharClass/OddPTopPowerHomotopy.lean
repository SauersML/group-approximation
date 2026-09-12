import GroupApproximation.CharClass.OddPTopPowerAWEval
import GroupApproximation.CharClass.AcyclicModels
import GroupApproximation.CharClass.OddPAcyclic
import GroupApproximation.CharClass.SteenrodCochain

/-!
# Every natural diagonal evaluates to the cup power up to a coboundary

Over a field `K`, the flat `r`-fold tensor power `X ↦ C(X)^{⊗r}` is a functor into complexes that is
acyclic on the standard simplices (lix-cupone's `tupD_exists_preimage_stdSimplexTop`), and the
singular chains `singFreeR K` are free on them.  So the acyclic-models theorem compares any two
natural chain maps `singFreeR K ⟶ C(−)^{⊗r}` that agree in degree `0`.  One of them is the iterated
Alexander–Whitney diagonal (`awNat`, from `OddPTopPowerAWChain.lean`), whose evaluation against
`u^{⊗r}` is the cup power `u^{⌣r}` (`OddPTopPowerAWEval.lean`).  Hence:

* `eval_eq_awTup_add_coboundary` — for any natural chain map `Φ` agreeing with the diagonal in
  degree `0` and any cocycle `u`, `⟨u^{⊗r}, Φ(σ)⟩ = ⟨u^{⊗r}, AW^{(r)}(σ)⟩ + (δw)(σ)` for one
  cochain `w`, uniformly in the simplex `σ`.

Applied at the non-equivariant part `Δ(e₀ ⊗ −)` of the odd-primary diagonal this is the top power
`[D₀ u] = [u ⌣ ⋯ ⌣ u]` (`OddPTopPower.lean`).
-/

namespace GroupApproximation.CharClass

open CategoryTheory Simplicial
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace TopPow

/-! ## 1. The tensor power over `K` as a functor into complexes -/

section Functor

variable (K : Type) [CommRing K]

/-- The flat `r`-fold tensor power of the singular chains of `X`, as a complex over `K`. -/
def tupCxK (X : TopCat.{0}) (r : ℕ) : ChainComplex (ModuleCat.{0} K) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of K (tupMod K X r k))
    (fun k => ModuleCat.ofHom (tupD K X r k))
    (fun k => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
      exact tupD_tupD K X k y)

theorem tupCxK_d (X : TopCat.{0}) (r k : ℕ) :
    (tupCxK K X r).d (k + 1) k = ModuleCat.ofHom (tupD K X r k) := by
  simp [tupCxK]

/-- The pushforward, as a map of complexes. -/
def tupCxKMap {X Y : TopCat.{0}} (f : X ⟶ Y) (r : ℕ) : tupCxK K X r ⟶ tupCxK K Y r where
  f k := ModuleCat.ofHom (tupMap K f r k)
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst hij'
    rw [tupCxK_d, tupCxK_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
    exact (tupMap_tupD K f j y).symm

theorem tupCxKMap_f {X Y : TopCat.{0}} (f : X ⟶ Y) (r k : ℕ) :
    (tupCxKMap K f r).f k = ModuleCat.ofHom (tupMap K f r k) :=
  rfl

/-- **The tensor power over `K`**: `X ↦ C(X)^{⊗r}`. -/
def tupFunK (r : ℕ) : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} K) ℕ where
  obj X := tupCxK K X r
  map f := tupCxKMap K f r
  map_id X := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [tupCxKMap_f, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply,
      ModuleCat.hom_ofHom]
    exact tupMap_id K k y
  map_comp f g := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [tupCxKMap_f, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      ModuleCat.hom_ofHom]
    exact tupMap_comp K f g k y

theorem tupFunK_d (r : ℕ) (X : TopCat.{0}) (k : ℕ) :
    ((tupFunK K r).obj X).d (k + 1) k = ModuleCat.ofHom (tupD K X r k) :=
  tupCxK_d K X r k

end Functor

/-! ## 2. The two hypotheses of the acyclic-models theorem -/

/-- **The tensor power is acyclic on the models** as soon as its differential is exact there.  Stated
with the exactness as data, so that `ZMod p` can supply it at its own `CommRing` structure (the
`Field` export elaborates at `Field.toCommRing`, and unifying the two can time out). -/
theorem tupFunK_acyclicOnModels_of (K : Type) [CommRing K] (r : ℕ)
    (hex : ∀ (n k : ℕ) (y : tupMod K (stdSimplexTop n) r (k + 1)),
      tupD K (stdSimplexTop n) r k y = 0 →
        ∃ z : tupMod K (stdSimplexTop n) r (k + 2), tupD K (stdSimplexTop n) r (k + 1) z = y) :
    AcyclicOnModels stdSimplexTop K (tupFunK K r) where
  exists_preimage n k y hy := by
    rw [tupFunK_d] at hy
    obtain ⟨z, hz⟩ := hex n k y hy
    refine ⟨z, ?_⟩
    rw [show ((tupFunK K r).obj (stdSimplexTop n)).d (k + 2) (k + 1)
        = ModuleCat.ofHom (tupD K (stdSimplexTop n) r (k + 1)) from tupFunK_d K r _ (k + 1)]
    exact hz

/-- **The tensor power is acyclic on the models**, over a field. -/
theorem tupFunK_acyclicOnModels (K : Type) [Field K] (r : ℕ) :
    AcyclicOnModels stdSimplexTop K (tupFunK K r) :=
  tupFunK_acyclicOnModels_of K r fun n k y hy => tupD_exists_preimage_stdSimplexTop K n r k y hy

/-- **The singular chains are free on the standard simplices**, over any ring. -/
def singFreeR_freeOnModels (K : Type) [CommRing K] :
    FreeOnModels stdSimplexTop K (singFreeR K) where
  B _ := Unit
  mdl k _ := k
  gen k _ := Finsupp.single ((simplexEquiv (stdSimplexTop k) k).symm (𝟙 (stdSimplexTop k))) (1 : K)
  basis X k := (Finsupp.basisSingleOne (R := K) (ι := singularSimplices X k)).reindex
    ((simplexEquiv X k).trans (Equiv.uniqueSigma fun _ : Unit => stdSimplexTop k ⟶ X).symm)
  basis_apply X k b φ := by
    rw [Module.Basis.reindex_apply]
    show Finsupp.single ((simplexEquiv X k).symm φ) (1 : K) = _
    rw [singFreeR_map_single]
    congr 1
    apply (simplexEquiv X k).injective
    rw [simplexEquiv_pushSimplex, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.id_comp]

/-! ## 3. The diagonal as a natural transformation -/

section Nat

variable (K : Type) [CommRing K]

/-- The graded diagonal of a `k`-simplex. -/
def awTup (X : TopCat.{0}) (r k : ℕ) (σ : singularSimplices X k) : tupMod K X r k :=
  Finsupp.comapDomain Subtype.val (awAll K X r ⟨k, σ⟩) fun _ _ _ _ h => Subtype.val_injective h

theorem tupIncl_awTup (X : TopCat.{0}) (r k : ℕ) (σ : singularSimplices X k) :
    tupIncl K X r k (awTup K X r k σ) = awAll K X r ⟨k, σ⟩ := by
  unfold awTup tupIncl
  rw [Finsupp.lmapDomain_apply]
  refine Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective _ ?_
  intro t ht
  exact ⟨⟨t, (Finsupp.mem_supported K _).mp (awAll_mem K X r ⟨k, σ⟩) ht⟩, rfl⟩

/-- The graded diagonal, extended linearly to chains. -/
def awTupLin (X : TopCat.{0}) (r k : ℕ) : (singularSimplices X k →₀ K) →ₗ[K] tupMod K X r k :=
  Finsupp.linearCombination K (awTup K X r k)

theorem awTupLin_single (X : TopCat.{0}) (r k : ℕ) (σ : singularSimplices X k) :
    awTupLin K X r k (Finsupp.single σ 1) = awTup K X r k σ := by
  unfold awTupLin
  rw [Finsupp.linearCombination_single, one_smul]

theorem tupD_awTup (X : TopCat.{0}) (r k : ℕ) (σ : singularSimplices X (k + 1)) :
    tupD K X r k (awTup K X r (k + 1) σ)
      = awTupLin K X r k (chainBd K X k (Finsupp.single σ 1)) := by
  apply tupIncl_injective K X k
  have h1 := LinearMap.congr_fun (tupIncl_comp_tupD K X k) (awTup K X r (k + 1) σ)
  simp only [LinearMap.comp_apply] at h1
  rw [h1, tupIncl_awTup, tupDAll_awAll, tagBd_succ_eq]
  unfold awLin awTupLin
  rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
  exact tupLC_congr_fun K (fun σ' => (tupIncl_awTup K X r k σ').symm) _

theorem tupD_awTupLin (X : TopCat.{0}) (r k : ℕ) (c : singularSimplices X (k + 1) →₀ K) :
    tupD K X r k (awTupLin K X r (k + 1) c) = awTupLin K X r k (chainBd K X k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single σ a =>
    rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : K) by rw [Finsupp.smul_single_one],
      map_smul, map_smul, map_smul, map_smul, awTupLin_single, tupD_awTup]

theorem tupMap_awTup {X Y : TopCat.{0}} (f : X ⟶ Y) (r k : ℕ) (σ : singularSimplices X k) :
    tupMap K f r k (awTup K X r k σ) = awTup K Y r k (pushSimplex f k σ) := by
  apply tupIncl_injective K Y k
  have h1 := LinearMap.congr_fun (tupIncl_comp_tupMap K f k) (awTup K X r k σ)
  simp only [LinearMap.comp_apply] at h1
  rw [h1, tupIncl_awTup, tupIncl_awTup, tupAllMap_awAll]
  rfl

theorem tupMap_awTupLin {X Y : TopCat.{0}} (f : X ⟶ Y) (r k : ℕ) (c : singularSimplices X k →₀ K) :
    tupMap K f r k (awTupLin K X r k c) = awTupLin K Y r k (Finsupp.mapDomain (pushSimplex f k) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.mapDomain_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, Finsupp.mapDomain_add, map_add]
  | single σ a =>
    rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : K) by rw [Finsupp.smul_single_one],
      map_smul, map_smul, Finsupp.mapDomain_smul, map_smul, Finsupp.mapDomain_single,
      awTupLin_single, awTupLin_single, tupMap_awTup]

/-- **The iterated Alexander–Whitney diagonal as a natural chain map** `singFreeR K ⟶ tupFunK K r`. -/
def awNat (r : ℕ) : singFreeR K ⟶ tupFunK K r where
  app X :=
    { f := fun k => ModuleCat.ofHom (awTupLin K X r k)
      comm' := by
        rintro i j (rfl : j + 1 = i)
        rw [tupFunK_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro c
        simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
        exact tupD_awTupLin K X r j c }
  naturality X Y f := by
    refine HomologicalComplex.hom_ext _ _ fun k => ?_
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
    show awTupLin K Y r k ((((singFreeR K).map f).f k).hom c) = tupMap K f r k (awTupLin K X r k c)
    rw [singFreeR_map_apply, tupMap_awTupLin]

theorem awNat_app_f_single (r : ℕ) (X : TopCat.{0}) (k : ℕ) (σ : singularSimplices X k) :
    (((awNat K r).app X).f k).hom (Finsupp.single σ 1) = awTup K X r k σ :=
  awTupLin_single K X r k σ

end Nat

/-! ## 4. The comparison -/

/-- A single-degree cocycle has no graded coboundary. -/
theorem gCoboundary_piSingle (K : Type) [CommRing K] {X : TopCat.{0}} {q : ℕ}
    (u : singularCochainGroup K X q) (hu : cochainCoboundary K X q u = 0) :
    gCoboundary K X (Pi.single q u) = 0 := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show cochainCoboundary K X n (Pi.single q u n) = 0
    by_cases h : n = q
    · subst h
      rw [Pi.single_eq_same, hu]
    · rw [Pi.single_eq_of_ne h u]
      unfold cochainCoboundary
      exact map_zero _

/-- **Every natural diagonal evaluates to the Alexander–Whitney evaluation up to a coboundary.**
For a natural chain map `Φ : singFreeR K ⟶ tupFunK K r` agreeing with `awNat` in degree `0` and a
cocycle `u ∈ C^q(X; K)`, there is one `k`-cochain `w` with
`⟨u^{⊗r}, Φ(σ)⟩ = ⟨u^{⊗r}, AW^{(r)}(σ)⟩ + (δw)(σ)` for every `(k+1)`-simplex `σ`. -/
theorem eval_eq_awTup_add_coboundary (K : Type) [CommRing K] (r : ℕ)
    (hG : AcyclicOnModels stdSimplexTop K (tupFunK K r))
    (Φ : singFreeR K ⟶ tupFunK K r)
    (h0 : ∀ X : TopCat.{0}, (Φ.app X).f 0 = ((awNat K r).app X).f 0)
    {X : TopCat.{0}} {q : ℕ} (u : singularCochainGroup K X q)
    (hu : cochainCoboundary K X q u = 0) (k : ℕ) :
    ∃ w : singularCochainGroup K X k, ∀ σ : singularSimplices X (k + 1),
      tupEval K X r (k + 1) (fun _ => Pi.single q u)
          (((Φ.app X).f (k + 1)).hom (Finsupp.single σ 1))
        = tupEval K X r (k + 1) (fun _ => Pi.single q u) (awTup K X r (k + 1) σ)
          + cochainEval (k + 1) (cochainCoboundary K X k w) σ := by
  let H := acyclicModelsHomotopy (singFreeR_freeOnModels K) hG Φ (awNat K r) h0
  refine ⟨cochainOfFun k fun τ =>
      tupEval K X r (k + 1) (fun _ => Pi.single q u) ((H.s k X).hom (Finsupp.single τ 1)),
    fun σ => ?_⟩
  have hcomm := congrArg (fun g => ModuleCat.Hom.hom g (Finsupp.single σ (1 : K))) (H.comm_succ k X)
  simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_add, LinearMap.add_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [awNat_app_f_single, sub_eq_iff_eq_add, tupFunK_d] at hcomm
  rw [hcomm, map_add, map_add]
  have hE : tupEval K X r (k + 1) (fun _ => Pi.single q u)
      ((ModuleCat.ofHom (tupD K X r (k + 1))).hom ((H.s (k + 1) X).hom (Finsupp.single σ 1))) = 0 :=
    tupEval_tupD_eq_zero K (fun _ => Pi.single q u) (fun _ => gCoboundary_piSingle K u hu) (k + 1) _
  rw [hE, add_zero, add_comm]
  refine congrArg (_ + ·) ?_
  rw [cochainCoboundary_eval]
  show tupEval K X r (k + 1) (fun _ => Pi.single q u)
      ((H.s k X).hom (chainBd K X k (Finsupp.single σ 1))) = _
  rw [chainBd, singFreeR_d_single, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, cochainEval_cochainOfFun, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one]

#audit_axioms tupFunK_acyclicOnModels
#audit_axioms awNat
#audit_axioms eval_eq_awTup_add_coboundary

end TopPow

end

end GroupApproximation.CharClass
