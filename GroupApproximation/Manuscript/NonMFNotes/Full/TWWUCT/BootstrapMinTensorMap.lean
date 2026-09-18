import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapMinTensor
import GroupApproximation.Analysis.CStarMinTensorFunctorial
import GroupApproximation.Analysis.CStarTakesakiIdentification
import GroupApproximation.Analysis.CStarCompletionHom

/-!
# Functoriality of the non-unital minimal tensor product

The minimal tensor product is a bifunctor on `⋆`-homomorphisms and respects homotopy (Blackadar,
*K-Theory for Operator Algebras*, 18.9; Rosenberg--Schochet, Duke Math. J. 55 (1987), §2).  This
file proves both facts for the non-unital product `MinTensor.closed A C` of
`BootstrapMinTensor`.

* `MinTensor.tensorMap₂ ι κ`: the algebraic map `ι ⊗ κ` of unital `⋆`-homomorphisms;
* `MinTensor.minTensorNorm_tensorMap₂_le`: it contracts the minimal norm.  Each spatial norm of
  `(ι ⊗ κ) x` in a pair of GNS representations is the spatial norm of `x` in the pulled-back
  pair, and every spatial norm is at most the minimal norm (`spatialNorm_le_minTensorNorm`);
* `MinTensor.tensorMapMin ι κ`: the extension `A ⊗_min C → A' ⊗_min C'` to the completions;
* `MinTensor.map f g : A ⊗_min C →⋆ₙₐ A' ⊗_min C'` for non-unital `f` and `g`, obtained from
  `f⁺ ⊗ g⁺` on the unitizations by restriction.  It sends `a ⊗ c` to `f a ⊗ g c`
  (`ambientMap_gen`) and satisfies `map_id` and `map_comp`;
* `MinTensor.nHomotopic_map`: homotopic pairs give homotopic maps.  Along the dense span of the
  elementary tensors this is continuity of `t ↦ p t a ⊗ q t c`; the ε/3 argument then carries it
  to the closure, since every map in the path is contractive.

Manuscript: `non_mf_group_notes.tex`, UCT input of `thm:fixed-radical-membership`
(lane TWWUCT-F3, work order WO-TWWUCT-F-3).
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.CStarTensor GroupApproximation.CStarState GroupApproximation.Full.TWWKK
open scoped TensorProduct

noncomputable section

namespace MinTensor

/-! ## Unital algebras: the map `ι ⊗ κ` of minimal tensor products -/

section Unital

variable {A A' C C' : Type} [CStarAlgebra A] [CStarAlgebra A'] [CStarAlgebra C]
  [CStarAlgebra C']

/-- `ι ⊗ κ` on algebraic tensors, as a `⋆`-homomorphism. -/
def tensorMap₂ (ι : A →⋆ₐ[ℂ] A') (κ : C →⋆ₐ[ℂ] C') : (A ⊗[ℂ] C) →⋆ₐ[ℂ] (A' ⊗[ℂ] C') :=
  { Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom with
    map_star' := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a c =>
          show Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom (star (a ⊗ₜ[ℂ] c))
            = star (Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom (a ⊗ₜ[ℂ] c))
          rw [TensorProduct.star_tmul, Algebra.TensorProduct.map_tmul,
            Algebra.TensorProduct.map_tmul, TensorProduct.star_tmul]
          show (ι (star a)) ⊗ₜ[ℂ] (κ (star c)) = (star (ι a)) ⊗ₜ[ℂ] (star (κ c))
          rw [map_star, map_star]
      | add y z hy hz =>
          have hy' : Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom (star y)
              = star (Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom y) := hy
          have hz' : Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom (star z)
              = star (Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom z) := hz
          show Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom (star (y + z))
            = star (Algebra.TensorProduct.map ι.toAlgHom κ.toAlgHom (y + z))
          rw [star_add, map_add, hy', hz', map_add, star_add] }

theorem tensorMap₂_tmul (ι : A →⋆ₐ[ℂ] A') (κ : C →⋆ₐ[ℂ] C') (a : A) (c : C) :
    tensorMap₂ ι κ (a ⊗ₜ[ℂ] c) = (ι a) ⊗ₜ[ℂ] (κ c) :=
  Algebra.TensorProduct.map_tmul ι.toAlgHom κ.toAlgHom a c

/-- The product of the GNS representations of `ψ` and `φ`, evaluated at `(ι ⊗ κ) x`, is the
product of the pulled-back representations evaluated at `x`. -/
theorem spatialHom_tensorMap₂ [Nontrivial A] [Nontrivial A'] [Nontrivial C] [Nontrivial C']
    (ψ : State A') (φ : State C') (ι : A →⋆ₐ[ℂ] A') (κ : C →⋆ₐ[ℂ] C') (x : A ⊗[ℂ] C) :
    spatialHom ψ.gnsRep φ.gnsRep (tensorMap₂ ι κ x)
      = spatialHom (gnsCompRep ψ ι) (gnsCompRep φ κ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a c =>
      rw [tensorMap₂_tmul, spatialHom_tmul, spatialHom_tmul, gnsCompRep_hom_apply,
        gnsCompRep_hom_apply]
  | add y z hy hz => simp only [map_add, hy, hz]

/-- **`ι ⊗ κ` contracts the minimal norm.** -/
theorem minTensorNorm_tensorMap₂_le [Nontrivial A] [Nontrivial A'] [Nontrivial C]
    [Nontrivial C'] (ι : A →⋆ₐ[ℂ] A') (κ : C →⋆ₐ[ℂ] C') (x : A ⊗[ℂ] C) :
    minTensorNorm (tensorMap₂ ι κ x) ≤ minTensorNorm x := by
  rw [minTensorNorm_apply]
  refine ciSup_le fun p => ?_
  have h : spatialNorm p.1.gnsRep p.2.gnsRep (tensorMap₂ ι κ x)
      = spatialNorm (gnsCompRep p.1 ι) (gnsCompRep p.2 κ) x := by
    rw [spatialNorm_apply, spatialNorm_apply, spatialHom_tensorMap₂]
  exact h.le.trans (spatialNorm_le_minTensorNorm _ _ x)

/-- The map before completion: unretag, apply `ι ⊗ κ`, land in the completed target. -/
def minPreMap₂ [Nontrivial A] [Nontrivial A'] [Nontrivial C] [Nontrivial C']
    (ι : A →⋆ₐ[ℂ] A') (κ : C →⋆ₐ[ℂ] C') : MinPreTensor A C →⋆ₐ[ℂ] MinTensorProduct A' C' :=
  ((minTensorIn A' C').comp (tensorMap₂ ι κ)).comp
    (WithCStarNorm.unretagStarAlgHom isCStarNorm_minTensorNorm)

theorem norm_minPreMap₂_le [Nontrivial A] [Nontrivial A'] [Nontrivial C] [Nontrivial C']
    (ι : A →⋆ₐ[ℂ] A') (κ : C →⋆ₐ[ℂ] C') (x : MinPreTensor A C) :
    ‖minPreMap₂ ι κ x‖ ≤ ‖x‖ := by
  show ‖minTensorIn A' C' (tensorMap₂ ι κ
      (WithCStarNorm.unretagStarAlgHom isCStarNorm_minTensorNorm x))‖ ≤ ‖x‖
  rw [norm_minTensorIn]
  exact minTensorNorm_tensorMap₂_le ι κ _

/-- **The map `ι ⊗ κ : A ⊗_min C → A' ⊗_min C'`**, the contractive extension across the
completion. -/
def tensorMapMin [Nontrivial A] [Nontrivial A'] [Nontrivial C] [Nontrivial C']
    (ι : A →⋆ₐ[ℂ] A') (κ : C →⋆ₐ[ℂ] C') : MinTensorProduct A C →⋆ₐ[ℂ] MinTensorProduct A' C' :=
  GroupApproximation.CStarCompletion.extendStarAlgHom (minPreMap₂ ι κ)
    (GroupApproximation.CStarCompletion.uniformContinuous_of_norm_le _
      fun x => norm_minPreMap₂_le ι κ x)

theorem tensorMapMin_minTensorIn [Nontrivial A] [Nontrivial A'] [Nontrivial C]
    [Nontrivial C'] (ι : A →⋆ₐ[ℂ] A') (κ : C →⋆ₐ[ℂ] C') (x : A ⊗[ℂ] C) :
    tensorMapMin ι κ (minTensorIn A C x) = minTensorIn A' C' (tensorMap₂ ι κ x) := by
  show GroupApproximation.CStarCompletion.extendStarAlgHom _ _ (minTensorIn A C x) = _
  exact GroupApproximation.CStarCompletion.extendStarAlgHom_coe _ _ _

theorem continuous_tensorMapMin [Nontrivial A] [Nontrivial A'] [Nontrivial C]
    [Nontrivial C'] (ι : A →⋆ₐ[ℂ] A') (κ : C →⋆ₐ[ℂ] C') : Continuous (tensorMapMin ι κ) :=
  UniformSpace.Completion.continuous_extension
    (f := ((minPreMap₂ ι κ : MinPreTensor A C →⋆ₐ[ℂ] MinTensorProduct A' C') :
      MinPreTensor A C → MinTensorProduct A' C'))

end Unital

/-! ## Non-unital algebras: the map `f ⊗ g` of `A ⊗_min C` -/

section NonUnital

variable {A A' A'' C C' C'' : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra C] [NonUnitalCStarAlgebra C']
  [NonUnitalCStarAlgebra C'']

/-- `f⁺ ⊗ g⁺ : A⁺ ⊗_min C⁺ → A'⁺ ⊗_min C'⁺`. -/
def ambientMap (f : A →⋆ₙₐ[ℂ] A') (g : C →⋆ₙₐ[ℂ] C') : Ambient A C →⋆ₐ[ℂ] Ambient A' C' :=
  tensorMapMin (Unitization.starMap f) (Unitization.starMap g)

theorem continuous_ambientMap (f : A →⋆ₙₐ[ℂ] A') (g : C →⋆ₙₐ[ℂ] C') :
    Continuous (ambientMap f g) :=
  continuous_tensorMapMin (Unitization.starMap f) (Unitization.starMap g)

/-- `f⁺ ⊗ g⁺` sends `a ⊗ c` to `f a ⊗ g c`. -/
theorem ambientMap_gen (f : A →⋆ₙₐ[ℂ] A') (g : C →⋆ₙₐ[ℂ] C') (a : A) (c : C) :
    ambientMap f g (gen A C a c) = gen A' C' (f a) (g c) := by
  show tensorMapMin (Unitization.starMap f) (Unitization.starMap g)
      (minTensorIn (Unitization ℂ A) (Unitization ℂ C)
        ((Unitization.inr a : Unitization ℂ A) ⊗ₜ[ℂ] (Unitization.inr c : Unitization ℂ C)))
    = minTensorIn (Unitization ℂ A') (Unitization ℂ C')
        ((Unitization.inr (f a) : Unitization ℂ A') ⊗ₜ[ℂ]
          (Unitization.inr (g c) : Unitization ℂ C'))
  rw [tensorMapMin_minTensorIn, tensorMap₂_tmul, Unitization.starMap_inr,
    Unitization.starMap_inr]

/-- `f⁺ ⊗ g⁺` maps `A ⊗_min C` into `A' ⊗_min C'`. -/
theorem ambientMap_mem_closed (f : A →⋆ₙₐ[ℂ] A') (g : C →⋆ₙₐ[ℂ] C') {x : Ambient A C}
    (hx : x ∈ closed A C) : ambientMap f g x ∈ closed A' C' := by
  have hspan : ∀ y ∈ Submodule.span ℂ (generators A C),
      ambientMap f g y ∈ Submodule.span ℂ (generators A' C') := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨p, rfl⟩ := hy'
      show ambientMap f g (gen A C p.1 p.2) ∈ Submodule.span ℂ (generators A' C')
      rw [ambientMap_gen]
      exact Submodule.subset_span ⟨(f p.1, g p.2), rfl⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [map_smul]
      exact Submodule.smul_mem _ r hy
  have hmaps : Set.MapsTo (ambientMap f g)
      (Submodule.span ℂ (generators A C) : Set (Ambient A C))
      (Submodule.span ℂ (generators A' C') : Set (Ambient A' C')) := by
    intro y hy
    exact hspan y hy
  exact mem_closed.2 (map_mem_closure (continuous_ambientMap f g) (mem_closed.1 hx) hmaps)

/-- **The map `f ⊗ g : A ⊗_min C → A' ⊗_min C'`** of non-unital `⋆`-homomorphisms. -/
def map (f : A →⋆ₙₐ[ℂ] A') (g : C →⋆ₙₐ[ℂ] C') : closed A C →⋆ₙₐ[ℂ] closed A' C' :=
  NonUnitalStarAlgHom.codRestrict
    ((ambientMap f g).toNonUnitalStarAlgHom.comp
      (NonUnitalStarSubalgebraClass.subtype (R := ℂ) (closed A C)))
    (closed A' C') (fun x => ambientMap_mem_closed f g x.2)

theorem coe_map (f : A →⋆ₙₐ[ℂ] A') (g : C →⋆ₙₐ[ℂ] C') (x : closed A C) :
    (map f g x : Ambient A' C') = ambientMap f g x :=
  rfl

/-- `f ⊗ g` sends `a ⊗ c` to `f a ⊗ g c`. -/
theorem map_tmul (f : A →⋆ₙₐ[ℂ] A') (g : C →⋆ₙₐ[ℂ] C') (a : A) (c : C) :
    map f g (tmul a c) = tmul (f a) (g c) :=
  Subtype.ext (ambientMap_gen f g a c)

/-- Two continuous `⋆`-homomorphisms that agree on the elementary tensors agree on
`A ⊗_min C`. -/
theorem ext_closed {Φ Ψ : Ambient A C →⋆ₐ[ℂ] Ambient A' C'} (hΦ : Continuous Φ)
    (hΨ : Continuous Ψ) (h : ∀ (a : A) (c : C), Φ (gen A C a c) = Ψ (gen A C a c))
    {x : Ambient A C} (hx : x ∈ closed A C) : Φ x = Ψ x := by
  have hspan : ∀ y ∈ Submodule.span ℂ (generators A C), Φ y = Ψ y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨p, rfl⟩ := hy'
      exact h p.1 p.2
    | zero => rw [map_zero, map_zero]
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | smul r y _ hy => rw [map_smul, map_smul, hy]
  have hsub : (Submodule.span ℂ (generators A C) : Set (Ambient A C)) ⊆
      {w : Ambient A C | Φ w = Ψ w} := by
    intro w hw
    exact hspan w hw
  exact closure_minimal hsub (isClosed_eq hΦ hΨ) (mem_closed.1 hx)

/-- **Identities go to the identity.** -/
theorem map_id :
    map (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ C)
      = NonUnitalStarAlgHom.id ℂ (closed A C) := by
  refine NonUnitalStarAlgHom.ext fun x => Subtype.ext ?_
  show ambientMap (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ C) x
    = StarAlgHom.id ℂ (Ambient A C) x
  exact ext_closed (Φ := ambientMap (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ C))
    (Ψ := StarAlgHom.id ℂ (Ambient A C)) (continuous_ambientMap _ _)
    (continuous_id.congr fun _ => rfl) (fun a c => (ambientMap_gen (NonUnitalStarAlgHom.id ℂ A)
      (NonUnitalStarAlgHom.id ℂ C) a c).trans rfl) x.2

/-- **Composites go to composites.** -/
theorem map_comp (f : A →⋆ₙₐ[ℂ] A') (f' : A' →⋆ₙₐ[ℂ] A'') (g : C →⋆ₙₐ[ℂ] C')
    (g' : C' →⋆ₙₐ[ℂ] C'') : map (f'.comp f) (g'.comp g) = (map f' g').comp (map f g) := by
  refine NonUnitalStarAlgHom.ext fun x => Subtype.ext ?_
  show ambientMap (f'.comp f) (g'.comp g) x = ((ambientMap f' g').comp (ambientMap f g)) x
  refine ext_closed (Φ := ambientMap (f'.comp f) (g'.comp g))
    (Ψ := (ambientMap f' g').comp (ambientMap f g)) (continuous_ambientMap _ _)
    ((continuous_ambientMap f' g').comp (continuous_ambientMap f g)) (fun a c => ?_) x.2
  rw [ambientMap_gen, StarAlgHom.comp_apply, ambientMap_gen, ambientMap_gen,
    NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.comp_apply]

/-! ## Homotopy invariance -/

/-- A `⋆`-homomorphism between C⋆-algebras is `1`-Lipschitz. -/
theorem dist_starAlgHom_le (Φ : Ambient A C →⋆ₐ[ℂ] Ambient A' C') (u v : Ambient A C) :
    dist (Φ u) (Φ v) ≤ dist u v := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact NonUnitalStarAlgHom.norm_apply_le Φ (u - v)

/-- **Continuity along a path**: for pointwise continuous paths `p` and `q`, the map
`t ↦ (p t ⊗ q t) x` is continuous at every `x ∈ A ⊗_min C`. -/
theorem continuous_ambientMap_path (p : ℝ → A →⋆ₙₐ[ℂ] A') (q : ℝ → C →⋆ₙₐ[ℂ] C')
    (hp : ∀ a : A, Continuous fun t : ℝ => p t a) (hq : ∀ c : C, Continuous fun t : ℝ => q t c)
    {x : Ambient A C} (hx : x ∈ closed A C) :
    Continuous fun t : ℝ => ambientMap (p t) (q t) x := by
  have hspan : ∀ y ∈ Submodule.span ℂ (generators A C),
      Continuous fun t : ℝ => ambientMap (p t) (q t) y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨⟨a, c⟩, rfl⟩ := hy'
      exact ((continuous_gen A' C').comp ((hp a).prodMk (hq c))).congr
        fun t => (ambientMap_gen (p t) (q t) a c).symm
    | zero =>
      exact continuous_const.congr fun t => (map_zero (ambientMap (p t) (q t))).symm
    | add y z _ _ hy hz =>
      exact (hy.fun_add hz).congr fun t => (map_add (ambientMap (p t) (q t)) y z).symm
    | smul r y _ hy =>
      exact (hy.fun_const_smul r).congr fun t => (map_smul (ambientMap (p t) (q t)) r y).symm
  rw [Metric.continuous_iff]
  intro t ε hε
  have hε3 : 0 < ε / 3 := div_pos hε three_pos
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 (mem_closed.1 hx) (ε / 3) hε3
  obtain ⟨δ, hδ, hδy⟩ := Metric.continuous_iff.1 (hspan y hy) t (ε / 3) hε3
  refine ⟨δ, hδ, fun s hs => ?_⟩
  calc dist (ambientMap (p s) (q s) x) (ambientMap (p t) (q t) x)
      ≤ dist (ambientMap (p s) (q s) x) (ambientMap (p s) (q s) y)
        + dist (ambientMap (p s) (q s) y) (ambientMap (p t) (q t) y)
        + dist (ambientMap (p t) (q t) y) (ambientMap (p t) (q t) x) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        refine add_lt_add (add_lt_add ?_ ?_) ?_
        · exact (dist_starAlgHom_le _ x y).trans_lt hxy
        · exact hδy s hs
        · exact (dist_starAlgHom_le _ y x).trans_lt ((dist_comm y x).trans_lt hxy)
    _ = ε := by ring

theorem continuous_map_path (p : ℝ → A →⋆ₙₐ[ℂ] A') (q : ℝ → C →⋆ₙₐ[ℂ] C')
    (hp : ∀ a : A, Continuous fun t : ℝ => p t a) (hq : ∀ c : C, Continuous fun t : ℝ => q t c)
    (x : closed A C) : Continuous fun t : ℝ => map (p t) (q t) x :=
  (Continuous.subtype_mk (p := fun y : Ambient A' C' => y ∈ closed A' C')
    (continuous_ambientMap_path p q hp hq x.2)
    fun t => ambientMap_mem_closed (p t) (q t) x.2).congr
    fun t => Subtype.ext (coe_map (p t) (q t) x).symm

/-- **Homotopy invariance**: homotopic pairs of `⋆`-homomorphisms give homotopic maps of
minimal tensor products. -/
theorem nHomotopic_map {f f' : A →⋆ₙₐ[ℂ] A'} {g g' : C →⋆ₙₐ[ℂ] C'} (hf : NHomotopic f f')
    (hg : NHomotopic g g') : NHomotopic (map f g) (map f' g') := by
  obtain ⟨p, hp, hp0, hp1⟩ := hf
  obtain ⟨q, hq, hq0, hq1⟩ := hg
  refine ⟨fun t => map (p t) (q t), fun x => continuous_map_path p q hp hq x, ?_, ?_⟩
  · show map (p 0) (q 0) = map f g
    rw [hp0, hq0]
  · show map (p 1) (q 1) = map f' g'
    rw [hp1, hq1]

end NonUnital

end MinTensor

end

end GroupApproximation.Full.TWWUCT.Bootstrap
