import GroupApproximation.CharClass.AcyclicModels

/-!
# The acyclic-models theorem: the existence half

`AcyclicModels.lean` proves that two natural transformations agreeing in degree
`0` are naturally chain homotopic.  This file proves the other half: a natural
map in degree `0` compatible with augmentations *extends* to a natural chain
map.

The induction is the same shape as the uniqueness half, with one difference.
Passing from degree `0` to degree `1` needs to solve `d z = Ψ₀(∂ γ)` in degree
`0`, where positive-degree acyclicity says nothing.  That is what the
augmentation is for: `ε_G(Ψ₀(∂ γ)) = ε_F(∂ γ) = 0`, and `AcyclicZeroOnModels`
supplies a preimage for anything the augmentation kills.  Every later degree
uses ordinary positive-degree acyclicity.  Consequently the induction proves the
chain-map identity `Ψ_{k+1} ∘ d = d ∘ Ψ_k` degree by degree, establishing the
preimage property one step ahead of where it is needed.
-/

universe u v w

namespace GroupApproximation.CharClass

open CategoryTheory CategoryTheory.Limits

section Augmented

variable {C : Type u} [Category.{v} C] {ι : Type w}
variable {Λ : Type} [CommRing Λ]

/-- An **augmentation** of a functor into chain complexes: a natural map out of
degree `0` to a fixed module, killing boundaries. -/
structure Augmentation (Λ : Type) [CommRing Λ]
    (F : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ) (A : ModuleCat.{0} Λ) where
  /-- The augmentation map. -/
  ε : ∀ X : C, (F.obj X).X 0 ⟶ A
  /-- Naturality of the augmentation. -/
  ε_natural : ∀ (X Y : C) (φ : X ⟶ Y), (F.map φ).f 0 ≫ ε Y = ε X
  /-- The augmentation kills boundaries. -/
  ε_d : ∀ X : C, (F.obj X).d 1 0 ≫ ε X = 0

/-- Acyclicity of `G` on the models in degree `0`, relative to an augmentation:
whatever the augmentation kills is a boundary. -/
structure AcyclicZeroOnModels (M : ι → C) {A : ModuleCat.{0} Λ}
    {G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ} (εG : Augmentation Λ G A) : Prop where
  /-- Degree-zero cycles for the augmentation are boundaries. -/
  exists_preimage_zero : ∀ (i : ι) (y : (G.obj (M i)).X 0),
    (εG.ε (M i)).hom y = 0 → ∃ z : (G.obj (M i)).X 1, ((G.obj (M i)).d 1 0).hom z = y

end Augmented

section Existence

variable {C : Type u} [Category.{v} C] {ι : Type w} {M : ι → C}
variable {Λ : Type} [CommRing Λ]
variable {F G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ}

/-- The degree-preserving analogue of `modelHom`: extend a family of universal
elements in degree `k` to a natural map `F(X)_k ⟶ G(X)_k`. -/
noncomputable def cmHom (hF : FreeOnModels M Λ F) (k : ℕ)
    (z : ∀ b : hF.B k, (G.obj (M (hF.mdl k b))).X k) (X : C) :
    (F.obj X).X k ⟶ (G.obj X).X k :=
  ModuleCat.ofHom ((hF.basis X k).constr Λ fun p => ((G.map p.2).f k).hom (z p.1))

lemma cmHom_basis (hF : FreeOnModels M Λ F) (k : ℕ)
    (z : ∀ b : hF.B k, (G.obj (M (hF.mdl k b))).X k) (X : C)
    (b : hF.B k) (φ : M (hF.mdl k b) ⟶ X) :
    (cmHom hF k z X).hom (hF.basis X k ⟨b, φ⟩) = ((G.map φ).f k).hom (z b) := by
  rw [cmHom, ModuleCat.hom_ofHom, Module.Basis.constr_basis]

/-- The universal elements of the extension. -/
noncomputable def cmElt (hF : FreeOnModels M Λ F)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0) :
    ∀ (k : ℕ) (b : hF.B k), (G.obj (M (hF.mdl k b))).X k
  | 0, b => (f0 (M (hF.mdl 0 b))).hom (hF.gen 0 b)
  | k + 1, b =>
      pickPreimage ((G.obj (M (hF.mdl (k + 1) b))).d (k + 1) k)
        ((cmHom hF k (fun c => cmElt hF f0 k c) (M (hF.mdl (k + 1) b))).hom
          (((F.obj (M (hF.mdl (k + 1) b))).d (k + 1) k).hom (hF.gen (k + 1) b)))

/-- The natural chain map produced by the acyclic-models construction. -/
noncomputable def amMap (hF : FreeOnModels M Λ F)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0) (k : ℕ) (X : C) :
    (F.obj X).X k ⟶ (G.obj X).X k :=
  cmHom hF k (fun b => cmElt hF f0 k b) X

lemma amMap_basis (hF : FreeOnModels M Λ F)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0) (k : ℕ) (X : C)
    (b : hF.B k) (φ : M (hF.mdl k b) ⟶ X) :
    (amMap hF f0 k X).hom (hF.basis X k ⟨b, φ⟩)
      = ((G.map φ).f k).hom (cmElt hF f0 k b) :=
  cmHom_basis hF k _ X b φ

lemma cmElt_succ (hF : FreeOnModels M Λ F)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0) (k : ℕ) (b : hF.B (k + 1)) :
    cmElt hF f0 (k + 1) b
      = pickPreimage ((G.obj (M (hF.mdl (k + 1) b))).d (k + 1) k)
          ((amMap hF f0 k (M (hF.mdl (k + 1) b))).hom
            (((F.obj (M (hF.mdl (k + 1) b))).d (k + 1) k).hom (hF.gen (k + 1) b))) := by
  rw [amMap, cmElt]

/-- Naturality of the extension, which holds by construction. -/
lemma amMap_naturality (hF : FreeOnModels M Λ F)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0) (k : ℕ) {X Y : C} (φ : X ⟶ Y) :
    (F.map φ).f k ≫ amMap hF f0 k Y = amMap hF f0 k X ≫ (G.map φ).f k := by
  apply ModuleCat.hom_ext
  apply (hF.basis X k).ext
  rintro ⟨b, ψ⟩
  have hFcomp : ((F.map φ).f k).hom (hF.basis X k ⟨b, ψ⟩) = hF.basis Y k ⟨b, ψ ≫ φ⟩ := by
    rw [hF.basis_apply X k b ψ, hF.basis_apply Y k b (ψ ≫ φ), F.map_comp,
      HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hGcomp : ((G.map (ψ ≫ φ)).f k).hom (cmElt hF f0 k b)
      = ((G.map φ).f k).hom (((G.map ψ).f k).hom (cmElt hF f0 k b)) := by
    rw [G.map_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    hFcomp, amMap_basis, amMap_basis, hGcomp]

/-- In degree `0` the extension is the map it extends. -/
lemma amMap_zero (hF : FreeOnModels M Λ F)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0)
    (hf0 : ∀ (X Y : C) (φ : X ⟶ Y), (F.map φ).f 0 ≫ f0 Y = f0 X ≫ (G.map φ).f 0)
    (X : C) : amMap hF f0 0 X = f0 X := by
  apply ModuleCat.hom_ext
  apply (hF.basis X 0).ext
  rintro ⟨b, φ⟩
  rw [amMap_basis, cmElt, hF.basis_apply X 0 b φ, ← LinearMap.comp_apply,
    ← ModuleCat.hom_comp, hf0 (M (hF.mdl 0 b)) X φ, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The chain-map identity in degree `k+1`, given that the universal elements in
that degree really are preimages. -/
lemma amMap_comm_of_spec (hF : FreeOnModels M Λ F)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0) (k : ℕ)
    (hspec : ∀ b : hF.B (k + 1),
      ((G.obj (M (hF.mdl (k + 1) b))).d (k + 1) k).hom (cmElt hF f0 (k + 1) b)
        = (amMap hF f0 k (M (hF.mdl (k + 1) b))).hom
            (((F.obj (M (hF.mdl (k + 1) b))).d (k + 1) k).hom (hF.gen (k + 1) b)))
    (X : C) :
    amMap hF f0 (k + 1) X ≫ (G.obj X).d (k + 1) k
      = (F.obj X).d (k + 1) k ≫ amMap hF f0 k X := by
  apply ModuleCat.hom_ext
  apply (hF.basis X (k + 1)).ext
  rintro ⟨b, φ⟩
  have hb := hF.basis_apply X (k + 1) b φ
  have hdnat : ((F.obj X).d (k + 1) k).hom (((F.map φ).f (k + 1)).hom (hF.gen (k + 1) b))
      = ((F.map φ).f k).hom (((F.obj (M (hF.mdl (k + 1) b))).d (k + 1) k).hom
          (hF.gen (k + 1) b)) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, (F.map φ).comm (k + 1) k,
      ModuleCat.hom_comp, LinearMap.comp_apply]
  have hGd : ((G.obj X).d (k + 1) k).hom
        (((G.map φ).f (k + 1)).hom (cmElt hF f0 (k + 1) b))
      = ((G.map φ).f k).hom
          (((G.obj (M (hF.mdl (k + 1) b))).d (k + 1) k).hom (cmElt hF f0 (k + 1) b)) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, (G.map φ).comm (k + 1) k,
      ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    amMap_basis, hGd, hspec b, hb, hdnat, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    amMap_naturality, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **The chain-map identity**, by induction on the degree.  The step from degree
`0` uses the augmentation; every later step uses positive-degree acyclicity. -/
lemma amMap_comm {A : ModuleCat.{0} Λ} (hF : FreeOnModels M Λ F)
    (hG : AcyclicOnModels M Λ G) (εF : Augmentation Λ F A) (εG : Augmentation Λ G A)
    (hG0 : AcyclicZeroOnModels M εG)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0)
    (hf0 : ∀ (X Y : C) (φ : X ⟶ Y), (F.map φ).f 0 ≫ f0 Y = f0 X ≫ (G.map φ).f 0)
    (hf0ε : ∀ X : C, f0 X ≫ εG.ε X = εF.ε X) :
    ∀ (k : ℕ) (X : C), amMap hF f0 (k + 1) X ≫ (G.obj X).d (k + 1) k
      = (F.obj X).d (k + 1) k ≫ amMap hF f0 k X := by
  intro k
  induction k with
  | zero =>
      have hspec : ∀ b : hF.B 1,
          ((G.obj (M (hF.mdl 1 b))).d 1 0).hom (cmElt hF f0 1 b)
            = (amMap hF f0 0 (M (hF.mdl 1 b))).hom
                (((F.obj (M (hF.mdl 1 b))).d 1 0).hom (hF.gen 1 b)) := by
        intro b
        have hε : (εG.ε (M (hF.mdl 1 b))).hom
            ((amMap hF f0 0 (M (hF.mdl 1 b))).hom
              (((F.obj (M (hF.mdl 1 b))).d 1 0).hom (hF.gen 1 b))) = 0 := by
          rw [amMap_zero hF f0 hf0, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
            hf0ε, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, εF.ε_d,
            ModuleCat.hom_zero, LinearMap.zero_apply]
        obtain ⟨z, hz⟩ := hG0.exists_preimage_zero (hF.mdl 1 b) _ hε
        rw [cmElt_succ]
        exact pickPreimage_spec _ _ ⟨z, hz⟩
      exact amMap_comm_of_spec hF f0 0 hspec
  | succ k ih =>
      have hspec : ∀ b : hF.B (k + 2),
          ((G.obj (M (hF.mdl (k + 2) b))).d (k + 2) (k + 1)).hom (cmElt hF f0 (k + 2) b)
            = (amMap hF f0 (k + 1) (M (hF.mdl (k + 2) b))).hom
                (((F.obj (M (hF.mdl (k + 2) b))).d (k + 2) (k + 1)).hom
                  (hF.gen (k + 2) b)) := by
        intro b
        have hcyc : ((G.obj (M (hF.mdl (k + 2) b))).d (k + 1) k).hom
            ((amMap hF f0 (k + 1) (M (hF.mdl (k + 2) b))).hom
              (((F.obj (M (hF.mdl (k + 2) b))).d (k + 2) (k + 1)).hom
                (hF.gen (k + 2) b))) = 0 := by
          have h1 := congrArg (fun u : (F.obj (M (hF.mdl (k + 2) b))).X (k + 1) ⟶
              (G.obj (M (hF.mdl (k + 2) b))).X k => u.hom
              (((F.obj (M (hF.mdl (k + 2) b))).d (k + 2) (k + 1)).hom (hF.gen (k + 2) b)))
            (ih (M (hF.mdl (k + 2) b)))
          simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
          rw [h1, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
            HomologicalComplex.d_comp_d, ModuleCat.hom_zero, LinearMap.zero_apply,
            map_zero]
        obtain ⟨z, hz⟩ := hG.exists_preimage (hF.mdl (k + 2) b) k _ hcyc
        rw [cmElt_succ]
        exact pickPreimage_spec _ _ ⟨z, hz⟩
      exact amMap_comm_of_spec hF f0 (k + 1) hspec

/-- **The acyclic-models theorem (existence half).**  A natural degree-`0` map
compatible with the augmentations extends to a natural chain map. -/
noncomputable def acyclicModelsMap {A : ModuleCat.{0} Λ} (hF : FreeOnModels M Λ F)
    (hG : AcyclicOnModels M Λ G) (εF : Augmentation Λ F A) (εG : Augmentation Λ G A)
    (hG0 : AcyclicZeroOnModels M εG)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0)
    (hf0 : ∀ (X Y : C) (φ : X ⟶ Y), (F.map φ).f 0 ≫ f0 Y = f0 X ≫ (G.map φ).f 0)
    (hf0ε : ∀ X : C, f0 X ≫ εG.ε X = εF.ε X) : F ⟶ G where
  app X :=
    { f := fun k => amMap hF f0 k X
      comm' := by
        rintro i j (rfl : j + 1 = i)
        exact amMap_comm hF hG εF εG hG0 f0 hf0 hf0ε j X }
  naturality X Y φ := by
    apply HomologicalComplex.hom_ext
    intro k
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    exact amMap_naturality hF f0 k φ

/-- The extension really extends: in degree `0` it is the given map. -/
lemma acyclicModelsMap_zero {A : ModuleCat.{0} Λ} (hF : FreeOnModels M Λ F)
    (hG : AcyclicOnModels M Λ G) (εF : Augmentation Λ F A) (εG : Augmentation Λ G A)
    (hG0 : AcyclicZeroOnModels M εG)
    (f0 : ∀ X : C, (F.obj X).X 0 ⟶ (G.obj X).X 0)
    (hf0 : ∀ (X Y : C) (φ : X ⟶ Y), (F.map φ).f 0 ≫ f0 Y = f0 X ≫ (G.map φ).f 0)
    (hf0ε : ∀ X : C, f0 X ≫ εG.ε X = εF.ε X) (X : C) :
    ((acyclicModelsMap hF hG εF εG hG0 f0 hf0 hf0ε).app X).f 0 = f0 X :=
  amMap_zero hF f0 hf0 X

end Existence

end GroupApproximation.CharClass
