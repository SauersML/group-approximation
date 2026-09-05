import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The acyclic-models theorem of Eilenberg and MacLane

This file proves, from scratch, the comparison theorem for functors into chain
complexes of modules that is classically called the *method of acyclic models*.

## Statement

Fix a commutative ring `Λ`, a category `C`, and a family of **models**
`M : ι → C`.  For functors `F G : C ⥤ ChainComplex (ModuleCat Λ) ℕ`:

* `F` is **free on the models** (`FreeOnModels`) when there are, in each degree
  `k`, an index type `B k`, an assignment `mdl : B k → ι` of a model to each
  index, and universal elements `gen k b ∈ F(M (mdl k b))_k`, such that for
  **every** object `X` the transported family `(b, φ) ↦ F(φ) (gen k b)`, indexed
  by pairs of an index `b` and a morphism `φ : M (mdl k b) ⟶ X`, is a `Λ`-basis
  of `F(X)_k`.
* `G` is **acyclic on the models** (`AcyclicOnModels`) when every cycle of
  `G(M i)` in a positive degree is a boundary.

The main result `acyclicModelsHomotopy` says: two natural transformations
`f g : F ⟶ G` that agree in degree `0` are *naturally* chain homotopic.  The
homotopy is produced degreewise, and the package `NaturalHomotopy` records both
the naturality of the homotopy operator and the two homotopy identities; the
derived `NaturalHomotopy.homotopy` converts it, at each object, into Mathlib's
`Homotopy`, so that `Homotopy.homologyMap_eq` applies.

## Equivariance is not a separate theorem

The `ℤ/2`-equivariant version, in which the source is free over the group ring
`Λ = R[ℤ/2]` and the target carries an involution, is the present theorem applied
with `Λ` *equal to the group ring*: a complex of `R`-modules carrying a
`G`-action is exactly a complex of `R[G]`-modules, an equivariant map is exactly
an `R[G]`-linear one, and acyclicity means the same for both (kernels and images
do not change).  Nothing below assumes `Λ` is a field, so `Λ = (ZMod 2)[ℤ/2]`,
a commutative ring, is allowed.  This is why `Λ` is kept general and why
acyclicity is stated as an element-level statement about cycles and boundaries
rather than as the vanishing of a homology object.

## Design notes

* The homotopy operator is built from a family of **universal elements**
  `modelElt k b ∈ G(M (mdl k b))_{k+1}`, one for each basis index; it is then
  extended to every object by `Module.Basis.constr`.  Naturality is a formal
  consequence of functoriality (`amHom_naturality`) and holds *before* any of
  the homotopy identities are proved.
* The universal elements are defined by a recursion using `pickPreimage`, a
  classical choice of a boundary preimage which returns `0` when there is none.
  Separating the *definition* from the *proof* that the choice succeeds is what
  makes the induction go through: the invariant that the choice is a genuine
  preimage is established afterwards, simultaneously with the homotopy identity,
  in `amHom_comm`.
-/

universe u v w

namespace GroupApproximation.CharClass

open CategoryTheory CategoryTheory.Limits

/-! ## 1. Assembling a chain homotopy from a degreewise family

Mathlib's `Homotopy` is indexed by *pairs* of degrees, with the components off
the shape required to vanish.  For an `ℕ`-indexed chain complex the only
relevant components are `P.X k ⟶ Q.X (k+1)`; this section repackages such a
family, together with the two homotopy identities, as a `Homotopy`. -/

section Assemble

variable {V : Type u} [Category.{v} V] [Preadditive V] {P Q : ChainComplex V ℕ}

/-- A degreewise family `s k : P.X k ⟶ Q.X (k+1)`, spread over all pairs of
degrees as required by `Homotopy`. -/
def homFamily (s : ∀ k : ℕ, P.X k ⟶ Q.X (k + 1)) (i j : ℕ) : P.X i ⟶ Q.X j :=
  if h : i + 1 = j then s i ≫ eqToHom (congrArg Q.X h) else 0

@[simp]
lemma homFamily_succ (s : ∀ k : ℕ, P.X k ⟶ Q.X (k + 1)) (i : ℕ) :
    homFamily s i (i + 1) = s i := by
  rw [homFamily, dif_pos rfl, eqToHom_refl, Category.comp_id]

lemma homFamily_eq_zero (s : ∀ k : ℕ, P.X k ⟶ Q.X (k + 1)) {i j : ℕ} (h : ¬ i + 1 = j) :
    homFamily s i j = 0 :=
  dif_neg h

/-- Assemble a degreewise family satisfying the two homotopy identities into a
chain homotopy from `e` to `0`. -/
def homotopyOfFamily (e : P ⟶ Q) (s : ∀ k : ℕ, P.X k ⟶ Q.X (k + 1))
    (h0 : e.f 0 = s 0 ≫ Q.d 1 0)
    (hs : ∀ k : ℕ, e.f (k + 1) = P.d (k + 1) k ≫ s k + s (k + 1) ≫ Q.d (k + 2) (k + 1)) :
    Homotopy e 0 where
  hom := homFamily s
  zero i j hij := homFamily_eq_zero s hij
  comm i := by
    rcases i with _ | k
    · have hz : homFamily s 0 0 = (0 : P.X 0 ⟶ Q.X 0) := homFamily_eq_zero s (by omega)
      have hd : dNext (0 : ℕ) (homFamily s) = 0 := by
        dsimp [dNext]
        rw [ChainComplex.next_nat_zero, hz, comp_zero]
      have hp : prevD (0 : ℕ) (homFamily s) = s 0 ≫ Q.d (0 + 1) 0 := by
        rw [prevD_eq (homFamily s) (show (ComplexShape.down ℕ).Rel (0 + 1) 0 from rfl),
          homFamily_succ]
      rw [hd, hp, HomologicalComplex.zero_f_apply, zero_add, add_zero]
      exact h0
    · have hd : dNext (k + 1) (homFamily s) = P.d (k + 1) k ≫ s k := by
        rw [dNext_eq (homFamily s) (show (ComplexShape.down ℕ).Rel (k + 1) k from rfl),
          homFamily_succ]
      have hp : prevD (k + 1) (homFamily s)
          = s (k + 1) ≫ Q.d (k + 1 + 1) (k + 1) := by
        rw [prevD_eq (homFamily s)
          (show (ComplexShape.down ℕ).Rel (k + 1 + 1) (k + 1) from rfl), homFamily_succ]
      rw [hd, hp, HomologicalComplex.zero_f_apply, add_zero]
      exact hs k

end Assemble

/-! ## 2. Freeness and acyclicity on models -/

section Models

variable {C : Type u} [Category.{v} C] {ι : Type w}

/-- **Freeness on models.** `F` is free on the models `M` when each `F(X)_k` has
a `Λ`-basis indexed by pairs (basis index `b`, morphism `M (mdl k b) ⟶ X`), the
basis vector at `(b, φ)` being the image of the universal element `gen k b`
under `F(φ)`. -/
structure FreeOnModels (M : ι → C) (Λ : Type) [CommRing Λ]
    (F : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ) where
  /-- The type of basis indices in degree `k`. -/
  B : ℕ → Type v
  /-- The model over which a basis index lives. -/
  mdl : ∀ k : ℕ, B k → ι
  /-- The universal element attached to a basis index. -/
  gen : ∀ (k : ℕ) (b : B k), (F.obj (M (mdl k b))).X k
  /-- The transported family is a basis of `F(X)_k`. -/
  basis : ∀ (X : C) (k : ℕ),
    Module.Basis (Σ b : B k, (M (mdl k b) ⟶ X)) Λ ((F.obj X).X k)
  /-- The basis vectors are the transported universal elements. -/
  basis_apply : ∀ (X : C) (k : ℕ) (b : B k) (φ : M (mdl k b) ⟶ X),
    basis X k ⟨b, φ⟩ = ((F.map φ).f k).hom (gen k b)

/-- **Acyclicity on models.** Every cycle of `G(M i)` in a positive degree is a
boundary. -/
structure AcyclicOnModels (M : ι → C) (Λ : Type) [CommRing Λ]
    (G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ) : Prop where
  /-- Positive-degree cycles over a model are boundaries. -/
  exists_preimage : ∀ (i : ι) (k : ℕ) (y : (G.obj (M i)).X (k + 1)),
    ((G.obj (M i)).d (k + 1) k).hom y = 0 →
    ∃ z : (G.obj (M i)).X (k + 2), ((G.obj (M i)).d (k + 2) (k + 1)).hom z = y

end Models

/-! ## 3. The construction -/

section Construction

variable {C : Type u} [Category.{v} C] {ι : Type w} {M : ι → C}
variable {Λ : Type} [CommRing Λ]
variable {F G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ}

/-- A classically chosen preimage of `y` under `d`, or `0` if none exists. -/
noncomputable def pickPreimage {A B : ModuleCat.{0} Λ} (d : A ⟶ B) (y : B) : A :=
  if h : ∃ z : A, d.hom z = y then h.choose else 0

lemma pickPreimage_spec {A B : ModuleCat.{0} Λ} (d : A ⟶ B) (y : B)
    (h : ∃ z : A, d.hom z = y) : d.hom (pickPreimage d y) = y := by
  rw [pickPreimage, dif_pos h]
  exact h.choose_spec

/-- The homotopy operator in degree `k` determined by a family of universal
elements, one for each basis index. -/
noncomputable def modelHom (hF : FreeOnModels M Λ F) (k : ℕ)
    (z : ∀ b : hF.B k, (G.obj (M (hF.mdl k b))).X (k + 1)) (X : C) :
    (F.obj X).X k ⟶ (G.obj X).X (k + 1) :=
  ModuleCat.ofHom ((hF.basis X k).constr Λ fun p => ((G.map p.2).f (k + 1)).hom (z p.1))

lemma modelHom_basis (hF : FreeOnModels M Λ F) (k : ℕ)
    (z : ∀ b : hF.B k, (G.obj (M (hF.mdl k b))).X (k + 1)) (X : C)
    (b : hF.B k) (φ : M (hF.mdl k b) ⟶ X) :
    (modelHom hF k z X).hom (hF.basis X k ⟨b, φ⟩) = ((G.map φ).f (k + 1)).hom (z b) := by
  rw [modelHom, ModuleCat.hom_ofHom, Module.Basis.constr_basis]

/-- The universal elements of the homotopy, defined by recursion on the degree:
in degree `0` there is nothing to do, and in degree `k+1` one chooses a boundary
preimage of the obstruction built from the previous degree. -/
noncomputable def modelElt (hF : FreeOnModels M Λ F) (f g : F ⟶ G) :
    ∀ (k : ℕ) (b : hF.B k), (G.obj (M (hF.mdl k b))).X (k + 1)
  | 0, _ => 0
  | k + 1, b =>
      pickPreimage ((G.obj (M (hF.mdl (k + 1) b))).d (k + 2) (k + 1))
        (((f.app (M (hF.mdl (k + 1) b))).f (k + 1)).hom (hF.gen (k + 1) b)
          - ((g.app (M (hF.mdl (k + 1) b))).f (k + 1)).hom (hF.gen (k + 1) b)
          - (modelHom hF k (fun c => modelElt hF f g k c) (M (hF.mdl (k + 1) b))).hom
              (((F.obj (M (hF.mdl (k + 1) b))).d (k + 1) k).hom (hF.gen (k + 1) b)))

/-- The natural homotopy operator produced by the acyclic-models construction. -/
noncomputable def amHom (hF : FreeOnModels M Λ F) (f g : F ⟶ G) (k : ℕ) (X : C) :
    (F.obj X).X k ⟶ (G.obj X).X (k + 1) :=
  modelHom hF k (fun b => modelElt hF f g k b) X

/-- The obstruction element in degree `k+1` over the model of `b`: the failure of
the homotopy identity for the universal element, which acyclicity turns into a
boundary. -/
noncomputable def amObstruction (hF : FreeOnModels M Λ F) (f g : F ⟶ G) (k : ℕ)
    (b : hF.B (k + 1)) : (G.obj (M (hF.mdl (k + 1) b))).X (k + 1) :=
  ((f.app (M (hF.mdl (k + 1) b))).f (k + 1)).hom (hF.gen (k + 1) b)
    - ((g.app (M (hF.mdl (k + 1) b))).f (k + 1)).hom (hF.gen (k + 1) b)
    - (amHom hF f g k (M (hF.mdl (k + 1) b))).hom
        (((F.obj (M (hF.mdl (k + 1) b))).d (k + 1) k).hom (hF.gen (k + 1) b))

lemma modelElt_succ (hF : FreeOnModels M Λ F) (f g : F ⟶ G) (k : ℕ) (b : hF.B (k + 1)) :
    modelElt hF f g (k + 1) b
      = pickPreimage ((G.obj (M (hF.mdl (k + 1) b))).d (k + 2) (k + 1))
          (amObstruction hF f g k b) := by
  rw [amObstruction, amHom, modelElt]

lemma amHom_basis (hF : FreeOnModels M Λ F) (f g : F ⟶ G) (k : ℕ) (X : C)
    (b : hF.B k) (φ : M (hF.mdl k b) ⟶ X) :
    (amHom hF f g k X).hom (hF.basis X k ⟨b, φ⟩)
      = ((G.map φ).f (k + 1)).hom (modelElt hF f g k b) :=
  modelHom_basis hF k _ X b φ

/-- **Naturality of the homotopy operator.**  This holds by construction, before
any homotopy identity is available. -/
lemma amHom_naturality (hF : FreeOnModels M Λ F) (f g : F ⟶ G) (k : ℕ)
    {X Y : C} (φ : X ⟶ Y) :
    (F.map φ).f k ≫ amHom hF f g k Y = amHom hF f g k X ≫ (G.map φ).f (k + 1) := by
  apply ModuleCat.hom_ext
  apply (hF.basis X k).ext
  rintro ⟨b, ψ⟩
  have hFcomp : ((F.map φ).f k).hom (hF.basis X k ⟨b, ψ⟩) = hF.basis Y k ⟨b, ψ ≫ φ⟩ := by
    rw [hF.basis_apply X k b ψ, hF.basis_apply Y k b (ψ ≫ φ), F.map_comp,
      HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hGcomp : ((G.map (ψ ≫ φ)).f (k + 1)).hom (modelElt hF f g k b)
      = ((G.map φ).f (k + 1)).hom (((G.map ψ).f (k + 1)).hom (modelElt hF f g k b)) := by
    rw [G.map_comp, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    hFcomp, amHom_basis, amHom_basis, hGcomp]

/-- In degree `0` the homotopy operator vanishes. -/
lemma amHom_zero (hF : FreeOnModels M Λ F) (f g : F ⟶ G) (X : C) :
    amHom hF f g 0 X = 0 := by
  apply ModuleCat.hom_ext
  apply (hF.basis X 0).ext
  rintro ⟨b, φ⟩
  rw [amHom_basis, modelElt, map_zero, ModuleCat.hom_zero, LinearMap.zero_apply]

/-- The `d ∘ s` half of the homotopy identity, as a degreewise family. -/
noncomputable def amPrev (hF : FreeOnModels M Λ F) (f g : F ⟶ G) :
    ∀ (k : ℕ) (X : C), (F.obj X).X k ⟶ (G.obj X).X k
  | 0, _ => 0
  | k + 1, X => (F.obj X).d (k + 1) k ≫ amHom hF f g k X

lemma d_comp_amPrev (hF : FreeOnModels M Λ F) (f g : F ⟶ G) (k : ℕ) (X : C) :
    (F.obj X).d (k + 1) k ≫ amPrev hF f g k X = 0 := by
  rcases k with _ | j
  · rw [amPrev, comp_zero]
  · rw [amPrev, ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]

/-- The obstruction is a cycle.  This is the only place where the inductive
hypothesis of the main induction is used. -/
lemma d_comp_obstruction (hF : FreeOnModels M Λ F) (f g : F ⟶ G) (k : ℕ)
    (ih : ∀ Z : C, (f.app Z).f k - (g.app Z).f k
      = amPrev hF f g k Z + amHom hF f g k Z ≫ (G.obj Z).d (k + 1) k)
    {Y : C} (γ : (F.obj Y).X (k + 1)) :
    ((G.obj Y).d (k + 1) k).hom
        (((f.app Y).f (k + 1)).hom γ - ((g.app Y).f (k + 1)).hom γ
          - (amHom hF f g k Y).hom (((F.obj Y).d (k + 1) k).hom γ)) = 0 := by
  have hf : ((G.obj Y).d (k + 1) k).hom (((f.app Y).f (k + 1)).hom γ)
      = ((f.app Y).f k).hom (((F.obj Y).d (k + 1) k).hom γ) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, (f.app Y).comm (k + 1) k,
      ModuleCat.hom_comp, LinearMap.comp_apply]
  have hg : ((G.obj Y).d (k + 1) k).hom (((g.app Y).f (k + 1)).hom γ)
      = ((g.app Y).f k).hom (((F.obj Y).d (k + 1) k).hom γ) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, (g.app Y).comm (k + 1) k,
      ModuleCat.hom_comp, LinearMap.comp_apply]
  have hprev : (amPrev hF f g k Y).hom (((F.obj Y).d (k + 1) k).hom γ) = 0 := by
    have h2 := congrArg (fun u : (F.obj Y).X (k + 1) ⟶ (G.obj Y).X k => u.hom γ)
      (d_comp_amPrev hF f g k Y)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h2
  have hs : ((G.obj Y).d (k + 1) k).hom
      ((amHom hF f g k Y).hom (((F.obj Y).d (k + 1) k).hom γ))
      = ((f.app Y).f k).hom (((F.obj Y).d (k + 1) k).hom γ)
        - ((g.app Y).f k).hom (((F.obj Y).d (k + 1) k).hom γ) := by
    have h3 := congrArg (fun u : (F.obj Y).X k ⟶ (G.obj Y).X k =>
      u.hom (((F.obj Y).d (k + 1) k).hom γ)) (ih Y)
    simp only [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_add,
      LinearMap.add_apply, ModuleCat.hom_comp, LinearMap.comp_apply] at h3
    rw [hprev, zero_add] at h3
    exact h3.symm
  rw [map_sub, map_sub, hf, hg, hs]
  abel

/-- The successor step of the homotopy identity, checked at a transported
universal element. -/
lemma amHom_step (hF : FreeOnModels M Λ F) (f g : F ⟶ G) (k : ℕ)
    {Y X : C} (γ : (F.obj Y).X (k + 1)) (φ : Y ⟶ X) (z : (G.obj Y).X (k + 2))
    (hz : ((G.obj Y).d (k + 2) (k + 1)).hom z
        = ((f.app Y).f (k + 1)).hom γ - ((g.app Y).f (k + 1)).hom γ
          - (amHom hF f g k Y).hom (((F.obj Y).d (k + 1) k).hom γ)) :
    ((f.app X).f (k + 1)).hom (((F.map φ).f (k + 1)).hom γ)
        - ((g.app X).f (k + 1)).hom (((F.map φ).f (k + 1)).hom γ)
      = (amPrev hF f g (k + 1) X).hom (((F.map φ).f (k + 1)).hom γ)
        + ((G.obj X).d (k + 2) (k + 1)).hom (((G.map φ).f (k + 2)).hom z) := by
  have hfnat : ((f.app X).f (k + 1)).hom (((F.map φ).f (k + 1)).hom γ)
      = ((G.map φ).f (k + 1)).hom (((f.app Y).f (k + 1)).hom γ) := by
    have h2 := HomologicalComplex.congr_hom (f.naturality φ) (k + 1)
    simp only [HomologicalComplex.comp_f] at h2
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, h2, ModuleCat.hom_comp,
      LinearMap.comp_apply]
  have hgnat : ((g.app X).f (k + 1)).hom (((F.map φ).f (k + 1)).hom γ)
      = ((G.map φ).f (k + 1)).hom (((g.app Y).f (k + 1)).hom γ) := by
    have h2 := HomologicalComplex.congr_hom (g.naturality φ) (k + 1)
    simp only [HomologicalComplex.comp_f] at h2
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, h2, ModuleCat.hom_comp,
      LinearMap.comp_apply]
  have hdnat : ((F.obj X).d (k + 1) k).hom (((F.map φ).f (k + 1)).hom γ)
      = ((F.map φ).f k).hom (((F.obj Y).d (k + 1) k).hom γ) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, (F.map φ).comm (k + 1) k,
      ModuleCat.hom_comp, LinearMap.comp_apply]
  have hprevterm : (amPrev hF f g (k + 1) X).hom (((F.map φ).f (k + 1)).hom γ)
      = ((G.map φ).f (k + 1)).hom
          ((amHom hF f g k Y).hom (((F.obj Y).d (k + 1) k).hom γ)) := by
    rw [amPrev, ModuleCat.hom_comp, LinearMap.comp_apply, hdnat, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, amHom_naturality, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hdz : ((G.obj X).d (k + 2) (k + 1)).hom (((G.map φ).f (k + 2)).hom z)
      = ((G.map φ).f (k + 1)).hom (((G.obj Y).d (k + 2) (k + 1)).hom z) := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, (G.map φ).comm (k + 2) (k + 1),
      ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [hfnat, hgnat, hprevterm, hdz, hz, map_sub, map_sub]
  abel

/-- **The homotopy identity**, proved by induction on the degree simultaneously
with the fact that the classically chosen preimages really are preimages. -/
lemma amHom_comm (hF : FreeOnModels M Λ F) (hG : AcyclicOnModels M Λ G) (f g : F ⟶ G)
    (h0 : ∀ X : C, (f.app X).f 0 = (g.app X).f 0) :
    ∀ (k : ℕ) (X : C), (f.app X).f k - (g.app X).f k
      = amPrev hF f g k X + amHom hF f g k X ≫ (G.obj X).d (k + 1) k := by
  intro k
  induction k with
  | zero =>
      intro X
      rw [h0 X, sub_self, amPrev, amHom_zero, zero_comp, add_zero]
  | succ k ih =>
      have hspec : ∀ b : hF.B (k + 1),
          ((G.obj (M (hF.mdl (k + 1) b))).d (k + 2) (k + 1)).hom
              (modelElt hF f g (k + 1) b)
            = amObstruction hF f g k b := by
        intro b
        have hcyc : ((G.obj (M (hF.mdl (k + 1) b))).d (k + 1) k).hom
            (amObstruction hF f g k b) = 0 :=
          d_comp_obstruction hF f g k ih (hF.gen (k + 1) b)
        obtain ⟨z, hz⟩ := hG.exists_preimage (hF.mdl (k + 1) b) k _ hcyc
        rw [modelElt_succ]
        exact pickPreimage_spec _ _ ⟨z, hz⟩
      intro X
      apply ModuleCat.hom_ext
      apply (hF.basis X (k + 1)).ext
      rintro ⟨b, φ⟩
      have hb := hF.basis_apply X (k + 1) b φ
      have hstep := amHom_step hF f g k (Y := M (hF.mdl (k + 1) b)) (hF.gen (k + 1) b) φ
        (modelElt hF f g (k + 1) b) (by rw [hspec b, amObstruction])
      rw [ModuleCat.hom_sub, LinearMap.sub_apply, ModuleCat.hom_add, LinearMap.add_apply,
        ModuleCat.hom_comp, LinearMap.comp_apply, amHom_basis, hb]
      exact hstep

end Construction

/-! ## 4. The theorem -/

section Theorem

variable {C : Type u} [Category.{v} C] {ι : Type w} {M : ι → C}
variable {Λ : Type} [CommRing Λ]
variable {F G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ}

/-- A natural chain homotopy between two natural transformations of functors into
chain complexes: a degreewise operator, natural in the object, satisfying the two
homotopy identities. -/
structure NaturalHomotopy (F G : C ⥤ ChainComplex (ModuleCat.{0} Λ) ℕ) (f g : F ⟶ G) where
  /-- The homotopy operator. -/
  s : ∀ (k : ℕ) (X : C), (F.obj X).X k ⟶ (G.obj X).X (k + 1)
  /-- Naturality of the homotopy operator. -/
  naturality : ∀ (k : ℕ) (X Y : C) (φ : X ⟶ Y),
    (F.map φ).f k ≫ s k Y = s k X ≫ (G.map φ).f (k + 1)
  /-- The homotopy identity in degree `0`. -/
  comm_zero : ∀ X : C, (f.app X).f 0 - (g.app X).f 0 = s 0 X ≫ (G.obj X).d 1 0
  /-- The homotopy identity in positive degrees. -/
  comm_succ : ∀ (k : ℕ) (X : C), (f.app X).f (k + 1) - (g.app X).f (k + 1)
    = (F.obj X).d (k + 1) k ≫ s k X + s (k + 1) X ≫ (G.obj X).d (k + 2) (k + 1)

/-- A natural homotopy gives, at each object, a `Homotopy` in Mathlib's sense. -/
noncomputable def NaturalHomotopy.homotopy {f g : F ⟶ G} (h : NaturalHomotopy F G f g)
    (X : C) : Homotopy (f.app X) (g.app X) :=
  Homotopy.equivSubZero.symm
    (homotopyOfFamily (f.app X - g.app X) (fun k => h.s k X)
      (by rw [HomologicalComplex.sub_f_apply]; exact h.comm_zero X)
      (fun k => by rw [HomologicalComplex.sub_f_apply]; exact h.comm_succ k X))

/-- **The acyclic-models theorem (uniqueness half).**  If `F` is free on the
models and `G` is acyclic on the models, then any two natural transformations
`F ⟶ G` agreeing in degree `0` are naturally chain homotopic. -/
noncomputable def acyclicModelsHomotopy (hF : FreeOnModels M Λ F)
    (hG : AcyclicOnModels M Λ G) (f g : F ⟶ G)
    (h0 : ∀ X : C, (f.app X).f 0 = (g.app X).f 0) : NaturalHomotopy F G f g where
  s := amHom hF f g
  naturality k _ _ φ := amHom_naturality hF f g k φ
  comm_zero X := by
    have h := amHom_comm hF hG f g h0 0 X
    rwa [amPrev, zero_add] at h
  comm_succ k X := by
    have h := amHom_comm hF hG f g h0 (k + 1) X
    rwa [amPrev] at h

/-- The homotopy of `acyclicModelsHomotopy` at a single object. -/
noncomputable def acyclicModelsHomotopyApp (hF : FreeOnModels M Λ F)
    (hG : AcyclicOnModels M Λ G) (f g : F ⟶ G)
    (h0 : ∀ X : C, (f.app X).f 0 = (g.app X).f 0) (X : C) :
    Homotopy (f.app X) (g.app X) :=
  (acyclicModelsHomotopy hF hG f g h0).homotopy X

end Theorem

end GroupApproximation.CharClass
