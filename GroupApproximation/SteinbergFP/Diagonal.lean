import GroupApproximation.Steinberg.Functoriality
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Data.Matrix.Block
import GroupApproximation.Meta.AxiomGuard

/-!
# The block-diagonal homomorphism `St_I(S) → St_{I × V}(S)`

For each `i : V` the embedding `a ↦ (a, i)` of `I` into `I × V` induces
`indexMap (blockEmb i) : St_I(S) → St_{I × V}(S)`.  Images for different `i` commute, because
their roots live on disjoint index blocks.  Their product is the block-diagonal homomorphism
`diagMap : St_I(S) →* St_{I × V}(S)`, `x_{ab}(r) ↦ ∏_i x_{(a,i),(b,i)}(r)`.

On elementary matrices `diagMap` is `M ↦ blockDiagonal (fun _ ↦ M)`
(`stMatrix_diagMap`).
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

open scoped commutatorElement
open SteinbergGroup

variable {I V S : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Ring S]

/-- `a ↦ (a, i)`. -/
def blockEmb (i : V) : I ↪ I × V :=
  ⟨fun a ↦ (a, i), fun _ _ h ↦ (Prod.mk.inj h).1⟩

omit [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] in
@[simp] theorem blockEmb_apply (i : V) (a : I) : blockEmb (I := I) i a = (a, i) := rfl

section Disjoint

variable {A C B : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] [Fintype B]
  [DecidableEq B]

/-- Images of index embeddings with disjoint ranges commute. -/
theorem commute_indexMap_of_disjoint (e₁ : A ↪ B) (e₂ : C ↪ B) (hd : ∀ a c, e₁ a ≠ e₂ c)
    (g : SteinbergGroup A S) (h : SteinbergGroup C S) :
    Commute (indexMap e₁ g) (indexMap e₂ h) := by
  -- First: every image of `e₁` commutes with every generator image of `e₂`.
  have hgen : ∀ (g : SteinbergGroup A S) (c d : C) (hcd : c ≠ d) (r' : S),
      Commute (indexMap e₁ g) (indexMap e₂ (x c d hcd r')) := by
    intro g c d hcd r'
    have hmem : g ∈ Subgroup.comap (indexMap e₁)
        (Subgroup.centralizer {indexMap e₂ (x c d hcd r')}) := by
      refine PresentedGroup.generated_by _ _ ?_ g
      rintro ⟨a, b, hab, r⟩
      change indexMap e₁ (x a b hab r) ∈ Subgroup.centralizer {indexMap e₂ (x c d hcd r')}
      rw [Subgroup.mem_centralizer_singleton_iff, indexMap_x, indexMap_x]
      exact (x_commute_of_ne _ _ _ _ _ _ (hd b c) (fun e ↦ hd a d e.symm) r r').eq
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hmem
    exact hmem
  have hmem : h ∈ Subgroup.comap (indexMap e₂) (Subgroup.centralizer {indexMap e₁ g}) := by
    refine PresentedGroup.generated_by _ _ ?_ h
    rintro ⟨c, d, hcd, r'⟩
    change indexMap e₂ (x c d hcd r') ∈ Subgroup.centralizer {indexMap e₁ g}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hgen g c d hcd r').eq.symm
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hmem
  exact hmem.symm

end Disjoint

/-- Images of `indexMap (blockEmb i)` and `indexMap (blockEmb k)` commute for `i ≠ k`. -/
theorem commute_indexMap_blockEmb {i k : V} (hik : i ≠ k) (g h : SteinbergGroup I S) :
    Commute (indexMap (blockEmb (I := I) i) g) (indexMap (blockEmb (I := I) k) h) :=
  commute_indexMap_of_disjoint _ _ (fun _ _ e ↦ hik (Prod.mk.inj e).2) g h

/-- The block-diagonal homomorphism `St_I(S) →* St_{I × V}(S)`. -/
def diagMap : SteinbergGroup I S →* SteinbergGroup (I × V) S :=
  (MonoidHom.noncommPiCoprod (fun i : V ↦ indexMap (R := S) (blockEmb (I := I) i))
      (fun _ _ hik g h ↦ commute_indexMap_blockEmb hik g h)).comp
    (Pi.constMonoidHom V (SteinbergGroup I S))

theorem diagMap_apply (g : SteinbergGroup I S) :
    diagMap (V := V) g = Finset.univ.noncommProd (fun i : V ↦ indexMap (blockEmb (I := I) i) g)
      (fun _ _ _ _ hik ↦ commute_indexMap_blockEmb hik g g) := by
  simp only [diagMap, MonoidHom.comp_apply, Pi.constMonoidHom_apply,
    MonoidHom.noncommPiCoprod_apply]
  rfl

/-! ## Compatibility with block-diagonal matrices -/

/-- `g ↦ π(g)` as a matrix. -/
def stMatrix (I S : Type*) [Fintype I] [DecidableEq I] [Ring S] :
    SteinbergGroup I S →* Matrix I I S :=
  (Units.coeHom (Matrix I I S)).comp ((elementaryGroup I S).subtype.comp projection)

@[simp] theorem stMatrix_x (a b : I) (hab : a ≠ b) (r : S) :
    stMatrix I S (x a b hab r) = 1 + Matrix.single a b r := by
  change ((projection (x a b hab r) : (Matrix I I S)ˣ) : Matrix I I S) = _
  rw [projection_x]
  rfl

/-- `K₂` membership read off the matrix. -/
theorem projection_eq_one_iff (g : SteinbergGroup I S) :
    projection g = 1 ↔ stMatrix I S g = 1 := by
  constructor
  · intro h
    change (((projection g : elementaryGroup I S) : (Matrix I I S)ˣ) : Matrix I I S) = 1
    rw [h]
    rfl
  · intro h
    apply Subtype.ext
    apply Units.ext
    exact h

/-- Two monoid homomorphisms out of `St_I(S)` agree once they agree on the generators. -/
theorem hom_ext_of_x {M : Type*} [Monoid M] {φ ψ : SteinbergGroup I S →* M}
    (h : ∀ (a b : I) (hab : a ≠ b) (r : S), φ (x a b hab r) = ψ (x a b hab r)) : φ = ψ := by
  have hU : φ.toHomUnits = ψ.toHomUnits := by
    apply PresentedGroup.ext
    rintro ⟨a, b, hab, r⟩
    apply Units.ext
    exact h a b hab r
  ext g
  have hg := congrArg Units.val (DFunLike.congr_fun hU g)
  simpa only [MonoidHom.coe_toHomUnits] using hg

omit [Fintype I] [Fintype V] in
/-- The single-block entry perturbation, as a block-diagonal matrix. -/
theorem one_add_single_blockEmb (i : V) (a b : I) (r : S) :
    (1 : Matrix (I × V) (I × V) S) + Matrix.single (a, i) (b, i) r =
      Matrix.blockDiagonal (Pi.mulSingle i (1 + Matrix.single a b r)) := by
  ext ⟨a', k⟩ ⟨b', k'⟩
  rw [Matrix.blockDiagonal_apply]
  by_cases hkk : k = k'
  · subst hkk
    rw [if_pos rfl]
    by_cases hki : k = i
    · subst hki
      rw [Pi.mulSingle_eq_same]
      simp [Matrix.one_apply, Matrix.single_apply]
    · rw [Pi.mulSingle_eq_of_ne hki]
      simp [Matrix.one_apply, Ne.symm hki]
  · rw [if_neg hkk, Matrix.add_apply, Matrix.one_apply_ne (fun h ↦ hkk (Prod.mk.inj h).2),
      Matrix.single_apply, if_neg (fun h ↦ hkk ((Prod.mk.inj h.1).2.symm.trans
        (Prod.mk.inj h.2).2)), add_zero]

/-- `g ↦ π(indexMap (blockEmb i) g)` is `g ↦ blockDiagonal (mulSingle i π(g))`. -/
theorem stMatrix_indexMap_blockEmb (i : V) (g : SteinbergGroup I S) :
    stMatrix (I × V) S (indexMap (blockEmb (I := I) i) g) =
      Matrix.blockDiagonal (Pi.mulSingle i (stMatrix I S g)) := by
  have h : (stMatrix (I × V) S).comp (indexMap (blockEmb (I := I) i)) =
      (Matrix.blockDiagonalRingHom I V S).toMonoidHom.comp
        ((MonoidHom.mulSingle (fun _ : V ↦ Matrix I I S) i).comp (stMatrix I S)) := by
    apply hom_ext_of_x
    intro a b hab r
    change stMatrix (I × V) S (indexMap (blockEmb (I := I) i) (x a b hab r)) =
      Matrix.blockDiagonal (Pi.mulSingle i (stMatrix I S (x a b hab r)))
    rw [indexMap_x, stMatrix_x, stMatrix_x]
    exact one_add_single_blockEmb i a b r
  exact DFunLike.congr_fun h g

/-- **Projection of the block-diagonal homomorphism.** -/
theorem stMatrix_diagMap (g : SteinbergGroup I S) :
    stMatrix (I × V) S (diagMap (V := V) g) =
      Matrix.blockDiagonal (fun _ : V ↦ stMatrix I S g) := by
  rw [diagMap_apply, Finset.map_noncommProd]
  simp only [stMatrix_indexMap_blockEmb]
  have hmap := Finset.map_noncommProd Finset.univ
    (fun i : V ↦ Pi.mulSingle i (stMatrix I S g))
    (fun i _ j _ _ ↦ Pi.mulSingle_apply_commute (fun _ : V ↦ stMatrix I S g) i j)
    (Matrix.blockDiagonalRingHom I V S)
  rw [Finset.noncommProd_mulSingle] at hmap
  exact hmap.symm

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.diagMap
#audit_axioms GroupApproximation.SteinbergFP.stMatrix_diagMap
