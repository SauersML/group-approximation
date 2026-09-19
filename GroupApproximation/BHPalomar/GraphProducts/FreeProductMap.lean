/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.CoprodI

/-!
# Two tools for the graph-product embedding

* `CoprodI.lift_of_comp_injective`: a free product of injective homomorphisms is injective.
  The proof maps reduced words letter by letter, so it uses the normal form theorem for free
  products (`Monoid.CoprodI.Word.equiv`) and nothing else.
* `autOfEnd`: a family of endomorphisms of `P` indexed by a group, composing like the group,
  is a homomorphism into `MulAut P`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace GroupApproximation.BHPalomar.GraphProducts

open Monoid Monoid.CoprodI

section WordMap

variable {ι : Type*} {M N : ι → Type*} [∀ i, Monoid (M i)] [∀ i, Monoid (N i)]

/-- Map a reduced word letter by letter along injective homomorphisms. -/
def wordMap (f : ∀ i, M i →* N i) (hf : ∀ i, Function.Injective (f i)) (w : Word M) :
    Word N where
  toList := w.toList.map fun l => ⟨l.1, f l.1 l.2⟩
  ne_one := by
    intro l hl
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl
    intro h
    exact w.ne_one l0 hl0 (hf l0.1 (by rw [map_one]; exact h))
  chain_ne := (List.isChain_map _).2 w.chain_ne

theorem wordMap_prod (f : ∀ i, M i →* N i) (hf : ∀ i, Function.Injective (f i)) (w : Word M) :
    (wordMap f hf w).prod = CoprodI.lift (fun i => (of : N i →* CoprodI N).comp (f i)) w.prod := by
  simp only [Word.prod, wordMap, map_list_prod, List.map_map]
  congr 1

theorem wordMap_injective (f : ∀ i, M i →* N i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (wordMap f hf) := by
  intro w₁ w₂ h
  have hl : w₁.toList.map (fun l => (⟨l.1, f l.1 l.2⟩ : Σ i, N i)) =
      w₂.toList.map (fun l => (⟨l.1, f l.1 l.2⟩ : Σ i, N i)) :=
    congrArg Word.toList h
  have hinj : Function.Injective (fun l : Σ i, M i => (⟨l.1, f l.1 l.2⟩ : Σ i, N i)) := by
    rintro ⟨i, m⟩ ⟨j, n⟩ hij
    simp only [Sigma.mk.inj_iff] at hij
    obtain ⟨rfl, hmn⟩ := hij
    rw [hf _ (eq_of_heq hmn)]
  exact Word.ext (List.map_injective_iff.mpr hinj hl)

/-- **A free product of injective homomorphisms is injective.** -/
theorem lift_of_comp_injective (f : ∀ i, M i →* N i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (CoprodI.lift fun i => (of : N i →* CoprodI N).comp (f i)) := by
  classical
  intro a b hab
  have ha : (Word.equiv a).prod = a := Word.equiv.symm_apply_apply a
  have hb : (Word.equiv b).prod = b := Word.equiv.symm_apply_apply b
  have h1 : (wordMap f hf (Word.equiv a)).prod = (wordMap f hf (Word.equiv b)).prod := by
    rw [wordMap_prod, wordMap_prod, ha, hb, hab]
  have h2 : wordMap f hf (Word.equiv a) = wordMap f hf (Word.equiv b) :=
    Word.equiv.symm.injective (show Word.equiv.symm (wordMap f hf (Word.equiv a)) =
      Word.equiv.symm (wordMap f hf (Word.equiv b)) from h1)
  have h3 : Word.equiv a = Word.equiv b := wordMap_injective f hf h2
  exact Word.equiv.injective h3

end WordMap

section AutOfEnd

variable {G P : Type*} [Group G] [Group P]

/-- A family of endomorphisms of `P`, indexed by a group and composing like it, as a
homomorphism into `MulAut P`. -/
def autOfEnd (e : G → P →* P) (he : ∀ a b, e (a * b) = (e a).comp (e b))
    (h1 : e 1 = MonoidHom.id P) : G →* MulAut P :=
  MonoidHom.mk'
    (fun g => MonoidHom.toMulEquiv (e g) (e g⁻¹) (by rw [← he, inv_mul_cancel, h1])
      (by rw [← he, mul_inv_cancel, h1]))
    (fun a b => MulEquiv.ext fun p => by
      show e (a * b) p = e a (e b p)
      rw [he]
      rfl)

@[simp]
theorem autOfEnd_apply (e : G → P →* P) (he : ∀ a b, e (a * b) = (e a).comp (e b))
    (h1 : e 1 = MonoidHom.id P) (g : G) (p : P) : autOfEnd e he h1 g p = e g p :=
  rfl

end AutOfEnd

end GroupApproximation.BHPalomar.GraphProducts
