import Mathlib.GroupTheory.PushoutI

/-!
# Injective maps between amalgamated free products

This file proves the normal-form lemma needed to place a free-lamp amalgam
inside a symmetric double.  The statement is a group-theoretic version of the
standard Bass--Serre normal-form argument: factor embeddings induce an
embedding of amalgams when they reflect membership in the edge group.

The proof is internal to Lean and uses `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`
from Mathlib (Chris Hughes, following Chiswell's lecture notes).
-/

namespace GroupApproximation

open Monoid

universe uι uH uG uG'

namespace PushoutEmbedding

variable {ι : Type uι} {H : Type uH}
  {G : ι → Type uG} {G' : ι → Type uG'}
  [Group H] [∀ i, Group (G i)] [∀ i, Group (G' i)]

/-- Map a reduced coproduct word factor by factor. -/
def wordMap (f : ∀ i, G i →* G' i) (hf : ∀ i, Function.Injective (f i))
    (w : CoprodI.Word G) : CoprodI.Word G' where
  toList := w.toList.map fun l ↦ ⟨l.1, f l.1 l.2⟩
  ne_one := by
    intro l hl
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
    exact fun h ↦ w.ne_one l' hl' ((hf l'.1) (by simpa using h))
  chain_ne := by
    rw [List.isChain_map]
    simpa using w.chain_ne

@[simp]
theorem wordMap_toList (f : ∀ i, G i →* G' i)
    (hf : ∀ i, Function.Injective (f i)) (w : CoprodI.Word G) :
    (wordMap f hf w).toList = w.toList.map fun l ↦ ⟨l.1, f l.1 l.2⟩ := rfl

/-- The product represented by `wordMap` is the image of the original
coproduct product. -/
theorem wordMap_prod (f : ∀ i, G i →* G' i)
    (hf : ∀ i, Function.Injective (f i)) (w : CoprodI.Word G) :
    (wordMap f hf w).prod =
      CoprodI.lift (fun i ↦ (CoprodI.of : G' i →* CoprodI G').comp (f i)) w.prod := by
  simp only [CoprodI.Word.prod, wordMap, map_list_prod]
  induction w.toList with
  | nil => rfl
  | cons l ls ih =>
      rcases l with ⟨i, g⟩
      simp only [List.map_cons, List.prod_cons]
      rw [ih]
      simp

/-- The homomorphism between pushouts induced by a commuting family of
factor homomorphisms. -/
def map (φ : ∀ i, H →* G i) (ψ : ∀ i, H →* G' i)
    (f : ∀ i, G i →* G' i) (hcomm : ∀ i, (f i).comp (φ i) = ψ i) :
    PushoutI φ →* PushoutI ψ :=
  PushoutI.lift
    (fun i ↦ (PushoutI.of (φ := ψ) i).comp (f i))
    (PushoutI.base ψ)
    (fun i ↦ by
      rw [MonoidHom.comp_assoc, hcomm i, PushoutI.of_comp_eq_base])

@[simp]
theorem map_of (φ : ∀ i, H →* G i) (ψ : ∀ i, H →* G' i)
    (f : ∀ i, G i →* G' i) (hcomm : ∀ i, (f i).comp (φ i) = ψ i)
    (i : ι) (g : G i) :
    map φ ψ f hcomm (PushoutI.of (φ := φ) i g) =
      PushoutI.of (φ := ψ) i (f i g) := by
  simp [map]

@[simp]
theorem map_base (φ : ∀ i, H →* G i) (ψ : ∀ i, H →* G' i)
    (f : ∀ i, G i →* G' i) (hcomm : ∀ i, (f i).comp (φ i) = ψ i)
    (h : H) :
    map φ ψ f hcomm (PushoutI.base φ h) = PushoutI.base ψ h := by
  simp [map]

theorem map_ofCoprodI_prod (φ : ∀ i, H →* G i) (ψ : ∀ i, H →* G' i)
    (f : ∀ i, G i →* G' i) (hf : ∀ i, Function.Injective (f i))
    (hcomm : ∀ i, (f i).comp (φ i) = ψ i) (w : CoprodI.Word G) :
    map φ ψ f hcomm (PushoutI.ofCoprodI w.prod) =
      PushoutI.ofCoprodI (wordMap f hf w).prod := by
  rw [wordMap_prod]
  induction w.prod using CoprodI.induction_on with
  | one => simp
  | of i g => simp [map]
  | mul x y hx hy => simp [hx, hy]

/-- A normal word is reduced after forgetting its chosen transversal. -/
theorem normalWord_reduced (φ : ∀ i, H →* G i)
    (d : PushoutI.NormalWord.Transversal φ) (w : PushoutI.NormalWord d) :
    PushoutI.Reduced φ w.toWord := by
  intro l hl hrange
  have hset : l.2 ∈ d.set l.1 := w.normalized l.1 l.2 hl
  have hsnd_self : (((d.compl l.1).equiv l.2).2 : G l.1) = l.2 :=
    ((d.compl l.1).equiv_snd_eq_self_iff_mem (Subgroup.one_mem _)).2 hset
  have hsnd_one : (((d.compl l.1).equiv l.2).2 : G l.1) = 1 :=
    ((d.compl l.1).coe_equiv_snd_eq_one_iff_mem (d.one_mem l.1)).2 hrange
  exact w.ne_one l hl (hsnd_self.symm.trans hsnd_one)

/-- **Bass--Serre embedding lemma.**  Factorwise injections induce an
injection of amalgamated free products provided no new factor element falls
into the target edge group. -/
theorem map_injective_of_reflects_range
    (φ : ∀ i, H →* G i) (ψ : ∀ i, H →* G' i)
    (f : ∀ i, G i →* G' i)
    (hφ : ∀ i, Function.Injective (φ i))
    (hψ : ∀ i, Function.Injective (ψ i))
    (hf : ∀ i, Function.Injective (f i))
    (hcomm : ∀ i, (f i).comp (φ i) = ψ i)
    (hreflect : ∀ i g, f i g ∈ (ψ i).range → g ∈ (φ i).range) :
    Function.Injective (map φ ψ f hcomm) := by
  classical
  apply (injective_iff_map_eq_one (map φ ψ f hcomm)).2
  intro x hx
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty φ hφ
  let w : PushoutI.NormalWord d := PushoutI.NormalWord.equiv x
  have hxprod : w.prod = x := (PushoutI.NormalWord.equiv (d := d)).symm_apply_apply x
  have hredSource : PushoutI.Reduced φ w.toWord := normalWord_reduced φ d w
  have hredTarget : PushoutI.Reduced ψ (wordMap f hf w.toWord) := by
    intro l hl
    obtain ⟨l', hl', heq⟩ := List.mem_map.mp hl
    cases heq
    exact fun hrange ↦ hredSource l' hl' (hreflect l'.1 l'.2 hrange)
  have hwordRange : PushoutI.ofCoprodI (wordMap f hf w.toWord).prod ∈
      (PushoutI.base ψ).range := by
    refine ⟨w.head⁻¹, ?_⟩
    have hprodImage :
        map φ ψ f hcomm w.prod =
          PushoutI.base ψ w.head *
            PushoutI.ofCoprodI (wordMap f hf w.toWord).prod := by
      rw [PushoutI.NormalWord.prod, map_mul, map_base,
        map_ofCoprodI_prod φ ψ f hf hcomm]
    rw [hxprod, hx] at hprodImage
    calc
      PushoutI.base ψ w.head⁻¹ = (PushoutI.base ψ w.head)⁻¹ * 1 := by simp
      _ = (PushoutI.base ψ w.head)⁻¹ *
          (PushoutI.base ψ w.head *
            PushoutI.ofCoprodI (wordMap f hf w.toWord).prod) :=
        congrArg (fun z ↦ (PushoutI.base ψ w.head)⁻¹ * z) hprodImage
      _ = PushoutI.ofCoprodI (wordMap f hf w.toWord).prod := by simp
  have hempty := hredTarget.eq_empty_of_mem_range hψ hwordRange
  have hsourceEmpty : w.toWord = .empty := by
    apply CoprodI.Word.ext
    have hlist := congrArg CoprodI.Word.toList hempty
    simpa [wordMap, CoprodI.Word.empty] using hlist
  have hxbase : x = PushoutI.base φ w.head := by
    rw [← hxprod, PushoutI.NormalWord.prod, hsourceEmpty]
    simp
  have hhead : w.head = 1 := by
    apply (PushoutI.base_injective hψ)
    have : PushoutI.base ψ w.head = 1 := by
      rw [← map_base φ ψ f hcomm, ← hxbase, hx]
    simpa using this
  rw [hxbase, hhead, map_one]

end PushoutEmbedding

end GroupApproximation
