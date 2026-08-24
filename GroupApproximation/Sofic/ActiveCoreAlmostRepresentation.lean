import GroupApproximation.Sofic.FiniteOrderRankMass
import GroupApproximation.Sofic.InvolutionCollapseProfile

/-!
# Active-core almost representations

This file turns a finite packet of ambient unitary sequences into an
operator-norm almost representation on the packet's active cores.  The only
input about the ambient sequence is semantic: two generator words evaluating
to the same group element become operator-norm close.  The active-core word
comparison then transfers that convergence without loss.
-/

namespace GroupApproximation
namespace ActiveCoreAlmostRepresentation

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {G : Type} {Y : ℕ → Type*} [Group G]

/-- Replace an element of a symmetric generating finset by its subtype index.
The fallback is unreachable on the chosen words but makes this a total map. -/
noncomputable def generatorIndex (S : Finset G) (i₀ : S) (g : G) : S := by
  classical
  exact if hg : g ∈ S then ⟨g, hg⟩ else i₀

omit [Group G] in
@[simp] theorem generatorIndex_of_mem (S : Finset G) (i₀ : S)
    {g : G} (hg : g ∈ S) : (generatorIndex S i₀ g : G) = g := by
  classical
  simp [generatorIndex, hg]

/-- A chosen word in a finite symmetric generating set, with the marked
generator represented by the literal one-letter word. -/
noncomputable def chosenGeneratorWord (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (a : G) (i₀ : S) (_hi₀ : (i₀ : G) = a)
    (g : G) : List S := by
  classical
  exact if hga : g = a then [i₀]
    else (Classical.choose
      (InvolutionCollapseProfile.exists_word S hgen hsymm g)).map
        (generatorIndex S i₀)

theorem chosenGeneratorWord_value (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (a : G) (i₀ : S) (hi₀ : (i₀ : G) = a)
    (g : G) :
    ((chosenGeneratorWord S hgen hsymm a i₀ hi₀ g).map
      fun i : S ↦ (i : G)).prod = g := by
  classical
  by_cases hga : g = a
  · subst g
    simp [chosenGeneratorWord, hi₀]
  · rw [chosenGeneratorWord, dif_neg hga, List.map_map]
    obtain ⟨hall, hprod⟩ := Classical.choose_spec
      (InvolutionCollapseProfile.exists_word S hgen hsymm g)
    let l := Classical.choose
      (InvolutionCollapseProfile.exists_word S hgen hsymm g)
    have hall' : ∀ x ∈ l, x ∈ S := by simpa [l] using hall
    have hmap : l.map ((fun i : S ↦ (i : G)) ∘ generatorIndex S i₀) = l := by
      have hc : l.map ((fun i : S ↦ (i : G)) ∘ generatorIndex S i₀) =
          l.map id := List.map_congr_left fun x hx ↦
        generatorIndex_of_mem S i₀ (hall' x hx)
      simpa using hc
    rw [hmap, hprod]

@[simp] theorem chosenGeneratorWord_mark (S : Finset G)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (a : G) (i₀ : S) (hi₀ : (i₀ : G) = a) :
    chosenGeneratorWord S hgen hsymm a i₀ hi₀ a = [i₀] := by
  classical
  simp [chosenGeneratorWord]

/-- Semantic convergence condition for an ambient finite generator packet. -/
def AmbientWordsRespectGroup
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)]
    (S : Finset G) (W : ∀ n, S → Matrix.unitaryGroup (Y n) ℂ) : Prop :=
  ∀ l₁ l₂ : List S,
    (l₁.map fun i : S ↦ (i : G)).prod =
      (l₂.map fun i : S ↦ (i : G)).prod →
    ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖((TorsionActiveCore.ambientWord (W n) l₁ :
          Matrix.unitaryGroup (Y n) ℂ) : Matrix (Y n) (Y n) ℂ) -
        (TorsionActiveCore.ambientWord (W n) l₂ :
          Matrix.unitaryGroup (Y n) ℂ)‖ ≤ ε

/-- The active-core word model associated to a finite ambient packet. -/
def compressedAlmostRepresentation
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)]
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (a : G) (i₀ : S) (hi₀ : (i₀ : G) = a)
    (W : ∀ n, S → Matrix.unitaryGroup (Y n) ℂ)
    (hcore : ∀ n, 0 < Fintype.card (TorsionActiveCore.activeCoreModel (W n)))
    (hrespect : AmbientWordsRespectGroup S W) : OpAlmostRepresentation G where
  model n := TorsionActiveCore.activeCoreModel (W n)
  modelNonempty := hcore
  map n g := TorsionActiveCore.activeCoreWord (W n)
    (chosenGeneratorWord S hgen hsymm a i₀ hi₀ g)
  asymptoticallyMultiplicative g h ε hε := by
    let qg := chosenGeneratorWord S hgen hsymm a i₀ hi₀ g
    let qh := chosenGeneratorWord S hgen hsymm a i₀ hi₀ h
    let qgh := chosenGeneratorWord S hgen hsymm a i₀ hi₀ (g * h)
    obtain ⟨N, hN⟩ := hrespect qgh (qg ++ qh) (by
      rw [List.map_append, List.prod_append]
      simp only [qg, qh, qgh, chosenGeneratorWord_value]) ε hε
    refine ⟨N, fun n hn ↦ ?_⟩
    change ‖((TorsionActiveCore.activeCoreWord (W n) qgh :
        Matrix.unitaryGroup (TorsionActiveCore.ActiveCoreIndex (W n)) ℂ) :
          Matrix (TorsionActiveCore.ActiveCoreIndex (W n))
            (TorsionActiveCore.ActiveCoreIndex (W n)) ℂ) -
      ((TorsionActiveCore.activeCoreWord (W n) qg :
        Matrix.unitaryGroup (TorsionActiveCore.ActiveCoreIndex (W n)) ℂ) :
          Matrix (TorsionActiveCore.ActiveCoreIndex (W n))
            (TorsionActiveCore.ActiveCoreIndex (W n)) ℂ) *
        (TorsionActiveCore.activeCoreWord (W n) qh)‖ ≤ ε
    have hle := TorsionActiveCore.norm_activeCoreWord_sub_le
      (W n) qgh (qg ++ qh)
    change ‖((TorsionActiveCore.activeCoreWord (W n) qgh :
        Matrix.unitaryGroup (TorsionActiveCore.ActiveCoreIndex (W n)) ℂ) :
          Matrix (TorsionActiveCore.ActiveCoreIndex (W n))
            (TorsionActiveCore.ActiveCoreIndex (W n)) ℂ) -
      ((TorsionActiveCore.activeCoreWord (W n) qg *
        TorsionActiveCore.activeCoreWord (W n) qh :
          Matrix.unitaryGroup (TorsionActiveCore.ActiveCoreIndex (W n)) ℂ) :
            Matrix (TorsionActiveCore.ActiveCoreIndex (W n))
              (TorsionActiveCore.ActiveCoreIndex (W n)) ℂ)‖ ≤ ε
    rw [← TorsionActiveCore.activeCoreWord_append]
    exact hle.trans (hN n hn)

@[simp] theorem compressedAlmostRepresentation_map_mark
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)]
    (S : Finset G) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hsymm : ∀ g ∈ S, g⁻¹ ∈ S) (a : G) (i₀ : S) (hi₀ : (i₀ : G) = a)
    (W : ∀ n, S → Matrix.unitaryGroup (Y n) ℂ)
    (hcore : ∀ n, 0 < Fintype.card (TorsionActiveCore.activeCoreModel (W n)))
    (hrespect : AmbientWordsRespectGroup S W) (n : ℕ) :
    (compressedAlmostRepresentation S hgen hsymm a i₀ hi₀ W hcore hrespect).map n a =
      TorsionActiveCore.activeCoreMatrix (W n) i₀ := by
  simp [compressedAlmostRepresentation, TorsionActiveCore.activeCoreWord]

end

end ActiveCoreAlmostRepresentation
end GroupApproximation
