import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StabMap
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.QalgStabMuLaws

/-!
# Cuntz's comparison map `μ_B : q(𝒦 ⊗ B) → 𝒦 ⊗ qB`

The instance of `QalgStabMuCore`/`QalgStabMuLaws` for the functor `f ↦ id_𝒦 ⊗ f = Stab.map f`:

* `Qalg.mu B : q(𝒦 ⊗ B) → 𝒦 ⊗ qB`, `μ (q (e_{ij} ⊗ b)) = e_{ij} ⊗ q b`;
* `Qalg.map_pi_comp_mu`: `(id_𝒦 ⊗ π_B) ∘ μ_B = π_{𝒦 ⊗ B}`;
* `Qalg.mu_comp_map_map`: naturality, `μ_C ∘ q(id_𝒦 ⊗ f) = (id_𝒦 ⊗ q f) ∘ μ_B`.

Source: J. Cuntz, *A new look at KK-theory*, K-Theory 1 (1987) 31--51, §1 (proof of
Proposition 1.6); arXiv:2404.06840, §3.
Manuscript: `non_mf_group_notes.tex`, UCT hypothesis of `thm:fixed-radical-membership`
(lane TWWKK-C2b-2, work order WO-TWWKK-C2b-2).
-/

namespace GroupApproximation.Full.TWWKK

universe u

noncomputable section

/-- `f ↦ id_𝒦 ⊗ f` as an entrywise functor. -/
def Stab.stabFunctor : MuAux.StabFunctor.{u} where
  map f := Stab.map f
  map_single f i j x := Stab.map_single f i j x

namespace Qalg

/-- **Cuntz's comparison map** `μ_B : q(𝒦 ⊗ B) → 𝒦 ⊗ qB`. -/
def mu (B : Type u) [NonUnitalCStarAlgebra B] : Qalg (Stab B) →⋆ₙₐ[ℂ] Stab (Qalg B) :=
  Stab.stabFunctor.mu B

/-- `(id_𝒦 ⊗ π_B) ∘ μ_B = π_{𝒦 ⊗ B}`. -/
theorem map_pi_comp_mu (B : Type u) [NonUnitalCStarAlgebra B] :
    (Stab.map (Qalg.pi B)).comp (Qalg.mu B) = Qalg.pi (Stab B) :=
  Stab.stabFunctor.map_pi_comp_mu B

/-- **Naturality of `μ`**: `μ_C ∘ q(id_𝒦 ⊗ f) = (id_𝒦 ⊗ q f) ∘ μ_B`. -/
theorem mu_comp_map_map {B C : Type u} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    (f : B →⋆ₙₐ[ℂ] C) :
    (Qalg.mu C).comp (Qalg.map (Stab.map f)) = (Stab.map (Qalg.map f)).comp (Qalg.mu B) :=
  Stab.stabFunctor.mu_comp_map_map f

end Qalg

end

end GroupApproximation.Full.TWWKK
