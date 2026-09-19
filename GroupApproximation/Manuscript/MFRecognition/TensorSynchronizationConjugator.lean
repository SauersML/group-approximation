import GroupApproximation.Manuscript.MFRecognition.TensorSynchronizationData
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationConjugatorCore

/-!
# `lem:tensor-sync`: the synchronizing unitary `W`

This module supplies the printed edge homomorphisms and kernel calculation for
`lem:tensor-sync` in `mf_recognition_complexity.tex`. The construction of the
coordinate conjugators and their assembly into a reduced-product unitary are
delegated to the OneSided tensor-synchronization core.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace TensorSynchronization

open Filter PolarLiftingGeneralCStar
open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly

noncomputable section

noncomputable local instance tensorSynchronizationConjugatorPartialOrder
    (A : Type*) [CStarAlgebra A] : PartialOrder A :=
  CStarAlgebra.spectralOrder A

local instance tensorSynchronizationConjugatorStarOrderedRing
    (A : Type*) [CStarAlgebra A] : StarOrderedRing A :=
  CStarAlgebra.spectralOrderedRing A

/-! ## The two printed homomorphisms out of `S` -/

section Edge

variable {Gamma : Type} [Group Gamma]

/-- `s ↦ (s,1)`, the source side of the printed edge relation
`u(s,1)u⁻¹ = (s,τ(s))`. -/
def edgeSource (S : Subgroup Gamma) (Q : Type) [Group Q] : S →* Gamma × Q :=
  S.subtype.prod (1 : S →* Q)

/-- `s ↦ (s,τ(s))`, the target side of the printed edge relation. -/
def edgeTarget {Q : Type} [Group Q] {S : Subgroup Gamma} (tau : S →* Q) :
    S →* Gamma × Q :=
  S.subtype.prod tau

/-- `(λ_n,β_n) : Γ × Q → G_n × B_n`. -/
def pairHom {Q : Type} [Group Q] {G : Type} [Group G] {Bfin : Type}
    [Group Bfin] (lam : Gamma →* G) (bet : Q →* Bfin) :
    Gamma × Q →* G × Bfin :=
  (lam.comp (MonoidHom.fst Gamma Q)).prod (bet.comp (MonoidHom.snd Gamma Q))

/-- The homomorphisms `s ↦ (λ_n(s),1)` and
`s ↦ (λ_n(s),β_nτ(s))` have the same kernel under the printed hypothesis
`ker(λ_n|_S) ≤ ker(β_n ∘ τ)`. -/
theorem pairHom_edgeKer_eq {Q : Type} [Group Q] {G : Type} [Group G]
    {Bfin : Type} [Group Bfin]
    {S : Subgroup Gamma} (tau : S →* Q) (lam : Gamma →* G) (bet : Q →* Bfin)
    (hker : (lam.comp S.subtype).ker ≤ (bet.comp tau).ker) :
    ((pairHom lam bet).comp (edgeSource S Q)).ker =
      ((pairHom lam bet).comp (edgeTarget tau)).ker := by
  ext s
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hs
    have h1 : lam (S.subtype s) = 1 := congrArg Prod.fst hs
    have h2 : bet (tau s) = 1 :=
      MonoidHom.mem_ker.mp (hker (MonoidHom.mem_ker.mpr h1))
    exact Prod.ext h1 h2
  · intro hs
    have h1 : lam (S.subtype s) = 1 := congrArg Prod.fst hs
    exact Prod.ext h1 (map_one bet)

end Edge

/-! ## The synchronizing unitary `W = [(1 ⊗ W_n)_n]` -/

section Corona

variable {Gamma : Type} [Group Gamma] {Q : Type} [Group Q]
  {A1 : Type} [CStarAlgebra A1] {S : Subgroup Gamma}
  (E : ℕ → Type) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
  [∀ n, DecidableEq (E n)]
  [∀ n, Nontrivial (CStarMatrix (E n) (E n) A1)]

/-- The reduced-product unitary `W = [(1 ⊗ W_n)_n]` satisfies
`W V(s,1) W* = V(s,τ(s))` for every `s ∈ S`. -/
theorem exists_syncConjugator (tau : S →* Q)
    (R1 : RegularRealizationData Gamma A1)
    (ell : ∀ n, Gamma × Q →* E n)
    (hker : ∀ n, ((ell n).comp (edgeSource S Q)).ker =
      ((ell n).comp (edgeTarget tau)).ker) :
    ∃ W : unitary (CStarProductCorona
        (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite), ∀ s : S,
      (W : CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) *
          ((syncRep E R1 ell (edgeSource S Q s) :
            unitary (CStarProductCorona
              (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)) :
            CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) *
            star (W : CStarProductCorona
              (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) =
        ((syncRep E R1 ell (edgeTarget tau s) :
          unitary (CStarProductCorona
            (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)) :
          CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) := by
  letI : ∀ n, Nonempty (E n) := fun _ ↦ ⟨1⟩
  letI : Nontrivial A1 := regularRealization_nontrivial R1
  refine ⟨synchronizedProductConjugator E R1 ell
    (edgeSource S Q) (edgeTarget tau) (fun _ ↦ rfl) hker, ?_⟩
  intro s
  exact synchronizedProductConjugator_covariance E R1 ell
    (edgeSource S Q) (edgeTarget tau) (fun _ ↦ rfl) hker s

end Corona

end

end TensorSynchronization
end MFRecognition
end Manuscript
end GroupApproximation
