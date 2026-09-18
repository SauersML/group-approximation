import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# High exponent: block-diagonal assembly of conjugation representations

Lanes bh-met-67, bh-met-67c.

The multiplicative analogue of `exists_linearization_of_field_pieces`
(`TorsionFreeCoprimaryBlock`).  Let `G`, `Q` be groups and `act : Q → G → G`.  Suppose that for
finitely many `j` we have `κ_j : G →* GL_{d_j}(K_j)` and `ρ_j : Q →* GL_{d_j}(K_j)` with
`κ_j (act q g) = ρ_j q * κ_j g * (ρ_j q)⁻¹`.  Suppose also that the `κ_j` jointly detect `1`,
and that the fields `K_j` embed in a common field `L`.  Then there are one injective
`κ' : G →* GL_{d'}(L)` and one `ρ' : Q →* GL_{d'}(L)` with the same intertwining relation.

Route.  Push every piece into `L` (`GeneralLinearGroup.map`).  Act block-diagonally on
`V = ∏_j L^{d_j}` (`blockEnd`, which works for any monoid, so also for `G`).  Choose a basis of
`V` (`eHighDevissage_exists_gl_of_end_conj`).

* `eHighDevissage_exists_gl_of_end_conj`: endomorphism data on a finite-dimensional space
  gives matrices.
* `eHighDevissage_exists_gl_of_field_pieces`: the block-diagonal assembly.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Coprimary

open Matrix

/-- Conjugation data by endomorphisms of a finite-dimensional space gives conjugation data by
invertible matrices.  The relation is stated without inverses: `κ (act q g) * ρ q = ρ q * κ g`. -/
theorem eHighDevissage_exists_gl_of_end_conj {Q G V L : Type} [Group Q] [Group G] [Field L]
    [AddCommGroup V] [Module L V] [Module.Finite L V] (act : Q → G → G) (κ : G →* Module.End L V)
    (ρ : Q →* Module.End L V) (hinj : ∀ g, κ g = 1 → g = 1)
    (hequiv : ∀ q g, κ (act q g) * ρ q = ρ q * κ g) :
    ∃ (d : ℕ) (κ' : G →* GeneralLinearGroup (Fin d) L) (ρ' : Q →* GeneralLinearGroup (Fin d) L),
      Function.Injective κ' ∧ ∀ q g, κ' (act q g) = ρ' q * κ' g * (ρ' q)⁻¹ := by
  let b := Module.finBasis L V
  let e : Module.End L V →* Matrix (Fin (Module.finrank L V)) (Fin (Module.finrank L V)) L :=
    (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom
  have he : Function.Injective e := fun x y hxy => (LinearMap.toMatrixAlgEquiv b).injective hxy
  refine ⟨Module.finrank L V, (e.comp κ).toHomUnits, (e.comp ρ).toHomUnits, ?_, fun q g => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    refine hinj g (he ?_)
    have h1 : e (κ g) = 1 := congrArg Units.val hg
    rw [h1, map_one]
  · refine eq_mul_inv_of_mul_eq (Units.ext ?_)
    show e (κ (act q g)) * e (ρ q) = e (ρ q) * e (κ g)
    rw [← map_mul, ← map_mul, hequiv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighDevissage_exists_gl_of_end_conj

/-- **Block-diagonal assembly.**  Finitely many conjugation representations over fields `K j`
that embed in `L` and jointly detect `1` combine into one faithful conjugation representation
over `L`. -/
theorem eHighDevissage_exists_gl_of_field_pieces {Q G J L : Type} [Group Q] [Group G]
    [Fintype J] [Field L] (act : Q → G → G) (K : J → Type) [∀ j, Field (K j)] (f : ∀ j, K j →+* L) (d : J → ℕ)
    (κ : ∀ j, G →* GeneralLinearGroup (Fin (d j)) (K j))
    (ρ : ∀ j, Q →* GeneralLinearGroup (Fin (d j)) (K j))
    (hdet : ∀ g, (∀ j, κ j g = 1) → g = 1)
    (hequiv : ∀ j q g, κ j (act q g) = ρ j q * κ j g * (ρ j q)⁻¹) :
    ∃ (d' : ℕ) (κ' : G →* GeneralLinearGroup (Fin d') L)
      (ρ' : Q →* GeneralLinearGroup (Fin d') L),
      Function.Injective κ' ∧ ∀ q g, κ' (act q g) = ρ' q * κ' g * (ρ' q)⁻¹ := by
  classical
  let κL : ∀ j, G →* GeneralLinearGroup (Fin (d j)) L :=
    fun j => (GeneralLinearGroup.map (f j)).comp (κ j)
  let ρL : ∀ j, Q →* GeneralLinearGroup (Fin (d j)) L :=
    fun j => (GeneralLinearGroup.map (f j)).comp (ρ j)
  have hL : ∀ j q g, κL j (act q g) * ρL j q = ρL j q * κL j g := by
    intro j q g
    have h8 : κL j (act q g) = ρL j q * κL j g * (ρL j q)⁻¹ := by
      show GeneralLinearGroup.map (f j) (κ j (act q g)) =
        GeneralLinearGroup.map (f j) (ρ j q) * GeneralLinearGroup.map (f j) (κ j g) *
          (GeneralLinearGroup.map (f j) (ρ j q))⁻¹
      rw [hequiv, map_mul, map_mul, map_inv]
    exact eq_mul_inv_iff_mul_eq.mp h8
  refine eHighDevissage_exists_gl_of_end_conj act (blockEnd κL) (blockEnd ρL)
    (fun g hg => hdet g fun j => ?_) (fun q g => LinearMap.ext fun v => funext fun j => ?_)
  · have h4 : ∀ w : Fin (d j) → L,
        (κL j g : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ w = w := by
      intro w
      have h5 : blockEnd κL g (Pi.single (M := fun j => Fin (d j) → L) j w) j =
          (1 : Module.End L (∀ j, Fin (d j) → L))
            (Pi.single (M := fun j => Fin (d j) → L) j w) j :=
        congrFun (LinearMap.congr_fun hg _) j
      change (κL j g : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ
          (Pi.single (M := fun j => Fin (d j) → L) j w j) =
        Pi.single (M := fun j => Fin (d j) → L) j w j at h5
      rwa [Pi.single_eq_same] at h5
    have h6 : (κL j g : Matrix (Fin (d j)) (Fin (d j)) L) = 1 :=
      Matrix.ext_of_mulVec_single fun i => by rw [h4, Matrix.one_mulVec]
    have h2 : GeneralLinearGroup.map (f j) (κ j g) = GeneralLinearGroup.map (f j) 1 := by
      rw [map_one]
      exact Units.ext (h6.trans Units.val_one.symm)
    refine Units.ext (Matrix.ext fun a c => (f j).injective ?_)
    exact congrArg (fun u : GeneralLinearGroup (Fin (d j)) L =>
      (u : Matrix (Fin (d j)) (Fin (d j)) L) a c) h2
  · change (κL j (act q g) : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ
        ((ρL j q : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ v j) =
      (ρL j q : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ
        ((κL j g : Matrix (Fin (d j)) (Fin (d j)) L) *ᵥ v j)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hL]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.eHighDevissage_exists_gl_of_field_pieces

end GroupApproximation.BooneHigman.Metabelian.Coprimary
