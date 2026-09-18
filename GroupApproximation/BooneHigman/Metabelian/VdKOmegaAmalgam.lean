import GroupApproximation.BooneHigman.Metabelian.VdKOmegaGen
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabDiagAction
import GroupApproximation.Meta.AxiomGuard

/-!
# The amalgam route, part 3: two glued parabolic actions give a `LastRootAction`

Lane `bh-met-92j`.  Let `α : P̃ →* G` and `β : P̃⁻ →* G` be homomorphisms out of the parabolic
and the opposite parabolic.  Assume two gluing conditions:

* `vdkOmega_Agree α β`: they agree on `St_n(R)`;
* `vdkOmega_Mixed α β`: the mixed relation `⁅x_{i,last}(a), x_{last,k}(b)⁆ = x_{ik}(ab)` holds.

Then `vdkOmega_genVal α β` assigns values to all roots of `St_{n+1}(R)` and satisfies **every**
Steinberg relation (`vdkOmega_genVal_add`, `_comm`, `_adj`).  For `G = Perm Ω` this gives
`vdkOmega_lastRootAction : LastRootAction n R Ω`.  The endpoint `vdkOmega_stab_injective_of_omega`
says: if moreover `α ∘ inr` acts freely at one point `ω₀`, then `stab : St_n → St_{n+1}` is
injective.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

variable {n : ℕ} {R : Type*} [CommRing R] {G : Type*} [Group G]

/-- The value of the root `x_{ij}(a)` of `St_{n+1}(R)`: `β` on row roots, `α` on the rest. -/
def vdkOmega_genVal (α : vdkParPres_Tilde n R →* G) (β : vdkOmega_TildeMinus n R →* G)
    (i j : Fin (n + 1)) (a : R) : G :=
  Fin.lastCases (motive := fun _ ↦ G)
    (Fin.lastCases (motive := fun _ ↦ G) 1 (fun j' ↦ vdkOmega_rv β (Pi.single j' a)) j)
    (fun i' ↦ Fin.lastCases (motive := fun _ ↦ G) (vdkOmega_cv α (Pi.single i' a))
      (fun j' ↦ vdkOmega_sv α i' j' a) j) i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_genVal

variable (α : vdkParPres_Tilde n R →* G) (β : vdkOmega_TildeMinus n R →* G)

theorem vdkOmega_genVal_cc (i j : Fin n) (a : R) :
    vdkOmega_genVal α β i.castSucc j.castSucc a = vdkOmega_sv α i j a := by
  simp only [vdkOmega_genVal, Fin.lastCases_castSucc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_genVal_cc

theorem vdkOmega_genVal_cL (i : Fin n) (a : R) :
    vdkOmega_genVal α β i.castSucc (Fin.last n) a = vdkOmega_cv α (Pi.single i a) := by
  simp only [vdkOmega_genVal, Fin.lastCases_castSucc, Fin.lastCases_last]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_genVal_cL

theorem vdkOmega_genVal_Lc (j : Fin n) (a : R) :
    vdkOmega_genVal α β (Fin.last n) j.castSucc a = vdkOmega_rv β (Pi.single j a) := by
  simp only [vdkOmega_genVal, Fin.lastCases_castSucc, Fin.lastCases_last]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_genVal_Lc

/-- Additivity of every root value. -/
theorem vdkOmega_genVal_add (i j : Fin (n + 1)) (hij : i ≠ j) (a b : R) :
    vdkOmega_genVal α β i j a * vdkOmega_genVal α β i j b =
      vdkOmega_genVal α β i j (a + b) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
  · have h : i ≠ j := ne_of_apply_ne Fin.castSucc hij
    simp only [vdkOmega_genVal_cc, vdkOmega_sv_of_ne α i j h]
    rw [← map_mul, ← map_mul, x_mul]
  · simp only [vdkOmega_genVal_cL]
    rw [← vdkOmega_cv_add, Pi.single_add]
  · simp only [vdkOmega_genVal_Lc]
    rw [← vdkOmega_rv_add, Pi.single_add]
  · exact absurd rfl hij

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_genVal_add

/-- Non-adjacent root values commute. -/
theorem vdkOmega_genVal_comm (hαβ : vdkOmega_Agree α β) (i j k l : Fin (n + 1)) (hij : i ≠ j)
    (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : R) :
    ⁅vdkOmega_genVal α β i j a, vdkOmega_genVal α β k l b⁆ = 1 := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last l with ⟨l, rfl⟩ | rfl
  · -- `cccc`
    have h1 : i ≠ j := ne_of_apply_ne Fin.castSucc hij
    have h2 : k ≠ l := ne_of_apply_ne Fin.castSucc hkl
    simp only [vdkOmega_genVal_cc, vdkOmega_sv_of_ne α i j h1, vdkOmega_sv_of_ne α k l h2]
    rw [vdkOmega_inr_commutator, commutatorElement_eq_one_iff_commute.mpr
      (x_commute_of_ne i j k l h1 h2 (ne_of_apply_ne Fin.castSucc hjk)
        (ne_of_apply_ne Fin.castSucc hli) a b), map_one, map_one]
  · -- `cccL`
    have h1 : i ≠ j := ne_of_apply_ne Fin.castSucc hij
    simp only [vdkOmega_genVal_cc, vdkOmega_genVal_cL, vdkOmega_sv_of_ne α i j h1]
    exact vdkOmega_comm_eq_one_of_conj
      (vdkOmega_conj_cv_triv α i j h1 a k b (ne_of_apply_ne Fin.castSucc hjk))
  · -- `ccLc`
    have h1 : i ≠ j := ne_of_apply_ne Fin.castSucc hij
    simp only [vdkOmega_genVal_cc, vdkOmega_genVal_Lc, vdkOmega_sv_of_ne α i j h1]
    exact vdkOmega_comm_eq_one_of_conj
      (vdkOmega_conj_rv_triv α β hαβ i j h1 a l b (ne_of_apply_ne Fin.castSucc hli).symm)
  · exact absurd rfl hkl
  · -- `cLcc`
    have h2 : k ≠ l := ne_of_apply_ne Fin.castSucc hkl
    simp only [vdkOmega_genVal_cL, vdkOmega_genVal_cc, vdkOmega_sv_of_ne α k l h2]
    exact vdkOmega_comm_eq_one_of_conj'
      (vdkOmega_conj_cv_triv α k l h2 b i a (ne_of_apply_ne Fin.castSucc hli))
  · -- `cLcL`
    simp only [vdkOmega_genVal_cL]
    exact vdkOmega_cv_comm α _ _
  · exact absurd rfl hjk
  · exact absurd rfl hjk
  · -- `Lccc`
    have h2 : k ≠ l := ne_of_apply_ne Fin.castSucc hkl
    simp only [vdkOmega_genVal_Lc, vdkOmega_genVal_cc, vdkOmega_sv_of_ne α k l h2]
    exact vdkOmega_comm_eq_one_of_conj'
      (vdkOmega_conj_rv_triv α β hαβ k l h2 b j a (ne_of_apply_ne Fin.castSucc hjk).symm)
  · exact absurd rfl hli
  · -- `LcLc`
    simp only [vdkOmega_genVal_Lc]
    exact vdkOmega_rv_comm β _ _
  · exact absurd rfl hkl
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij
  · exact absurd rfl hij

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_genVal_comm

end GroupApproximation.BooneHigman.Metabelian.ElemFP
