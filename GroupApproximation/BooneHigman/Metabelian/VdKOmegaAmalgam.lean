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

/-- The commutator relation for adjacent roots.  The one input beyond the two parabolics is
`vdkOmega_Mixed`, used in the case `(c, last, c)`. -/
theorem vdkOmega_genVal_adj (hαβ : vdkOmega_Agree α β) (hmix : vdkOmega_Mixed α β)
    (i j k : Fin (n + 1)) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅vdkOmega_genVal α β i j a, vdkOmega_genVal α β j k b⁆ =
      vdkOmega_genVal α β i k (a * b) := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k, rfl⟩ | rfl
  · -- `ccc`
    have h1 : i ≠ j := ne_of_apply_ne Fin.castSucc hij
    have h2 : j ≠ k := ne_of_apply_ne Fin.castSucc hjk
    have h3 : i ≠ k := ne_of_apply_ne Fin.castSucc hik
    simp only [vdkOmega_genVal_cc, vdkOmega_sv_of_ne α i j h1, vdkOmega_sv_of_ne α j k h2,
      vdkOmega_sv_of_ne α i k h3]
    rw [vdkOmega_inr_commutator, x_commutator i j k h1 h2 h3 a b]
  · -- `ccL`
    have h1 : i ≠ j := ne_of_apply_ne Fin.castSucc hij
    simp only [vdkOmega_genVal_cc, vdkOmega_genVal_cL, vdkOmega_sv_of_ne α i j h1]
    exact vdkOmega_sv_cv_adj α i j h1 a b
  · -- `cLc`: the mixed relation
    have h3 : i ≠ k := ne_of_apply_ne Fin.castSucc hik
    simp only [vdkOmega_genVal_cL, vdkOmega_genVal_Lc, vdkOmega_genVal_cc,
      vdkOmega_sv_of_ne α i k h3]
    exact hmix i k h3 a b
  · exact absurd rfl hjk
  · -- `Lcc`
    have h2 : j ≠ k := ne_of_apply_ne Fin.castSucc hjk
    simp only [vdkOmega_genVal_Lc, vdkOmega_genVal_cc, vdkOmega_sv_of_ne α j k h2]
    exact vdkOmega_rv_sv_adj α β hαβ j k h2 a b
  · exact absurd rfl hik
  · exact absurd rfl hij
  · exact absurd rfl hij

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_genVal_adj

/-- **The amalgam `LastRootAction`.**  Two permutation actions of the parabolic `P̃` and the
opposite parabolic `P̃⁻` on one set `Ω`, glued by `vdkOmega_Agree` and `vdkOmega_Mixed`, extend
to an action of `St_{n+1}(R)` whose restriction to `St_n(R)` is `α ∘ inr`. -/
def vdkOmega_lastRootAction {Ω : Type*} (α : vdkParPres_Tilde n R →* Equiv.Perm Ω)
    (β : vdkOmega_TildeMinus n R →* Equiv.Perm Ω) (hαβ : vdkOmega_Agree α β)
    (hmix : vdkOmega_Mixed α β) : LastRootAction n R Ω where
  act := α.comp vdkParPres_inr
  T i j _ a := vdkOmega_genVal α β i j a
  compat i j hij _ a := by
    change vdkOmega_genVal α β i.castSucc j.castSucc a = α (vdkParPres_inr (x i j hij a))
    rw [vdkOmega_genVal_cc, vdkOmega_sv_of_ne α i j hij]
  add i j hij a b _ := vdkOmega_genVal_add α β i j hij a b
  commute i j k l hij hkl hjk hli a b _ :=
    vdkOmega_genVal_comm α β hαβ i j k l hij hkl hjk hli a b
  adjacent i j k hij hjk hik a b _ := vdkOmega_genVal_adj α β hαβ hmix i j k hij hjk hik a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_lastRootAction

/-- **Reduction.**  Glued parabolic actions, with `St_n(R)` acting freely at one point `ω₀`, make
`stab : St_n(R) → St_{n+1}(R)` injective. -/
theorem vdkOmega_stab_injective_of_omega {Ω : Type*}
    (α : vdkParPres_Tilde n R →* Equiv.Perm Ω) (β : vdkOmega_TildeMinus n R →* Equiv.Perm Ω)
    (hαβ : vdkOmega_Agree α β) (hmix : vdkOmega_Mixed α β) (ω₀ : Ω)
    (hfree : ∀ g : St n R, α (vdkParPres_inr g) ω₀ = ω₀ → g = 1) :
    Function.Injective (stab n R) := by
  refine (injective_iff_map_eq_one (stab n R)).mpr fun g hg ↦ hfree g ?_
  have h := (vdkOmega_lastRootAction α β hαβ hmix).act_eq_one_of_stab_eq_one hg
  change α (vdkParPres_inr g) = 1 at h
  rw [h, Equiv.Perm.one_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkOmega_stab_injective_of_omega

end GroupApproximation.BooneHigman.Metabelian.ElemFP
