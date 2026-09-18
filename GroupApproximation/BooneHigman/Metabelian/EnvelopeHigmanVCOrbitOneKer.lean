import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFWitPivotSwap
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitMultiStep
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# The pivot set `S` meets `ker E` trivially (lane bh-met-92y)

Notation as in `EnvelopeHigmanVCOrbitMultiStep`: `Q = higmanVCCommon_Q d`, `E : Q →* V_d`,
`U = higmanVCTreeNF_U d`, and `S = U · ⋃_C H_C · U` (`higmanVCTreeNFWitPivot_S d`).

**Proved (unconditional, no Higman input).**
* `higmanVCOrbitOne_U_eq_one`: `q ∈ U` with `E q = 1` gives `q = 1` (`U`-faithfulness).
* `higmanVCOrbitOne_eq_of_mem_S`: `s ∈ S`, `u ∈ U` and `E s = E u` give `s = u`.
  Write `s = u₁ h u₂`.  Then `E h = E (u₁⁻¹ u u₂⁻¹)`, so the proved kernel step
  (`higmanVCTreeNFWitPivot_mem_U`) puts `h` in `U`.  Now `s u⁻¹ ∈ U ∩ ker E = 1`.
* `higmanVCOrbitOne_eq_one_of_mem_S`: `S ∩ ker E = {1}`.

**LOUD: the lane target (`higmanVCOrbitMulti_Step` by tree-pair combinatorics) is NOT
proved here, and no new residual is introduced.**  In `V_d`, tree-pair and prefix-code
combinatorics do produce an `s ∈ S` with `E s = E (m(x₀, y₀) h t)` (given Claim F).  But
lifting that equality to `Q` gives `m(x₀, y₀) h t = s z`, where `z` is a central element of
`ker E` (`higmanVCCommon_ker_central`).  The lemmas here only kill kernel elements that lie
in `S` itself.  Removing `z` is exactly Step B (`HigmanVCCommonCentralStatement`), which is
equivalent to Higman's theorem (1).  So the Step is Higman-strength, and no route through
`E`-images alone can be strictly weaker.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A balanced element with trivial `E`-image is trivial. -/
theorem higmanVCOrbitOne_U_eq_one {d : ℕ} (hd : 1 < d) {q : higmanVCCommon_Q d}
    (hq : q ∈ higmanVCTreeNF_U d) (e : higmanVCTreeNF_E d q = 1) : q = 1 := by
  obtain ⟨r, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  rw [higmanVCTreeNF_E_mk] at e
  exact higmanVCCommon_mk_eq_one_iff.mpr
    (higmanVCTreeNF_U_faithful (by omega) (MonoidHom.mem_ker.mpr e) hq)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitOne_U_eq_one

/-- **`E` separates `S` from `U`.**  If `s ∈ S`, `u ∈ U` and `E s = E u`, then `s = u`. -/
theorem higmanVCOrbitOne_eq_of_mem_S {d : ℕ} (hd : 1 < d) {s u : higmanVCCommon_Q d}
    (hs : s ∈ higmanVCTreeNFWitPivot_S d) (hu : u ∈ higmanVCTreeNF_U d)
    (e : higmanVCTreeNF_E d s = higmanVCTreeNF_E d u) : s = u := by
  obtain ⟨u₁, hu₁, C, hC, h, hh, u₂, hu₂, rfl⟩ := higmanVCTreeNFWitPivot_mem_S.mp hs
  have hβ : u₁⁻¹ * u * u₂⁻¹ ∈ higmanVCTreeNF_U d :=
    (higmanVCTreeNF_U d).mul_mem
      ((higmanVCTreeNF_U d).mul_mem ((higmanVCTreeNF_U d).inv_mem hu₁) hu)
      ((higmanVCTreeNF_U d).inv_mem hu₂)
  have e' := e
  simp only [map_mul] at e'
  have eh : higmanVCTreeNF_E d h = higmanVCTreeNF_E d (u₁⁻¹ * u * u₂⁻¹) := by
    simp only [map_mul, map_inv]
    rw [← e']
    group
  have hhU := higmanVCTreeNFWitPivot_mem_U hd hC hh hβ eh
  have hsU : u₁ * h * u₂ ∈ higmanVCTreeNF_U d :=
    (higmanVCTreeNF_U d).mul_mem ((higmanVCTreeNF_U d).mul_mem hu₁ hhU) hu₂
  have h1 : u₁ * h * u₂ * u⁻¹ = 1 := by
    refine higmanVCOrbitOne_U_eq_one hd
      ((higmanVCTreeNF_U d).mul_mem hsU ((higmanVCTreeNF_U d).inv_mem hu)) ?_
    rw [map_mul, map_inv, e, mul_inv_cancel]
  exact mul_inv_eq_one.mp h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitOne_eq_of_mem_S

/-- **`S ∩ ker E = {1}`.** -/
theorem higmanVCOrbitOne_eq_one_of_mem_S {d : ℕ} (hd : 1 < d) {s : higmanVCCommon_Q d}
    (hs : s ∈ higmanVCTreeNFWitPivot_S d) (e : higmanVCTreeNF_E d s = 1) : s = 1 :=
  higmanVCOrbitOne_eq_of_mem_S hd hs (higmanVCTreeNF_U d).one_mem (by rw [e, map_one])

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitOne_eq_one_of_mem_S

/-- An element of `S` whose `E`-image is balanced is itself balanced. -/
theorem higmanVCOrbitOne_mem_U_of_mem_S {d : ℕ} (hd : 1 < d) {s u : higmanVCCommon_Q d}
    (hs : s ∈ higmanVCTreeNFWitPivot_S d) (hu : u ∈ higmanVCTreeNF_U d)
    (e : higmanVCTreeNF_E d s = higmanVCTreeNF_E d u) : s ∈ higmanVCTreeNF_U d := by
  rw [higmanVCOrbitOne_eq_of_mem_S hd hs hu e]
  exact hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitOne_mem_U_of_mem_S

end GroupApproximation.BooneHigman.Metabelian.Envelope
