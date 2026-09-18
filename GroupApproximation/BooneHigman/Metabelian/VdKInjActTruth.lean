import GroupApproximation.BooneHigman.Metabelian.VdKInjActWire
import GroupApproximation.BooneHigman.Metabelian.VdKInjCosetWire
import GroupApproximation.Meta.AxiomGuard

/-!
# van der Kallen's injectivity action, part 5: truth check of the residual

Lane `bh-met-91o`.  This file shows that `vdkInjAct_CocycleStatement` is **true modulo Step A**.
From injectivity of `K2Stab n R` and `rowStab(e_last) ≤ P`, it builds a based row cocycle.

* `vdkInjAct_isCocycle_of_mul`: any `Φ(u, g) ∈ St_n(R)` with
  `Φ(u, g) Φ(u M_g, g') = Φ(u, g g')` restricts to a row cocycle on roots.
* `vdkInjAct_sec u` is a section of the orbit map `g ↦ e_last M_g`, with `sec e_last = 1`.
* `vdkInjAct_pre h` is a preimage of `h` under `vdkRowPar`, whenever one exists.
* `vdkInjAct_truthPhi u g` is the `St_n(R)`-component of `sec(u) g sec(u M_g)⁻¹ ∈ rowStab ≤ P`
  on the orbit of `e_last`.  Off the orbit it is `1`.
* `vdkInjAct_cocycleStatement_of_injStab`: Step A and the target give the residual.  With
  `vdkInjAct_transitiveInj_of_cocycle`, this makes the residual equivalent to the target modulo
  Step A (`vdkInjAct_cocycle_iff_of_rowStab`).  That equivalence is the LOUD strength statement.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 (colVec_zero projectionMatrix)
open scoped Matrix

variable {n : ℕ} {R : Type*} [CommRing R]

/-- A function on rows and `St_{n+1}(R)` that is multiplicative along the row action gives a row
cocycle. -/
theorem vdkInjAct_isCocycle_of_mul (Φ : (Fin (n + 1) → R) → St (n + 1) R → St n R)
    (hΦ : ∀ u g g', Φ u g * Φ (vdkInjAct_row u g) g' = Φ u (g * g')) :
    vdkInjAct_IsCocycle (fun u i j hij a ↦ Φ u (x i j hij a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u i j hij a b
    show Φ u (x i j hij a) * Φ (vdkInjAct_row u (x i j hij a)) (x i j hij b) =
      Φ u (x i j hij (a + b))
    rw [hΦ, x_mul]
  · intro u i j k l hij hkl hjk hli a b
    show Φ u (x i j hij a) * Φ (vdkInjAct_row u (x i j hij a)) (x k l hkl b) =
      Φ u (x k l hkl b) * Φ (vdkInjAct_row u (x k l hkl b)) (x i j hij a)
    rw [hΦ, hΦ, (x_commute_of_ne i j k l hij hkl hjk hli a b).eq]
  · intro u i j k hij hjk hik a b
    show Φ u (x i j hij a) * Φ (vdkInjAct_row u (x i j hij a)) (x j k hjk b) =
      Φ u (x i k hik (a * b)) * Φ (vdkInjAct_row u (x i k hik (a * b))) (x j k hjk b) *
        Φ (vdkInjAct_row (vdkInjAct_row u (x i k hik (a * b))) (x j k hjk b)) (x i j hij a)
    rw [hΦ, hΦ, vdkInjAct_row_mul, hΦ, vdkInjAct_x_adjacent_eq i j k hij hjk hik a b]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_isCocycle_of_mul

/-- The orbit of `e_last` under the row action. -/
abbrev vdkInjAct_Orb (u : Fin (n + 1) → R) : Prop :=
  ∃ g : St (n + 1) R, vdkInjAct_row (Pi.single (Fin.last n) 1) g = u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_Orb

theorem vdkInjAct_Orb_row {u : Fin (n + 1) → R} (hu : vdkInjAct_Orb u) (g : St (n + 1) R) :
    vdkInjAct_Orb (vdkInjAct_row u g) := by
  obtain ⟨g₀, h₀⟩ := hu
  exact ⟨g₀ * g, by rw [← vdkInjAct_row_mul, h₀]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_Orb_row

theorem vdkInjAct_Orb_of_row {u : Fin (n + 1) → R} {g : St (n + 1) R}
    (hu : vdkInjAct_Orb (vdkInjAct_row u g)) : vdkInjAct_Orb u := by
  obtain ⟨g₁, h₁⟩ := hu
  refine ⟨g₁ * g⁻¹, ?_⟩
  rw [← vdkInjAct_row_mul, h₁, vdkInjAct_row_mul, mul_inv_cancel, vdkInjAct_row_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_Orb_of_row

open Classical in
/-- A section of the orbit map `g ↦ e_last M_g`, with value `1` at `e_last` and off the orbit. -/
noncomputable def vdkInjAct_sec (u : Fin (n + 1) → R) : St (n + 1) R :=
  if u = Pi.single (Fin.last n) 1 then 1 else
    if h : vdkInjAct_Orb u then Classical.choose h else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_sec

theorem vdkInjAct_sec_base : vdkInjAct_sec (Pi.single (Fin.last n) (1 : R)) = 1 := by
  rw [vdkInjAct_sec, if_pos rfl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_sec_base

theorem vdkInjAct_sec_spec {u : Fin (n + 1) → R} (hu : vdkInjAct_Orb u) :
    vdkInjAct_row (Pi.single (Fin.last n) 1) (vdkInjAct_sec u) = u := by
  by_cases h₁ : u = Pi.single (Fin.last n) 1
  · rw [vdkInjAct_sec, if_pos h₁, vdkInjAct_row_one, h₁]
  · rw [vdkInjAct_sec, if_neg h₁, dif_pos hu]
    exact Classical.choose_spec hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_sec_spec

theorem vdkInjAct_sec_inv {w : Fin (n + 1) → R} (hw : vdkInjAct_Orb w) :
    vdkInjAct_row w (vdkInjAct_sec w)⁻¹ = Pi.single (Fin.last n) 1 := by
  calc vdkInjAct_row w (vdkInjAct_sec w)⁻¹
      = vdkInjAct_row (vdkInjAct_row (Pi.single (Fin.last n) 1) (vdkInjAct_sec w))
          (vdkInjAct_sec w)⁻¹ := by rw [vdkInjAct_sec_spec hw]
    _ = Pi.single (Fin.last n) 1 := by
        rw [vdkInjAct_row_mul, mul_inv_cancel, vdkInjAct_row_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_sec_inv

