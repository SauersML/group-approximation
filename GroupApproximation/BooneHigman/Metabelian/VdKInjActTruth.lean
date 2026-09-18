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

open Classical in
/-- A preimage under `vdkRowPar`, when one exists, and `(0, 1)` otherwise. -/
noncomputable def vdkInjAct_pre (h : St (n + 1) R) : (Fin n → R) × St n R :=
  if hh : ∃ p : (Fin n → R) × St n R, vdkRowPar p = h then Classical.choose hh else (0, 1)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_pre

theorem vdkInjAct_pre_spec {h : St (n + 1) R} (hh : h ∈ vdkRowParSubgroup n R) :
    vdkRowPar (vdkInjAct_pre h) = h := by
  have hh' : ∃ p : (Fin n → R) × St n R, vdkRowPar p = h := (mem_vdkRowParSubgroup h).mp hh
  rw [vdkInjAct_pre, dif_pos hh']
  exact Classical.choose_spec hh'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_pre_spec

theorem vdkInjAct_pre_rowPar (hinj : Function.Injective (vdkRowPar (n := n) (R := R)))
    (p : (Fin n → R) × St n R) : vdkInjAct_pre (vdkRowPar p) = p :=
  hinj (vdkInjAct_pre_spec ((mem_vdkRowParSubgroup _).mpr ⟨p, rfl⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_pre_rowPar

theorem vdkInjAct_rowPar_mul (p p' : (Fin n → R) × St n R) :
    vdkRowPar p * vdkRowPar p' = vdkRowPar (p.1 + projectionMatrix p.2 *ᵥ p'.1, p.2 * p'.2) := by
  obtain ⟨v, g⟩ := p
  obtain ⟨v', g'⟩ := p'
  exact vdkRowPar_mul v g v' g'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_rowPar_mul

/-- On the parabolic, the `St_n(R)`-component of the preimage is multiplicative. -/
theorem vdkInjAct_pre_mul (hinj : Function.Injective (vdkRowPar (n := n) (R := R)))
    {q₁ q₂ : St (n + 1) R} (h₁ : q₁ ∈ vdkRowParSubgroup n R) (h₂ : q₂ ∈ vdkRowParSubgroup n R) :
    (vdkInjAct_pre (q₁ * q₂)).2 = (vdkInjAct_pre q₁).2 * (vdkInjAct_pre q₂).2 := by
  have h12 := vdkInjAct_rowPar_mul (vdkInjAct_pre q₁) (vdkInjAct_pre q₂)
  rw [vdkInjAct_pre_spec h₁, vdkInjAct_pre_spec h₂] at h12
  rw [h12, vdkInjAct_pre_rowPar hinj]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_pre_mul

theorem vdkInjAct_twist_mem {u : Fin (n + 1) → R} (hu : vdkInjAct_Orb u) (g : St (n + 1) R) :
    vdkInjAct_sec u * g * (vdkInjAct_sec (vdkInjAct_row u g))⁻¹ ∈ vdkInjCoset_rowStab n R := by
  rw [vdkInjCoset_mem_rowStab]
  show vdkInjAct_row (Pi.single (Fin.last n) 1)
      (vdkInjAct_sec u * g * (vdkInjAct_sec (vdkInjAct_row u g))⁻¹) = Pi.single (Fin.last n) 1
  rw [← vdkInjAct_row_mul, ← vdkInjAct_row_mul, vdkInjAct_sec_spec hu,
    vdkInjAct_sec_inv (vdkInjAct_Orb_row hu g)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_twist_mem

open Classical in
/-- The multiplicative function behind the truth check: the `St_n(R)`-component of
`sec(u) g sec(u M_g)⁻¹` on the orbit of `e_last`, and `1` off it. -/
noncomputable def vdkInjAct_truthPhi (u : Fin (n + 1) → R) (g : St (n + 1) R) : St n R :=
  if vdkInjAct_Orb u then
    (vdkInjAct_pre (vdkInjAct_sec u * g * (vdkInjAct_sec (vdkInjAct_row u g))⁻¹)).2
  else 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_truthPhi

theorem vdkInjAct_truthPhi_pos {u : Fin (n + 1) → R} (hu : vdkInjAct_Orb u) (g : St (n + 1) R) :
    vdkInjAct_truthPhi u g =
      (vdkInjAct_pre (vdkInjAct_sec u * g * (vdkInjAct_sec (vdkInjAct_row u g))⁻¹)).2 := by
  rw [vdkInjAct_truthPhi, if_pos hu]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_truthPhi_pos

theorem vdkInjAct_truthPhi_neg {u : Fin (n + 1) → R} (hu : ¬vdkInjAct_Orb u)
    (g : St (n + 1) R) : vdkInjAct_truthPhi u g = 1 := by
  rw [vdkInjAct_truthPhi, if_neg hu]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_truthPhi_neg

/-- Step A and injectivity of `vdkRowPar` make `truthPhi` multiplicative along the row action. -/
theorem vdkInjAct_truthPhi_mul (hA : vdkInjCoset_rowStab n R ≤ vdkRowParSubgroup n R)
    (hinj : Function.Injective (vdkRowPar (n := n) (R := R))) (u : Fin (n + 1) → R)
    (g g' : St (n + 1) R) :
    vdkInjAct_truthPhi u g * vdkInjAct_truthPhi (vdkInjAct_row u g) g' =
      vdkInjAct_truthPhi u (g * g') := by
  by_cases hu : vdkInjAct_Orb u
  · have hu' := vdkInjAct_Orb_row hu g
    have hq : vdkInjAct_sec u * g * (vdkInjAct_sec (vdkInjAct_row u g))⁻¹ *
        (vdkInjAct_sec (vdkInjAct_row u g) * g' *
          (vdkInjAct_sec (vdkInjAct_row (vdkInjAct_row u g) g'))⁻¹) =
        vdkInjAct_sec u * (g * g') * (vdkInjAct_sec (vdkInjAct_row u (g * g')))⁻¹ := by
      rw [vdkInjAct_row_mul]
      group
    rw [vdkInjAct_truthPhi_pos hu g, vdkInjAct_truthPhi_pos hu' g',
      vdkInjAct_truthPhi_pos hu (g * g'),
      ← vdkInjAct_pre_mul hinj (hA (vdkInjAct_twist_mem hu g)) (hA (vdkInjAct_twist_mem hu' g')),
      hq]
  · have hu' : ¬vdkInjAct_Orb (vdkInjAct_row u g) := fun h ↦ hu (vdkInjAct_Orb_of_row h)
    rw [vdkInjAct_truthPhi_neg hu g, vdkInjAct_truthPhi_neg hu' g',
      vdkInjAct_truthPhi_neg hu (g * g'), one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_truthPhi_mul

/-- The cocycle of `truthPhi` is based: at `e_last`, a stabilized root `x_{i'j'}(a)` is
`vdkRowPar (0, x_{ij}(a))`, so its component is `x_{ij}(a)`. -/
theorem vdkInjAct_truthPhi_based (hinj : Function.Injective (vdkRowPar (n := n) (R := R))) :
    vdkInjAct_IsBased (fun u i j hij a ↦ vdkInjAct_truthPhi u (x i j hij a)) := by
  intro i j hij h' a
  show vdkInjAct_truthPhi (Pi.single (Fin.last n) 1) (x i.castSucc j.castSucc h' a) = x i j hij a
  have he : vdkInjAct_Orb (Pi.single (Fin.last n) (1 : R)) := ⟨1, vdkInjAct_row_one _⟩
  have hrow : vdkInjAct_row (Pi.single (Fin.last n) (1 : R)) (x i.castSucc j.castSucc h' a) =
      Pi.single (Fin.last n) 1 :=
    (vdkInjCoset_mem_rowStab _).mp (vdkInjCoset_x_mem _ _ h' a (Fin.castSucc_ne_last i))
  have hs : vdkRowPar ((0 : Fin n → R), x i j hij a) = stab n R (x i j hij a) := by
    rw [vdkRowPar_apply, colVec_zero, one_mul]
  rw [vdkInjAct_truthPhi_pos he, hrow, vdkInjAct_sec_base, one_mul, inv_one, mul_one,
    ← stab_x i j hij a, ← hs, vdkInjAct_pre_rowPar hinj]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_truthPhi_based

/-- **Truth check at one `n`.**  Step A and injectivity of `K2Stab n R` give a based row cocycle.
-/
theorem vdkInjAct_cocycle_of_rowStab (hA : vdkInjCoset_RowStabAt n R)
    (hK : Function.Injective (K2Stab n R)) :
    ∃ c : vdkInjAct_Cocycle n R, vdkInjAct_IsCocycle c ∧ vdkInjAct_IsBased c := by
  have hinj := vdkRowParInjective_of_K2Stab_injective hK
  exact ⟨_, vdkInjAct_isCocycle_of_mul _ (vdkInjAct_truthPhi_mul hA hinj),
    vdkInjAct_truthPhi_based hinj⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_cocycle_of_rowStab

/-- **Truth check.**  Step A (`vdkInjCoset_RowStabStatement`) and the target give the residual.
-/
theorem vdkInjAct_cocycleStatement_of_injStab (hA : vdkInjCoset_RowStabStatement)
    (h : vdkInjDirect_TransitiveInjStatement) : vdkInjAct_CocycleStatement := by
  intro R _ r hsr htr
  exact vdkInjAct_cocycle_of_rowStab (hA R r (r + 3) hsr le_rfl) (h R r hsr htr)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_cocycleStatement_of_injStab

/-- **Strength (LOUD).**  Modulo Step A, the residual is equivalent to the target. -/
theorem vdkInjAct_cocycle_iff_of_rowStab (hA : vdkInjCoset_RowStabStatement) :
    vdkInjAct_CocycleStatement ↔ vdkInjDirect_TransitiveInjStatement :=
  ⟨vdkInjAct_transitiveInj_of_cocycle, vdkInjAct_cocycleStatement_of_injStab hA⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjAct_cocycle_iff_of_rowStab

end GroupApproximation.BooneHigman.Metabelian.ElemFP

