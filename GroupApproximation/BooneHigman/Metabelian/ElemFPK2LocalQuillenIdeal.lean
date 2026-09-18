import Mathlib.RingTheory.Ideal.Maximal
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2LocalQuillenComp
import GroupApproximation.Meta.AxiomGuard

/-!
# The Quillen ideal of an element of `K₂(N, B[t])`: the patching half of the local-global principle

Lane `bh-met-46`.  Let `B` be a commutative ring and `u ∈ K₂(N, B[t])`.  With the substitutions
`σ_a`, `μ_c`, `τ_b`, `ρ` of `ElemFPK2LocalQuillenMaps` put

  `v_a(u) = σ_a(u) · C(u)⁻¹ = u(t + a y) · u(t)⁻¹ ∈ K₂(N, B[t][y])`   (`quillenDiff u a`)

and `Q(u) = {a ∈ B : v_a(u) dies after padding}` (`quillenIdeal u`).

* `Q(u)` is an ideal.  `v_0 = 1` (`σ_0 = C`).  `μ_c v_a = v_{c a}`, so `Q(u)` is closed under
  multiplication by `B`.  `v_{a + b} = τ_b(v_a) · v_b`, because `τ_b σ_a = σ_{a+b}` and
  `τ_b C = σ_b`, so `Q(u)` is closed under addition.  Dying after padding is closed under products
  and ring maps (`diesAfterPadding_mul`, `diesAfterPadding_K2Map`).
* `quillenDiff_one_collapse`: if `ev_{t=0} u = 1`, then `ρ(v_1) = u`, because `ρ σ_1 = id` and
  `ρ C = C ∘ ev_{t=0}`.  So `1 ∈ Q(u)` makes `u` die.
* `diesAfterPadding_of_local`: **patching.**  If `ev_{t=0} u = 1` and every maximal ideal `m` of
  `B` misses some element of `Q(u)`, then `Q(u) = B` (Krull), so `u` dies after padding.
* `quillenIdeal_eq_top_of_diesAfterPadding`: conversely, if `u` dies then `Q(u) = B`.

This is the formal (Quillen) half of the local-global principle for unstable `K₂` of polynomial
rings.  It uses no Steinberg relation, only functoriality of `K₂(N, -)` and padding.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

section DiesAfterPadding

variable {R : Type*} [Ring R] {N : ℕ}

theorem diesAfterPadding_one : K2DiesAfterPadding (1 : K2 (Fin N) R) :=
  ⟨N, le_rfl, map_one _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_one

theorem diesAfterPadding_inv {u : K2 (Fin N) R} (hu : K2DiesAfterPadding u) :
    K2DiesAfterPadding u⁻¹ := by
  obtain ⟨M, hNM, hM⟩ := hu
  exact ⟨M, hNM, by rw [map_inv, hM, inv_one]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_inv

end DiesAfterPadding

section QuillenIdeal

variable {B : Type*} [CommRing B] {N : ℕ}

/-- `v_a(u) = u(t + a y) · u(t)⁻¹ ∈ K₂(N, B[t][y])`. -/
noncomputable def quillenDiff (u : K2 (Fin N) (Polynomial B)) (a : B) :
    K2 (Fin N) (Polynomial (Polynomial B)) :=
  K2Map (quillenShift B a) u *
    (K2Map (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B)) u)⁻¹

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenDiff

theorem quillenDiff_zero (u : K2 (Fin N) (Polynomial B)) : quillenDiff u 0 = 1 := by
  rw [quillenDiff, quillenShift_zero, mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenDiff_zero

/-- `μ_c v_a = v_{c a}`. -/
theorem K2Map_quillenScale_quillenDiff (u : K2 (Fin N) (Polynomial B)) (c a : B) :
    K2Map (quillenScale B c) (quillenDiff u a) = quillenDiff u (c * a) := by
  rw [quillenDiff, quillenDiff, map_mul, map_inv, K2Map_K2Map, K2Map_K2Map,
    quillenScale_comp_shift, quillenScale_comp_C]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.K2Map_quillenScale_quillenDiff

/-- `v_{a + b} = τ_b(v_a) · v_b`. -/
theorem quillenDiff_add (u : K2 (Fin N) (Polynomial B)) (a b : B) :
    quillenDiff u (a + b) = K2Map (quillenTranslate B b) (quillenDiff u a) * quillenDiff u b := by
  rw [quillenDiff, quillenDiff, quillenDiff, map_mul, map_inv, K2Map_K2Map, K2Map_K2Map,
    quillenTranslate_comp_shift, quillenTranslate_comp_C, mul_assoc, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenDiff_add

/-- If `ev_{t=0} u = 1`, then `ρ(v_1) = u`. -/
theorem quillenDiff_one_collapse {u : K2 (Fin N) (Polynomial B)}
    (hu : K2Map (Polynomial.evalRingHom 0 : Polynomial B →+* B) u = 1) :
    K2Map (quillenCollapse B) (quillenDiff u 1) = u := by
  rw [quillenDiff, map_mul, map_inv, K2Map_K2Map, K2Map_K2Map, quillenCollapse_comp_shift_one,
    K2Map_id, quillenCollapse_comp_C, ← K2Map_K2Map, hu, map_one, inv_one, mul_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenDiff_one_collapse

theorem diesAfterPadding_quillenDiff_zero (u : K2 (Fin N) (Polynomial B)) :
    K2DiesAfterPadding (quillenDiff u 0) := by
  rw [quillenDiff_zero]
  exact diesAfterPadding_one

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_quillenDiff_zero

theorem diesAfterPadding_quillenDiff_add (u : K2 (Fin N) (Polynomial B)) {a b : B}
    (ha : K2DiesAfterPadding (quillenDiff u a)) (hb : K2DiesAfterPadding (quillenDiff u b)) :
    K2DiesAfterPadding (quillenDiff u (a + b)) := by
  rw [quillenDiff_add]
  exact diesAfterPadding_mul (diesAfterPadding_K2Map (quillenTranslate B b) ha) hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_quillenDiff_add

theorem diesAfterPadding_quillenDiff_mul (u : K2 (Fin N) (Polynomial B)) (c : B) {a : B}
    (ha : K2DiesAfterPadding (quillenDiff u a)) : K2DiesAfterPadding (quillenDiff u (c * a)) := by
  rw [← K2Map_quillenScale_quillenDiff u c a]
  exact diesAfterPadding_K2Map (quillenScale B c) ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_quillenDiff_mul

/-- **The Quillen ideal** `Q(u) = {a ∈ B : u(t + a y) · u(t)⁻¹ dies after padding}`. -/
noncomputable def quillenIdeal (u : K2 (Fin N) (Polynomial B)) : Ideal B where
  carrier := {a | K2DiesAfterPadding (quillenDiff u a)}
  add_mem' := fun ha hb ↦ diesAfterPadding_quillenDiff_add u ha hb
  zero_mem' := diesAfterPadding_quillenDiff_zero u
  smul_mem' := fun c ha ↦ diesAfterPadding_quillenDiff_mul u c ha

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenIdeal

theorem mem_quillenIdeal (u : K2 (Fin N) (Polynomial B)) (a : B) :
    a ∈ quillenIdeal u ↔ K2DiesAfterPadding (quillenDiff u a) :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.mem_quillenIdeal

/-- If `ev_{t=0} u = 1` and `1 ∈ Q(u)`, then `u` dies after padding. -/
theorem diesAfterPadding_of_one_mem_quillenIdeal {u : K2 (Fin N) (Polynomial B)}
    (hu : K2Map (Polynomial.evalRingHom 0 : Polynomial B →+* B) u = 1)
    (h1 : (1 : B) ∈ quillenIdeal u) : K2DiesAfterPadding u := by
  have h := diesAfterPadding_K2Map (quillenCollapse B) ((mem_quillenIdeal u 1).mp h1)
  rwa [quillenDiff_one_collapse hu] at h

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_of_one_mem_quillenIdeal

/-- **Patching** (the Quillen half of the local-global principle).  If `ev_{t=0} u = 1` and every
maximal ideal of `B` misses some element of the Quillen ideal `Q(u)`, then `u` dies after
padding. -/
theorem diesAfterPadding_of_local {u : K2 (Fin N) (Polynomial B)}
    (hu : K2Map (Polynomial.evalRingHom 0 : Polynomial B →+* B) u = 1)
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ s : B, s ∉ m ∧ K2DiesAfterPadding (quillenDiff u s)) :
    K2DiesAfterPadding u := by
  have htop : quillenIdeal u = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (quillenIdeal u) hne
    obtain ⟨s, hsm, hs⟩ := hloc m hm
    exact hsm (hle ((mem_quillenIdeal u s).mpr hs))
  exact diesAfterPadding_of_one_mem_quillenIdeal hu ((Ideal.eq_top_iff_one _).mp htop)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_of_local

/-- Conversely, if `u` dies after padding, then every `v_a(u)` dies after padding. -/
theorem diesAfterPadding_quillenDiff_of_diesAfterPadding {u : K2 (Fin N) (Polynomial B)}
    (hu : K2DiesAfterPadding u) (a : B) : K2DiesAfterPadding (quillenDiff u a) :=
  diesAfterPadding_mul (diesAfterPadding_K2Map (quillenShift B a) hu)
    (diesAfterPadding_inv
      (diesAfterPadding_K2Map (Polynomial.C : Polynomial B →+* Polynomial (Polynomial B)) hu))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.diesAfterPadding_quillenDiff_of_diesAfterPadding

/-- Conversely, if `u` dies after padding, then `Q(u) = B`. -/
theorem quillenIdeal_eq_top_of_diesAfterPadding {u : K2 (Fin N) (Polynomial B)}
    (hu : K2DiesAfterPadding u) : quillenIdeal u = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr ((mem_quillenIdeal u 1).mpr
    (diesAfterPadding_quillenDiff_of_diesAfterPadding hu 1))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.quillenIdeal_eq_top_of_diesAfterPadding

end QuillenIdeal

end GroupApproximation.BooneHigman.Metabelian.ElemFP
