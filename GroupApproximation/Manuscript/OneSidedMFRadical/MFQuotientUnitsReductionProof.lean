import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsPeirce

/-!
# Arbitrary units reduce to supported units

Choose two orthogonal copies of the unit. A Peirce column operation first
makes the first corner nonzero. Single-sandwich division and two elementary
operations plant an identity in the second corner. Two more Peirce operations
clear its row and column. Every operation belongs to the corner-unit subgroup,
so the resulting supported unit represents the original coset.

This discharges `AGPMenalMoncasiReduction`; no citation, K₁ hypothesis, or
generalized matrix-ring decomposition is needed for the reduction.
-/

namespace GroupApproximation
namespace MFQuotientUnits
namespace Peirce

variable {R : Type} [Ring R]

/-- Equality of right cosets, written as a subgroup membership. -/
def Congr (N : Subgroup Rˣ) (u v : Rˣ) : Prop := u * v⁻¹ ∈ N

namespace Congr

variable {N : Subgroup Rˣ} {u v w : Rˣ}

theorem refl (N : Subgroup Rˣ) (u : Rˣ) : Congr N u u := by
  show u * u⁻¹ ∈ N
  rw [mul_inv_cancel]
  exact N.one_mem

theorem trans (h : Congr N u v) (h' : Congr N v w) : Congr N u w := by
  have hm := N.mul_mem h h'
  have heq : (u * v⁻¹) * (v * w⁻¹) = u * w⁻¹ := by group
  simpa only [heq] using hm

theorem left (N : Subgroup Rˣ) (u w : Rˣ) (hw : w ∈ N) : Congr N u (w * u) := by
  show u * (w * u)⁻¹ ∈ N
  have h : u * (w * u)⁻¹ = w⁻¹ := by group
  rw [h]
  exact N.inv_mem hw

theorem right (N : Subgroup Rˣ) [N.Normal] (u w : Rˣ) (hw : w ∈ N) :
    Congr N u (u * w) := by
  show u * (u * w)⁻¹ ∈ N
  have h : u * (u * w)⁻¹ = u * w⁻¹ * u⁻¹ := by group
  rw [h]
  exact (inferInstance : N.Normal).conj_mem w⁻¹ (N.inv_mem hw) u

end Congr

theorem exists_frame (hR : IsPurelyInfiniteSimpleRing R) : Nonempty (Frame R) := by
  obtain ⟨r, hr, hortho, hequiv⟩ := exists_orthogonal_unit_family hR 2
  have hc : ∀ i : Fin 2, ∃ s t : R, t * s = 1 ∧ s * t = r i := by
    intro i
    obtain ⟨s, t, hts, hst, -, -, -, -⟩ :=
      exists_normalized_isometry IsIdempotentElem.one (hr i)
        (one_mul _) (mul_one _) (hequiv i).symm
    exact ⟨s, t, hts, hst⟩
  choose s t hts hst using hc
  refine ⟨⟨s, t, hts, ?_⟩⟩
  intro i j hij
  have hs : r j * s j = s j := by rw [← hst j, mul_assoc, hts j, mul_one]
  have ht : t i * r i = t i := by rw [← hst i, ← mul_assoc, hts i, one_mul]
  calc t i * s j = (t i * r i) * (r j * s j) := by rw [ht, hs]
    _ = t i * (r i * r j) * s j := by noncomm_ring
    _ = 0 := by rw [hortho i j hij]; simp

namespace Frame

variable (F : Frame R)

theorem e_idem (i : Fin 2) : F.e i * F.e i = F.e i := by
  simp only [e, mul_assoc, F.ts_action, ite_true]

theorem e_ne_zero [Nontrivial R] (i : Fin 2) : F.e i ≠ 0 := by
  intro hz
  have h : F.t i * (F.e i * F.s i) = 1 := by
    calc F.t i * (F.e i * F.s i) = (F.t i * F.s i) * (F.t i * F.s i) := by
          dsimp [e]; noncomm_ring
      _ = 1 := by rw [F.ts]; simp
  rw [hz, zero_mul, mul_zero] at h
  exact zero_ne_one h

def coeff (u : Rˣ) (i j : Fin 2) : R := F.t i * (u : R) * F.s j

theorem coeff_mul_root (u : Rˣ) (a b : Fin 2) (hab : a ≠ b) (c : R)
    (i j : Fin 2) :
    F.coeff (u * F.root a b hab c) i j =
      F.coeff u i j + if b = j then F.coeff u i a * c else 0 := by
  dsimp [coeff]
  rw [Units.val_mul, F.root_val]
  have h : F.t i * ((u : R) * (1 + F.s a * c * F.t b)) * F.s j =
      F.t i * (u : R) * F.s j + (F.t i * (u : R) * F.s a * c) * (F.t b * F.s j) := by
    noncomm_ring
  rw [h]
  split_ifs with hbj
  · subst j; rw [F.ts, mul_one]
  · rw [F.cross b j hbj, mul_zero]

theorem coeff_root_mul (u : Rˣ) (a b : Fin 2) (hab : a ≠ b) (c : R)
    (i j : Fin 2) :
    F.coeff (F.root a b hab c * u) i j =
      F.coeff u i j + if i = a then c * F.coeff u b j else 0 := by
  dsimp [coeff]
  rw [Units.val_mul, F.root_val]
  have h : F.t i * ((1 + F.s a * c * F.t b) * (u : R)) * F.s j =
      F.t i * (u : R) * F.s j + (F.t i * F.s a) * c * (F.t b * (u : R) * F.s j) := by
    noncomm_ring
  rw [h]
  split_ifs with hia
  · subst a; rw [F.ts, one_mul]
  · rw [F.cross i a hia, zero_mul, zero_mul]

variable [Countable R] (hR : IsPurelyInfiniteSimpleRing R)

include hR

/-- One Peirce operation suffices to make the first corner nonzero. -/
theorem exists_pivot (u : Rˣ) :
    ∃ v : Rˣ, Congr (cornerUnitSubgroup R) u v ∧ F.coeff v 0 0 ≠ 0 := by
  haveI := hR.isSimpleRing
  let e := F.e 0
  have he : e * e = e := F.e_idem 0
  have hene : e ≠ 0 := F.e_ne_zero 0
  have heu : e * (u : R) ≠ 0 := by
    intro hz
    apply hene
    calc e = (e * (u : R)) * (u⁻¹ : Rˣ) := by rw [mul_assoc, u.val_inv, mul_one]
      _ = 0 := by rw [hz, zero_mul]
  have hcorner : ∃ v : Rˣ, Congr (cornerUnitSubgroup R) u v ∧ e * (v : R) * e ≠ 0 := by
    by_cases hz : e * (u : R) * e = 0
    · obtain ⟨p, q, hpq⟩ := exists_sandwich_of_isPurelyInfiniteSimpleRing hR heu
      let x := (1 - e) * q * e
      have hl : e * x = 0 := by
        calc e * x = (e - e * e) * q * e := by dsimp [x]; noncomm_ring
          _ = 0 := by rw [he, sub_self]; simp
      have hr : x * e = x := by dsimp [x]; rw [mul_assoc, he]
      obtain ⟨w, hw, hwval⟩ := F.lower hR 0 1 (by decide) hl hr
      refine ⟨u * w, Congr.right _ u w hw, ?_⟩
      have hval : e * ((u * w : Rˣ) : R) * e = (e * (u : R)) * q * e := by
        rw [Units.val_mul, hwval]
        calc e * ((u : R) * (1 + x)) * e =
            e * (u : R) * e + (e * (u : R) - e * (u : R) * e) * q * (e * e) := by
              dsimp [x]; noncomm_ring
          _ = (e * (u : R)) * q * e := by rw [hz, he, sub_zero, zero_add]
      rw [hval]
      intro hz'
      apply hene
      calc e = (p * (e * (u : R)) * q) * e := by rw [hpq, one_mul]
        _ = p * ((e * (u : R)) * q * e) := by noncomm_ring
        _ = 0 := by rw [hz', mul_zero]
    · exact ⟨u, Congr.refl _ u, hz⟩
  obtain ⟨v, hv, hne⟩ := hcorner
  refine ⟨v, hv, ?_⟩
  intro hz
  apply hne
  calc e * (v : R) * e = F.s 0 * F.coeff v 0 0 * F.t 0 := by
        dsimp [e, Frame.e, coeff]; noncomm_ring
    _ = 0 := by rw [hz]; simp

/-- Two elementary operations plant an identity in the second corner. -/
theorem exists_identity_corner (u : Rˣ) :
    ∃ v : Rˣ, Congr (cornerUnitSubgroup R) u v ∧
      F.e 1 * (v : R) * F.e 1 = F.e 1 := by
  obtain ⟨v, huv, hv⟩ := F.exists_pivot hR u
  obtain ⟨p, q, hpq⟩ := exists_sandwich_of_isPurelyInfiniteSimpleRing hR hv
  let rho := q * (1 - p * F.coeff v 0 1)
  let v₁ := v * F.root 0 1 (by decide) rho
  have hfirst : p * F.coeff v₁ 0 1 = 1 := by
    rw [show v₁ = v * F.root 0 1 (by decide) rho from rfl, F.coeff_mul_root, if_pos rfl]
    calc p * (F.coeff v 0 1 + F.coeff v 0 0 * rho) =
        p * F.coeff v 0 1 + (p * F.coeff v 0 0 * q) * (1 - p * F.coeff v 0 1) := by
          dsimp [rho]; noncomm_ring
      _ = 1 := by rw [hpq, one_mul]; noncomm_ring
  let c := (1 - F.coeff v₁ 1 1) * p
  let v₂ := F.root 1 0 (by decide) c * v₁
  have hone : F.coeff v₂ 1 1 = 1 := by
    rw [show v₂ = F.root 1 0 (by decide) c * v₁ from rfl, F.coeff_root_mul, if_pos rfl]
    dsimp [c]
    rw [mul_assoc, hfirst, mul_one]
    noncomm_ring
  refine ⟨v₂, huv.trans ((Congr.right _ v _ (F.root_mem hR 0 1 (by decide) rho)).trans
    (Congr.left _ v₁ _ (F.root_mem hR 1 0 (by decide) c))), ?_⟩
  calc F.e 1 * (v₂ : R) * F.e 1 = F.s 1 * F.coeff v₂ 1 1 * F.t 1 := by
        dsimp [e, coeff]; noncomm_ring
    _ = F.e 1 := by rw [hone, mul_one]; rfl

/-- Clearing the identity corner produces the required supported unit. -/
theorem exists_supported (u : Rˣ) :
    ∃ v : Rˣ, Congr (cornerUnitSubgroup R) u v ∧
      (v : R) = F.e 1 + (1 - F.e 1) * (v : R) * (1 - F.e 1) := by
  obtain ⟨v, huv, hfvf⟩ := F.exists_identity_corner hR u
  let f := F.e 1
  have hf : f * f = f := F.e_idem 1
  let x := -(f * (v : R) * (1 - f))
  have hfx : f * x = x := by
    calc f * x = -((f * f) * (v : R) * (1 - f)) := by dsimp [x]; noncomm_ring
      _ = x := by rw [hf]
  have hxf : x * f = 0 := by
    calc x * f = -(f * (v : R) * (f - f * f)) := by dsimp [x]; noncomm_ring
      _ = 0 := by rw [hf, sub_self]; simp
  obtain ⟨w, hw, hwval⟩ := F.upper hR 1 0 (by decide) hfx hxf
  let d := v * w
  have hfd : f * (d : R) = f := by
    change f * ((v * w : Rˣ) : R) = f
    rw [Units.val_mul, hwval]
    calc f * ((v : R) * (1 + x)) = f * (v : R) - (f * (v : R) * f) * (v : R) * (1 - f) := by
          dsimp [x]; noncomm_ring
      _ = f * (v : R) - f * (v : R) * (1 - f) := by rw [hfvf]
      _ = f * (v : R) * f := by noncomm_ring
      _ = f := hfvf
  let y := -((1 - f) * (d : R) * f)
  have hfy : f * y = 0 := by
    calc f * y = -((f - f * f) * (d : R) * f) := by dsimp [y]; noncomm_ring
      _ = 0 := by rw [hf, sub_self]; simp
  have hyf : y * f = y := by
    calc y * f = -((1 - f) * (d : R) * (f * f)) := by dsimp [y]; noncomm_ring
      _ = y := by rw [hf]
  obtain ⟨z, hz, hzval⟩ := F.lower hR 1 0 (by decide) hfy hyf
  let result := z * d
  have hfr : f * (result : R) = f := by
    change f * ((z * d : Rˣ) : R) = f
    rw [Units.val_mul, hzval, ← mul_assoc, mul_add, mul_one, hfy, add_zero, hfd]
  have hrf : (result : R) * f = f := by
    change ((z * d : Rˣ) : R) * f = f
    rw [Units.val_mul, hzval]
    calc ((1 + y) * (d : R)) * f = (d : R) * f - (1 - f) * (d : R) * (f * (d : R)) * f := by
          dsimp [y]; noncomm_ring
      _ = (d : R) * f - (1 - f) * (d : R) * f * f := by rw [hfd]
      _ = (d : R) * f - (1 - f) * (d : R) * f := by rw [mul_assoc ((1 - f) * (d : R)), hf]
      _ = f * (d : R) * f := by noncomm_ring
      _ = f := by rw [hfd, hf]
  refine ⟨result, huv.trans ((Congr.right _ v w hw).trans (Congr.left _ d z hz)), ?_⟩
  change (result : R) = f + (1 - f) * (result : R) * (1 - f)
  have hfrf : f * (result : R) * f = f := by rw [hfr, hf]
  noncomm_ring [hfr, hrf, hfrf]

end Frame
end Peirce

/-- Every unit is congruent modulo corner units to one fixing a nonzero
idempotent. This statement does not assume that the original unit is a
commutator or is killed by a K-theory map. -/
theorem unit_reduces_to_supported {R : Type} [Ring R] [Countable R]
    (hR : IsPurelyInfiniteSimpleRing R) (u : Rˣ) :
    ∃ (v : Rˣ) (e : R), e ≠ 0 ∧ IsIdempotentElem e ∧
      (v : R) = e + (1 - e) * (v : R) * (1 - e) ∧
      u * v⁻¹ ∈ cornerUnitSubgroup R := by
  haveI := hR.isSimpleRing
  obtain ⟨F⟩ := Peirce.exists_frame hR
  obtain ⟨v, huv, hv⟩ := F.exists_supported hR u
  exact ⟨v, F.e 1, F.e_ne_zero 1, F.e_idem 1, hv, huv⟩

/-- The remaining AGP reduction interface is discharged by the explicit
Peirce operations above. -/
theorem agpMenalMoncasiReduction : AGPMenalMoncasiReduction := by
  intro R _ _ hR A _ κ _ _ u _
  exact unit_reduces_to_supported hR u

end MFQuotientUnits
end GroupApproximation

#audit_axioms GroupApproximation.MFQuotientUnits.unit_reduces_to_supported
#audit_closed_axioms GroupApproximation.MFQuotientUnits.agpMenalMoncasiReduction
