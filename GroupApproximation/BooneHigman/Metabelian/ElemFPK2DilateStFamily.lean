import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateStLift
import GroupApproximation.Meta.AxiomGuard

/-!
# The eventual families attached to points of the pullback

Lane `bh-met-90s`, family module.  Notation as in `ElemFPK2DilateStRing`.

For `q ∈ P` with chosen lift `ι_κ φ = q`, put `F_r(q) = μ_{s^{r-κ}} φ ∈ A[X]`
(`k2DilateSt_family`).  This is the colimit `colim (A[X], μ_s) ≅ P` made explicit: `F(q)` does
not depend on the lift for large `r`, and `F` is eventually additive and multiplicative.

* `k2DilateSt_scale_eventually_eq`: if `ι_k f = ι_l g` then `μ_{s^{r-k}} f = μ_{s^{r-l}} g` for
  all large `r`.  The difference `μ_{s^l} f - μ_{s^k} g` lies in the kernel of `ι_{k+l}`, which
  is killed by dilation (`k2DilateSt_eventually_of_stage`).
* `k2DilateSt_family_eventually`: for every lift `ι_k f = q`, eventually `F_r(q) = μ_{s^{r-k}} f`.
* `k2DilateSt_family_add`, `k2DilateSt_family_mul`: eventually `F_r(p ∘ q) = F_r(p) ∘ F_r(q)`.
* `k2DilateSt_family_base`: eventually `F_r(ι_0 f) = μ_{s^r} f`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

section DilateStFamily

variable {A : Type*} [CommRing A]

/-- **Independence of the lift.**  If `ι_k f = ι_l g`, then eventually
`μ_{s^{r-k}} f = μ_{s^{r-l}} g`. -/
theorem k2DilateSt_scale_eventually_eq {s : A} {k l : ℕ} {f g : Polynomial A}
    (h : k2DilateSt_stage s k f = k2DilateSt_stage s l g) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r →
      k2CubeDilate_scale A (s ^ (r - k)) f = k2CubeDilate_scale A (s ^ (r - l)) g := by
  have hd : k2DilateSt_stage s (k + l)
      (k2CubeDilate_scale A (s ^ l) f - k2CubeDilate_scale A (s ^ k) g) = 0 := by
    rw [map_sub, k2DilateSt_stage_scale, add_comm k l, k2DilateSt_stage_scale, h, sub_self]
  obtain ⟨m, hm⟩ := k2DilateSt_eventually_of_stage hd
  refine ⟨m + k + l, fun r hr ↦ ?_⟩
  have e := hm (r - k - l) (by omega)
  rw [map_sub, sub_eq_zero, k2DilateSt_scale_scale, k2DilateSt_scale_scale] at e
  have e1 : l + (r - k - l) = r - k := by omega
  have e2 : k + (r - k - l) = r - l := by omega
  rw [e1, e2] at e
  exact e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_scale_eventually_eq

/-- The family `F_r(q) = μ_{s^{r-κ}} φ` attached to `q ∈ P` with chosen lift `ι_κ φ = q`. -/
noncomputable def k2DilateSt_family (s : A) (r : ℕ) (q : k2DilateSt_pullback s) :
    Polynomial A :=
  k2CubeDilate_scale A (s ^ (r - k2DilateSt_liftStage s q)) (k2DilateSt_liftPoly s q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_family

/-- For every lift `ι_k f = q`, eventually `F_r(q) = μ_{s^{r-k}} f`. -/
theorem k2DilateSt_family_eventually {s : A} {q : k2DilateSt_pullback s} {k : ℕ}
    {f : Polynomial A} (hf : k2DilateSt_stage s k f = (q : A × Polynomial (Localization.Away s))) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r → k2DilateSt_family s r q = k2CubeDilate_scale A (s ^ (r - k)) f :=
  k2DilateSt_scale_eventually_eq ((k2DilateSt_stage_lift s q).trans hf.symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_family_eventually

theorem k2DilateSt_family_add_of {s : A} {p q : k2DilateSt_pullback s} {k l : ℕ}
    {f g : Polynomial A} (hp : k2DilateSt_stage s k f = (p : A × Polynomial (Localization.Away s)))
    (hq : k2DilateSt_stage s l g = (q : A × Polynomial (Localization.Away s))) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r →
      k2DilateSt_family s r (p + q) = k2DilateSt_family s r p + k2DilateSt_family s r q := by
  have h : k2DilateSt_stage s (k + l)
      (k2CubeDilate_scale A (s ^ l) f + k2CubeDilate_scale A (s ^ k) g) =
        (p : A × Polynomial (Localization.Away s)) + q := by
    rw [map_add, k2DilateSt_stage_scale, add_comm k l, k2DilateSt_stage_scale, hp, hq]
  obtain ⟨m₁, h₁⟩ := k2DilateSt_family_eventually (q := p + q) h
  obtain ⟨m₂, h₂⟩ := k2DilateSt_family_eventually hp
  obtain ⟨m₃, h₃⟩ := k2DilateSt_family_eventually hq
  refine ⟨m₁ + m₂ + m₃ + k + l, fun r hr ↦ ?_⟩
  rw [h₁ r (by omega), h₂ r (by omega), h₃ r (by omega), map_add, k2DilateSt_scale_scale,
    k2DilateSt_scale_scale]
  have e1 : l + (r - (k + l)) = r - k := by omega
  have e2 : k + (r - (k + l)) = r - l := by omega
  rw [e1, e2]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_family_add_of

theorem k2DilateSt_family_mul_of {s : A} {p q : k2DilateSt_pullback s} {k l : ℕ}
    {f g : Polynomial A} (hp : k2DilateSt_stage s k f = (p : A × Polynomial (Localization.Away s)))
    (hq : k2DilateSt_stage s l g = (q : A × Polynomial (Localization.Away s))) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r →
      k2DilateSt_family s r (p * q) = k2DilateSt_family s r p * k2DilateSt_family s r q := by
  have h : k2DilateSt_stage s (k + l)
      (k2CubeDilate_scale A (s ^ l) f * k2CubeDilate_scale A (s ^ k) g) =
        (p : A × Polynomial (Localization.Away s)) * q := by
    rw [map_mul, k2DilateSt_stage_scale, add_comm k l, k2DilateSt_stage_scale, hp, hq]
  obtain ⟨m₁, h₁⟩ := k2DilateSt_family_eventually (q := p * q) h
  obtain ⟨m₂, h₂⟩ := k2DilateSt_family_eventually hp
  obtain ⟨m₃, h₃⟩ := k2DilateSt_family_eventually hq
  refine ⟨m₁ + m₂ + m₃ + k + l, fun r hr ↦ ?_⟩
  rw [h₁ r (by omega), h₂ r (by omega), h₃ r (by omega), map_mul, k2DilateSt_scale_scale,
    k2DilateSt_scale_scale]
  have e1 : l + (r - (k + l)) = r - k := by omega
  have e2 : k + (r - (k + l)) = r - l := by omega
  rw [e1, e2]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_family_mul_of

/-- `F` is eventually additive. -/
theorem k2DilateSt_family_add (s : A) (p q : k2DilateSt_pullback s) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r →
      k2DilateSt_family s r (p + q) = k2DilateSt_family s r p + k2DilateSt_family s r q :=
  k2DilateSt_family_add_of (k2DilateSt_stage_lift s p) (k2DilateSt_stage_lift s q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_family_add

/-- `F` is eventually multiplicative. -/
theorem k2DilateSt_family_mul (s : A) (p q : k2DilateSt_pullback s) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r →
      k2DilateSt_family s r (p * q) = k2DilateSt_family s r p * k2DilateSt_family s r q :=
  k2DilateSt_family_mul_of (k2DilateSt_stage_lift s p) (k2DilateSt_stage_lift s q)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_family_mul

/-- On the image of `ι_0`, eventually `F_r(ι_0 f) = μ_{s^r} f`. -/
theorem k2DilateSt_family_base (s : A) (f : Polynomial A) :
    ∃ m : ℕ, ∀ r : ℕ, m ≤ r →
      k2DilateSt_family s r (k2DilateSt_toPullback s 0 f) = k2CubeDilate_scale A (s ^ r) f := by
  obtain ⟨m, hm⟩ := k2DilateSt_family_eventually (q := k2DilateSt_toPullback s 0 f)
    (k2DilateSt_coe_toPullback s 0 f).symm
  exact ⟨m, fun r hr ↦ by rw [hm r hr, Nat.sub_zero]⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2DilateSt_family_base

end DilateStFamily

end GroupApproximation.BooneHigman.Metabelian.ElemFP
