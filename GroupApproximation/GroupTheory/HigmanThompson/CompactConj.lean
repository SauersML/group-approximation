import GroupApproximation.GroupTheory.HigmanThompson.CompactE
import GroupApproximation.GroupTheory.HigmanThompson.GeometricF
import GroupApproximation.Meta.AxiomGuard

/-!
# Conjugating the half-line model onto a bounded interval

`compE m r` is a strictly increasing bijection of `ℚ` onto `(-∞, r)`.  Conjugating by it
(`compConj`) is an injective homomorphism `Equiv.Perm ℚ →* Equiv.Perm ℚ`: a permutation `g`
becomes `t ↦ E (g (E⁻¹ t))` on `(-∞, r)` and the identity on `[r, ∞)`.

`compactF m r` is the geometric group of the interval: piecewise linear permutations over
`(ℤ[1/n], n^ℤ)` fixing `(-∞, 0]` and `[r, ∞)` pointwise.  The follow-up module identifies
`geoF m` with `compactF m r` through `compConj`; this module sets up the map and the group.
-/

namespace GroupApproximation
namespace HigmanThompson

variable (m r : ℕ)

/-- The inverse of `compE` on `(-∞, r)`, extended by the identity. -/
noncomputable def compEinv (t : ℚ) : ℚ :=
  if h : t < r then Classical.choose (compE_surj m r h) else t

theorem compE_compEinv {t : ℚ} (ht : t < r) : compE m r (compEinv m r t) = t := by
  simp only [compEinv, dif_pos ht]
  exact Classical.choose_spec (compE_surj m r ht)

theorem compEinv_compE (u : ℚ) : compEinv m r (compE m r u) = u :=
  (compE_strictMono m r).injective (compE_compEinv m r (compE_lt m r u))

theorem compEinv_of_le {t : ℚ} (h : t ≤ (r : ℚ) - 1) : compEinv m r t = t := by
  have ht : t < r := by linarith
  have h1 : compE m r t = t := compE_of_le m r h
  calc compEinv m r t = compEinv m r (compE m r t) := by rw [h1]
    _ = t := compEinv_compE m r t

theorem compEinv_strictMonoOn {s t : ℚ} (hs : s < r) (ht : t < r) (hst : s < t) :
    compEinv m r s < compEinv m r t := by
  by_contra h
  have h' := (compE_strictMono m r).monotone (not_lt.mp h)
  rw [compE_compEinv m r ht, compE_compEinv m r hs] at h'
  exact absurd hst (not_lt.mpr h')

/-- The conjugate of `g` by `compE`, as a function. -/
noncomputable def compConjFun (g : Equiv.Perm ℚ) (t : ℚ) : ℚ :=
  if t < r then compE m r (g (compEinv m r t)) else t

theorem compConjFun_of_lt (g : Equiv.Perm ℚ) {t : ℚ} (ht : t < r) :
    compConjFun m r g t = compE m r (g (compEinv m r t)) := by
  simp [compConjFun, ht]

theorem compConjFun_of_ge (g : Equiv.Perm ℚ) {t : ℚ} (ht : (r : ℚ) ≤ t) :
    compConjFun m r g t = t := by
  simp [compConjFun, not_lt.mpr ht]

theorem compConjFun_lt (g : Equiv.Perm ℚ) {t : ℚ} (ht : t < r) : compConjFun m r g t < r := by
  rw [compConjFun_of_lt m r g ht]
  exact compE_lt m r _

theorem compConjFun_mul (g h : Equiv.Perm ℚ) (t : ℚ) :
    compConjFun m r (g * h) t = compConjFun m r g (compConjFun m r h t) := by
  by_cases ht : t < r
  · rw [compConjFun_of_lt m r _ ht, compConjFun_of_lt m r g (compConjFun_lt m r h ht),
      compConjFun_of_lt m r h ht, compEinv_compE, Equiv.Perm.mul_apply]
  · have ht' : (r : ℚ) ≤ t := not_lt.mp ht
    rw [compConjFun_of_ge m r _ ht', compConjFun_of_ge m r h ht', compConjFun_of_ge m r g ht']

theorem compConjFun_one (t : ℚ) : compConjFun m r 1 t = t := by
  by_cases ht : t < r
  · rw [compConjFun_of_lt m r _ ht, Equiv.Perm.one_apply, compE_compEinv m r ht]
  · exact compConjFun_of_ge m r 1 (not_lt.mp ht)

/-- **Conjugation by `compE`**, as a permutation. -/
noncomputable def compConj (g : Equiv.Perm ℚ) : Equiv.Perm ℚ where
  toFun := compConjFun m r g
  invFun := compConjFun m r g⁻¹
  left_inv t := by
    rw [← compConjFun_mul, inv_mul_cancel, compConjFun_one]
  right_inv t := by
    rw [← compConjFun_mul, mul_inv_cancel, compConjFun_one]

@[simp] theorem compConj_apply (g : Equiv.Perm ℚ) (t : ℚ) :
    compConj m r g t = compConjFun m r g t := rfl

/-- **Conjugation by `compE` is a homomorphism.** -/
noncomputable def compConjHom : Equiv.Perm ℚ →* Equiv.Perm ℚ where
  toFun := compConj m r
  map_one' := by
    ext t
    exact compConjFun_one m r t
  map_mul' g h := by
    ext t
    exact compConjFun_mul m r g h t

theorem compConjHom_apply (g : Equiv.Perm ℚ) (t : ℚ) :
    compConjHom m r g t = compConjFun m r g t := rfl

/-- **Conjugation by `compE` is injective.** -/
theorem compConjHom_injective : Function.Injective (compConjHom m r) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  ext u
  have h := congrArg (fun p : Equiv.Perm ℚ => p (compE m r u)) hg
  simp only [compConjHom_apply, Equiv.Perm.one_apply] at h
  rw [compConjFun_of_lt m r g (compE_lt m r u), compEinv_compE] at h
  exact (compE_strictMono m r).injective h

/-- **The interval model `F_{n,r}`**: piecewise linear permutations over `(ℤ[1/n], n^ℤ)`
fixing `(-∞, 0]` and `[r, ∞)` pointwise. -/
def compactF : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | f ∈ PLGroup (m + 2) (powSlopes m) ∧ (∀ t : ℚ, t ≤ 0 → f t = t) ∧
    ∀ t : ℚ, (r : ℚ) ≤ t → f t = t}
  one_mem' := ⟨(PLGroup (m + 2) (powSlopes m)).one_mem, fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨hf, hf0, hfr⟩ ⟨hg, hg0, hgr⟩
    refine ⟨(PLGroup (m + 2) (powSlopes m)).mul_mem hf hg, fun t ht => ?_, fun t ht => ?_⟩
    · show f (g t) = t
      rw [hg0 t ht, hf0 t ht]
    · show f (g t) = t
      rw [hgr t ht, hfr t ht]
  inv_mem' := by
    rintro f ⟨hf, hf0, hfr⟩
    refine ⟨(PLGroup (m + 2) (powSlopes m)).inv_mem hf, fun t ht => ?_, fun t ht => ?_⟩
    · rw [Equiv.Perm.inv_eq_iff_eq, hf0 t ht]
    · rw [Equiv.Perm.inv_eq_iff_eq, hfr t ht]

#audit_axioms GroupApproximation.HigmanThompson.compConjHom_injective

end HigmanThompson
end GroupApproximation
