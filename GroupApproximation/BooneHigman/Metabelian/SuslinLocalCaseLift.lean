import GroupApproximation.BooneHigman.Metabelian.SuslinLocalCaseEventual
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin local case, part 3: clearing denominators for elementary matrices

Lane `bh-met-88`.  For a localization `S = M⁻¹A`:

* every polynomial over `S` comes from a polynomial over some `A_b`, `b ∈ M`
  (`suslinLocalCase_exists_poly_lift`, via `IsLocalization.integerNormalization_spec`);
* every element of `E_N(S[X])` comes from an element of `E_N(A_a[X])` for some `a ∈ M`
  (`suslinLocalCase_lift_of_mem`, closure induction with common denominators);
* **clearing denominators** (`suslinLocalCase_away_of_loc`): if the image of
  `τ ∈ GL_N(A[X])` in `GL_N(S[X])` is elementary, then so is its image in `GL_N(A_a[X])` for
  some `a ∈ M`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

variable {A : Type*} [CommRing A]

/-- Every polynomial over `S = M⁻¹A` is the image of a polynomial over some `A_b`, `b ∈ M`. -/
theorem suslinLocalCase_exists_poly_lift (S : Type*) [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] (r : Polynomial S) :
    ∃ (b : A) (hb : b ∈ M) (q : Polynomial (Localization.Away b)),
      Polynomial.map (suslinLocalCase_toLoc S hb) q = r := by
  obtain ⟨b, hb, hpb⟩ := IsLocalization.integerNormalization_spec M r
  obtain ⟨v, hv⟩ :=
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away b) b).exists_left_inv
  refine ⟨b, hb, Polynomial.C v * Polynomial.map (algebraMap A (Localization.Away b))
    (IsLocalization.integerNormalization M r), ?_⟩
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_map, suslinLocalCase_toLoc_comp S hb,
    hpb]
  ext n
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_smul, Algebra.smul_def, ← mul_assoc,
    ← suslinLocalCase_toLoc_algebraMap S hb b, ← map_mul, hv, map_one, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_exists_poly_lift

/-- Every element of `E_N(S[X])` is the image of an element of `E_N(A_a[X])`, `a ∈ M`. -/
theorem suslinLocalCase_lift_of_mem (S : Type*) [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] {N : ℕ}
    {g : Matrix.GeneralLinearGroup (Fin N) (Polynomial S)}
    (hg : g ∈ elementaryGroup (Fin N) (Polynomial S)) :
    ∃ (a : A) (ha : a ∈ M) (e : Matrix.GeneralLinearGroup (Fin N)
        (Polynomial (Localization.Away a))),
      e ∈ elementaryGroup (Fin N) (Polynomial (Localization.Away a)) ∧
        elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.mapRingHom (suslinLocalCase_toLoc S ha)) e = g := by
  have hg' : g ∈ Subgroup.closure
      {z | ∃ (i j : Fin N) (h : i ≠ j) (r : Polynomial S), elementaryUnit i j h r = z} := hg
  refine Subgroup.closure_induction
    (p := fun (x : Matrix.GeneralLinearGroup (Fin N) (Polynomial S)) _ =>
      ∃ (a : A) (ha : a ∈ M) (e : Matrix.GeneralLinearGroup (Fin N)
          (Polynomial (Localization.Away a))),
        e ∈ elementaryGroup (Fin N) (Polynomial (Localization.Away a)) ∧
          elementaryMatrixUnitMap (ι := Fin N)
            (Polynomial.mapRingHom (suslinLocalCase_toLoc S ha)) e = x) ?_ ?_ ?_ ?_ hg'
  · rintro x ⟨i, j, hij, r, rfl⟩
    obtain ⟨b, hb, q, hq⟩ := suslinLocalCase_exists_poly_lift S M r
    refine ⟨b, hb, elementaryUnit i j hij q, elementaryUnit_mem i j hij q, ?_⟩
    rw [elementaryMatrixUnitMap_elementaryUnit, Polynomial.coe_mapRingHom, hq]
  · exact ⟨1, M.one_mem, 1, one_mem _, map_one _⟩
  · intro x y _ _ hx hy
    obtain ⟨a, ha, e, he, rfl⟩ := hx
    obtain ⟨b, hb, f, hf, rfl⟩ := hy
    refine ⟨a * b, M.mul_mem ha hb,
      elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.mapRingHom (suslinLocalCase_trans (dvd_mul_right a b))) e *
        elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.mapRingHom (suslinLocalCase_trans (dvd_mul_left b a))) f,
      mul_mem (elementaryGroup_map_le (ι := Fin N) _ (Subgroup.mem_map_of_mem _ he))
        (elementaryGroup_map_le (ι := Fin N) _ (Subgroup.mem_map_of_mem _ hf)), ?_⟩
    rw [map_mul, suslinLocalCase_map_poly_comp, suslinLocalCase_map_poly_comp,
      suslinLocalCase_toLoc_comp_trans S ha (M.mul_mem ha hb) (dvd_mul_right a b),
      suslinLocalCase_toLoc_comp_trans S hb (M.mul_mem ha hb) (dvd_mul_left b a)]
  · intro x _ hx
    obtain ⟨a, ha, e, he, rfl⟩ := hx
    exact ⟨a, ha, e⁻¹, inv_mem he, map_inv _ e⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_lift_of_mem

/-- **Clearing denominators.**  If the image of `τ ∈ GL_N(A[X])` in `GL_N(S[X])` is elementary
for a localization `S = M⁻¹A`, then its image in `GL_N(A_a[X])` is elementary for some
`a ∈ M`. -/
theorem suslinLocalCase_away_of_loc (S : Type*) [CommRing S] [Algebra A S]
    (M : Submonoid A) [IsLocalization M S] {N : ℕ}
    (τ : Matrix.GeneralLinearGroup (Fin N) (Polynomial A))
    (hτ : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom (algebraMap A S)) τ ∈
      elementaryGroup (Fin N) (Polynomial S)) :
    ∃ a ∈ M, elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.mapRingHom (algebraMap A (Localization.Away a))) τ ∈
      elementaryGroup (Fin N) (Polynomial (Localization.Away a)) := by
  obtain ⟨a, ha, e, he, hea⟩ := suslinLocalCase_lift_of_mem S M hτ
  have hcomp : elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.mapRingHom (suslinLocalCase_toLoc S ha))
        (elementaryMatrixUnitMap (ι := Fin N)
          (Polynomial.mapRingHom (algebraMap A (Localization.Away a))) τ) =
      elementaryMatrixUnitMap (ι := Fin N)
        (Polynomial.mapRingHom (suslinLocalCase_toLoc S ha)) e := by
    rw [suslinLocalCase_map_poly_comp, suslinLocalCase_toLoc_comp S ha, hea]
  obtain ⟨b, hb, hbP⟩ := suslinLocalCase_eventually_units_eq S ha hcomp
  refine ⟨a * b, M.mul_mem ha hb, ?_⟩
  have h := hbP b dvd_rfl
  rw [suslinLocalCase_map_poly_comp, suslinLocalCase_trans_comp] at h
  rw [h]
  exact elementaryGroup_map_le (ι := Fin N) _ (Subgroup.mem_map_of_mem _ he)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinLocalCase_away_of_loc

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
