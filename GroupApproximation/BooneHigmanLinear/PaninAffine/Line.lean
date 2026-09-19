import GroupApproximation.BooneHigmanLinear.PaninAffine.Algebra

/-!
# Degree along a line, and the shear coordinate change (lane k2-panin)

* `natDegree_aeval_le_totalDegree`, `coeff_aeval_totalDegree`: substitute polynomials of
  degree `≤ 1` in `X` into `f`. The result has `X`-degree at most `totalDegree f`, and its
  top coefficient is given by the top homogeneous part of `f`.
* `shear a`: the `K`-automorphism `s₀ ↦ s₀`, `sⱼ₊₁ ↦ sⱼ₊₁ + aⱼ s₀`. After it, `f` has
  `s₀`-leading coefficient `eval a (lcPoly f) ∈ K`, where `lcPoly f ≠ 0` for `f ≠ 0`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open MvPolynomial

section LineDegree

theorem coeff_prod_sum_of_natDegree_le {ι R : Type*} [CommSemiring R] (s : Finset ι)
    (F : ι → Polynomial R) (e : ι → ℕ) (h : ∀ i ∈ s, (F i).natDegree ≤ e i) :
    (∏ i ∈ s, F i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (F i).coeff (e i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a s ha ih h
  rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
  have hs : ∀ i ∈ s, (F i).natDegree ≤ e i := fun i hi => h i (Finset.mem_insert_of_mem hi)
  rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (h a (Finset.mem_insert_self a s))
    ((Polynomial.natDegree_prod_le s F).trans (Finset.sum_le_sum hs)), ih hs]

variable {σ : Type*} [Fintype σ] {K R : Type*} [CommSemiring K] [CommSemiring R] [Algebra K R]

theorem natDegree_aeval_le_totalDegree (g : σ → Polynomial R) (hg : ∀ i, (g i).natDegree ≤ 1)
    (f : MvPolynomial σ K) : (aeval g f).natDegree ≤ f.totalDegree := by
  rw [aeval_def, eval₂_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun α hα => ?_
  rw [Polynomial.algebraMap_apply]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have hdeg : (α.sum fun _ e => e) = ∑ i, α i := Finsupp.sum_fintype _ _ (fun _ => rfl)
  have h2 : (∑ i, α i) ≤ f.totalDegree := hdeg ▸ le_totalDegree hα
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) h2
  exact (Polynomial.natDegree_pow_le).trans ((Nat.mul_le_mul le_rfl (hg i)).trans (mul_one _).le)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.natDegree_aeval_le_totalDegree

theorem coeff_aeval_totalDegree (g : σ → Polynomial R) (hg : ∀ i, (g i).natDegree ≤ 1)
    (f : MvPolynomial σ K) :
    (aeval g f).coeff f.totalDegree =
      ∑ α ∈ f.support.filter (fun α => (α.sum fun _ e => e) = f.totalDegree),
        algebraMap K R (f.coeff α) * ∏ i, (g i).coeff 1 ^ α i := by
  classical
  rw [aeval_def, eval₂_eq', Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C_mul]
  have hdeg : (α.sum fun _ e => e) = ∑ i, α i := Finsupp.sum_fintype _ _ (fun _ => rfl)
  have hpow : ∀ i, (g i ^ α i).natDegree ≤ α i := fun i =>
    (Polynomial.natDegree_pow_le).trans ((Nat.mul_le_mul le_rfl (hg i)).trans (mul_one _).le)
  split_ifs with h
  · rw [← h, hdeg, coeff_prod_sum_of_natDegree_le _ _ _ (fun i _ => hpow i)]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have h1 := Polynomial.coeff_pow_of_natDegree_le (m := α i) (hg i)
    rwa [mul_one] at h1
  · have hlt : ∑ i, α i < f.totalDegree :=
      lt_of_le_of_ne (hdeg ▸ le_totalDegree hα) (fun h' => h (hdeg.trans h'))
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
    exact ((Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun i _ => hpow i)).trans_lt
      hlt

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.coeff_aeval_totalDegree

end LineDegree

section Shear

variable {K : Type*} [Field K] {n : ℕ}

/-- The shear `s₀ ↦ s₀`, `sⱼ₊₁ ↦ sⱼ₊₁ + aⱼ s₀`, as an algebra map. -/
noncomputable def shearHom (a : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K →ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  aeval (Fin.cons (X 0) fun j => X j.succ + C (a j) * X 0)

theorem shearHom_X_zero (a : Fin n → K) : shearHom a (X 0) = X 0 := by
  simp [shearHom]

theorem shearHom_X_succ (a : Fin n → K) (j : Fin n) :
    shearHom a (X j.succ) = X j.succ + C (a j) * X 0 := by
  simp [shearHom]

theorem shearHom_comp_neg (a : Fin n → K) :
    (shearHom a).comp (shearHom (-a)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [shearHom_X_zero]
  · simp only [AlgHom.comp_apply, AlgHom.id_apply, shearHom_X_succ, map_add, map_mul,
      shearHom_X_zero, Pi.neg_apply]
    rw [show shearHom a (C (-a j)) = C (-a j) by simp [shearHom], C_neg]
    ring

/-- The shear as an algebra automorphism. -/
noncomputable def shear (a : Fin n → K) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin (n + 1)) K :=
  AlgEquiv.ofAlgHom (shearHom a) (shearHom (-a)) (shearHom_comp_neg a)
    (by simpa using shearHom_comp_neg (-a))

theorem shear_apply (a : Fin n → K) (g : MvPolynomial (Fin (n + 1)) K) :
    shear a g = shearHom a g := rfl

theorem shear_symm_apply (a : Fin n → K) (g : MvPolynomial (Fin (n + 1)) K) :
    (shear a).symm g = shearHom (-a) g := rfl

/-- The images of the variables in `K[s₁..sₙ][s₀]` after the shear. -/
noncomputable def shearLine (a : Fin n → K) : Fin (n + 1) → Polynomial (MvPolynomial (Fin n) K) :=
  Fin.cons Polynomial.X fun j => Polynomial.C (X j) + Polynomial.C (C (a j)) * Polynomial.X

theorem shearLine_natDegree_le (a : Fin n → K) (i : Fin (n + 1)) :
    (shearLine a i).natDegree ≤ 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [shearLine]
  · simp only [shearLine, Fin.cons_succ]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le (by simp) ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le))

theorem finSuccEquiv_shear (a : Fin n → K) (g : MvPolynomial (Fin (n + 1)) K) :
    finSuccEquiv K n (shear a g) = aeval (shearLine a) g := by
  have hX : ∀ i, finSuccEquiv K n (shear a (X i)) =
      aeval (shearLine a) (X i : MvPolynomial (Fin (n + 1)) K) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [shear_apply, shearHom_X_zero, finSuccEquiv_X_zero, aeval_X]
      simp [shearLine]
    · rw [shear_apply, shearHom_X_succ, map_add, map_mul, finSuccEquiv_X_succ,
        finSuccEquiv_X_zero, finSuccEquiv_C', aeval_X]
      simp [shearLine]
  induction g using MvPolynomial.induction_on with
  | C c =>
    rw [shear_apply, show shearHom a (C c) = C c by simp [shearHom], finSuccEquiv_C', aeval_C,
      Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, hX]

/-- The `s₀`-leading coefficient of the sheared polynomial, as a polynomial in the shear
parameters. -/
noncomputable def lcPoly (f : MvPolynomial (Fin (n + 1)) K) : MvPolynomial (Fin n) K :=
  ∑ α ∈ f.support.filter (fun α => (α.sum fun _ e => e) = f.totalDegree),
    monomial (Finsupp.tail α) (f.coeff α)

theorem coeff_finSuccEquiv_shear_totalDegree (a : Fin n → K) (f : MvPolynomial (Fin (n + 1)) K) :
    (finSuccEquiv K n (shear a f)).coeff f.totalDegree = C (eval a (lcPoly f)) := by
  classical
  rw [finSuccEquiv_shear, coeff_aeval_totalDegree _ (shearLine_natDegree_le a), lcPoly, map_sum,
    map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  simp [shearLine, Finsupp.tail_apply, map_prod, map_pow, MvPolynomial.algebraMap_eq,
    Polynomial.coeff_C]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.coeff_finSuccEquiv_shear_totalDegree

theorem lcPoly_ne_zero {f : MvPolynomial (Fin (n + 1)) K} (hf : f ≠ 0) : lcPoly f ≠ 0 := by
  classical
  obtain ⟨α₀, hα₀, hsup⟩ :=
    Finset.exists_mem_eq_sup f.support (support_nonempty.mpr hf) (fun s => s.sum fun _ e => e)
  have hdeg : (α₀.sum fun _ e => e) = f.totalDegree := hsup.symm
  have hsum : ∀ γ : Fin (n + 1) →₀ ℕ, (γ.sum fun _ e => e) = γ 0 + ∑ j : Fin n, γ j.succ := by
    intro γ
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ]
  rw [MvPolynomial.ne_zero_iff]
  refine ⟨Finsupp.tail α₀, ?_⟩
  rw [lcPoly, coeff_sum, Finset.sum_eq_single α₀]
  · rw [coeff_monomial, if_pos rfl]
    exact mem_support_iff.mp hα₀
  · intro β hβ hne
    rw [coeff_monomial, if_neg]
    intro htail
    apply hne
    obtain ⟨-, hβd⟩ := Finset.mem_filter.mp hβ
    have htl : ∀ j : Fin n, β j.succ = α₀ j.succ := fun j => by
      simpa [Finsupp.tail_apply] using DFunLike.congr_fun htail j
    ext i
    refine Fin.cases ?_ (fun j => htl j) i
    have h1 := hsum β
    have h2 := hsum α₀
    have h3 : ∑ j : Fin n, β j.succ = ∑ j : Fin n, α₀ j.succ :=
      Finset.sum_congr rfl fun j _ => htl j
    omega
  · intro h
    exact absurd (Finset.mem_filter.mpr ⟨hα₀, hdeg⟩) h

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.lcPoly_ne_zero

/-- After the shear, `f` is a nonzero constant times a monic polynomial in `s₀`. -/
theorem monic_finSuccEquiv_C_mul_shear (a : Fin n → K) {f : MvPolynomial (Fin (n + 1)) K}
    (ha : eval a (lcPoly f) ≠ 0) :
    (finSuccEquiv K n (C (eval a (lcPoly f))⁻¹ * shear a f)).Monic := by
  have hle : (finSuccEquiv K n (shear a f)).natDegree ≤ f.totalDegree := by
    rw [finSuccEquiv_shear]
    exact natDegree_aeval_le_totalDegree _ (shearLine_natDegree_le a) f
  have hco := coeff_finSuccEquiv_shear_totalDegree a f
  have hdeg : (finSuccEquiv K n (shear a f)).natDegree = f.totalDegree := by
    refine le_antisymm hle (Polynomial.le_natDegree_of_ne_zero ?_)
    rw [hco]
    exact MvPolynomial.C_eq_zero.not.mpr ha
  rw [map_mul, finSuccEquiv_C', Polynomial.Monic, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C, Polynomial.leadingCoeff, hdeg, hco, ← MvPolynomial.C_mul,
    inv_mul_cancel₀ ha, MvPolynomial.C_1]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.monic_finSuccEquiv_C_mul_shear

end Shear

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
