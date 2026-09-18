import Mathlib.Algebra.MvPolynomial.Nilpotent
import GroupApproximation.BooneHigman.Metabelian.VdKDiagEndpoint
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.Meta.AxiomGuard

/-!
# The diagonal statement is equivalent to the row-core residual

Lane `bh-met-90v`.  Target: `vdkInj_DiagStatement`, by a route that uses the specialization
hypothesis on `u` (every ring map `ψ : R_k → R_j`, `j < k`, kills `u`), leaving a residual
strictly weaker than lane `bh-met-90p`'s `vdkDiag_RowCoreStatement`.

## LOUD: no such residual exists

The specialization hypothesis gives **no logical leverage**.  Here `R_k = F_p[s_1, …, s_k]`.

* `vdkRowCoreX_two_le`: `sr(R_k) ≤ r` with `k > 0` forces `r ≥ 2`.  The row
  `(1 + s_1, s_1²)` is unimodular, because `(1 + s_1)(1 - s_1) + s_1² = 1`.  But
  `1 + s_1 + b s_1²` is never a unit, because its `s_1`-coefficient is `1`, which is not
  nilpotent.
* `vdkRowCoreX_stableRangeLE_of_retract`: `sr ≤ r` passes to ring retracts, so `sr(R_j) ≤ r`
  for `j ≤ k` (`rename`/`killCompl`).
* `vdkRowCoreX_injective_of_diag`: by strong induction on `j` at the **fixed rank `r + 3`**,
  `vdkInj_DiagStatement` gives injectivity of `K2Stab (r + 3)` on all of `K₂(r + 3, R_j)`
  whenever `sr(R_j) ≤ r`.
  - Base case: `j = 0` is the field case `vdkRowExt_fieldStab`, using `r + 3 ≥ 5`.
  - Step: for `j > 0`, naturality gives `K2Stab (ψ u) = ψ (K2Stab u) = 1`.  The induction
    hypothesis at `i < j`, using `sr(R_i) ≤ r` by retract, gives `ψ u = 1`.  So the
    specialization hypothesis holds automatically.
* `vdkRowCoreX_diag_iff_injective`: hence the diagonal statement is equivalent to plain
  injective stability of `K2Stab (r + 3)` over `R_k` (`k > 0`, `sr ≤ r`), with no hypothesis
  on `u`.
* `vdkRowCoreX_rowCore_of_diag`, `vdkRowCoreX_diag_iff_rowCore`: through the coset row data
  (`vdkRowDataOfInjective`), the diagonal statement is **equivalent** to
  `vdkDiag_RowCoreStatement`.

So every Statement `S` with `vdkDiag_RowCoreStatement → S → vdkInj_DiagStatement` is
equivalent to both.  A residual strictly weaker than `vdkDiag_RowCoreStatement` that still
implies the target cannot exist.  Instancewise, at a fixed `k`, `Diag_k` is weaker than
`RowCore_k`.  But `Diag` at every `j < k` already recovers the instance hypothesis, so any gain
is lost once all `j < k` are needed.  This is the same collapse as
`K2InjStabSpecializationStatement` (lane `bh-met-80`).

## Why routes (a) and (b) were not taken

* (a) Build a `vdkDiag_RowCore` on an explicit `X` only in the specialized situation.  A
  `RowCore` does not depend on `u`, so no specialization hypothesis on `u` can enter its
  construction.
  - Taking `X` to be a general `St`-set whose stabilizers meet `P̃` trivially is instancewise
    equivalent to the diagonal statement, through the coset construction.
  - The explicit choice `X = St / ι(K₂(n, R_{k-1}))` gives a `ker ev₀`-type statement, which
    is instancewise stronger.
* (b) A direct proof of the diagonal statement is, by the equivalence above, a proof of
  van der Kallen's injective stability at rank `r + 3` over `R_k`.  That is not available
  without literature inputs.

## Remaining gap

`vdkInj_DiagStatement` itself, or equivalently `vdkDiag_RowCoreStatement`.  It is true, because
it follows from `vdkStab_InjStabStatement` (`vdkDiag_rowCore_of_injStab`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **Stable range passes to retracts**: if `g ∘ f = id` and `sr(B) ≤ r`, then `sr(A) ≤ r`. -/
theorem vdkRowCoreX_stableRangeLE_of_retract {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B →+* A) (hgf : g.comp f = RingHom.id A) {r : ℕ}
    (h : vdkStab_StableRangeLE B r) : vdkStab_StableRangeLE A r := by
  have hgf' : ∀ x, g (f x) = x := fun x ↦ RingHom.congr_fun hgf x
  intro n hn v hv
  obtain ⟨b, hb⟩ := h n hn (fun i ↦ f (v i)) (vdkStab_isUnimodular_map f (fun _ ↦ rfl) hv)
  refine ⟨fun i ↦ g (b i), vdkStab_isUnimodular_map g (fun i ↦ ?_) hb⟩
  simp only [vdkStab_reduceRow_apply, map_add, map_mul, hgf']

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_stableRangeLE_of_retract

/-- The row `(a, c)` of length two. -/
def vdkRowCoreX_row {R : Type*} [CommRing R] (a c : R) : Fin (1 + 1) → R :=
  Fin.snoc (α := fun _ ↦ R) (fun _ ↦ a) c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_row

theorem vdkRowCoreX_row_castSucc {R : Type*} [CommRing R] (a c : R) (i : Fin 1) :
    vdkRowCoreX_row a c i.castSucc = a :=
  Fin.snoc_castSucc (α := fun _ ↦ R) c (fun _ ↦ a) i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_row_castSucc

theorem vdkRowCoreX_row_last {R : Type*} [CommRing R] (a c : R) :
    vdkRowCoreX_row a c (Fin.last 1) = c :=
  Fin.snoc_last (α := fun _ ↦ R) c (fun _ ↦ a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_row_last

theorem vdkRowCoreX_sum_row {R : Type*} [CommRing R] (a c a' c' : R) :
    ∑ i, vdkRowCoreX_row a c i * vdkRowCoreX_row a' c' i = a * a' + c * c' := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_one]
  simp only [vdkRowCoreX_row_castSucc, vdkRowCoreX_row_last]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_sum_row

/-- The `s_i`-coefficient of `1 + s_i + c s_i²` is `1`. -/
theorem vdkRowCoreX_coeff_eq_one {p k : ℕ} (i : Fin k) (c : MvPolynomial (Fin k) (ZMod p)) :
    MvPolynomial.coeff (Finsupp.single i 1)
      (1 + MvPolynomial.X i + c * MvPolynomial.X i ^ 2) = 1 := by
  have h0 : Finsupp.single i 1 ≠ (0 : Fin k →₀ ℕ) := Finsupp.single_ne_zero.mpr one_ne_zero
  have h2 : ¬ Finsupp.single i 2 ≤ Finsupp.single i 1 := by
    rw [Finsupp.single_le_iff, Finsupp.single_eq_same]
    omega
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_one, if_neg h0.symm,
    MvPolynomial.coeff_X_same, MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial',
    if_neg h2, zero_add, add_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_coeff_eq_one

/-- **`sr(F_p[s_1, …, s_k]) ≥ 2` for `k > 0`**: the unimodular row `(1 + s_1, s_1²)` is not
reducible, since `1 + s_1 + b s_1²` has `s_1`-coefficient `1`, hence is not a unit. -/
theorem vdkRowCoreX_two_le {p : ℕ} (hp : p.Prime) {k r : ℕ} (hk : 0 < k)
    (h : vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) r) : 2 ≤ r := by
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  by_contra hr
  obtain ⟨b, w, hw⟩ := vdkStab_stableRangeLE_mono h (show r ≤ 1 by omega) 1 le_rfl
    (vdkRowCoreX_row (1 + MvPolynomial.X ⟨0, hk⟩) (MvPolynomial.X ⟨0, hk⟩ ^ 2))
    ⟨vdkRowCoreX_row (1 - MvPolynomial.X ⟨0, hk⟩) 1, by rw [vdkRowCoreX_sum_row]; ring⟩
  rw [Fin.sum_univ_one, vdkStab_reduceRow_apply, vdkRowCoreX_row_castSucc,
    vdkRowCoreX_row_last] at hw
  have hu := (MvPolynomial.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hw)).2
    (Finsupp.single ⟨0, hk⟩ 1) (Finsupp.single_ne_zero.mpr one_ne_zero)
  rw [vdkRowCoreX_coeff_eq_one] at hu
  exact not_isNilpotent_one hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_two_le

/-- **The diagonal statement gives full injective stability at rank `r + 3`**, by strong
induction on the number of variables: the specialization hypothesis is supplied by the lower
instances. -/
theorem vdkRowCoreX_injective_of_diag (h : vdkInj_DiagStatement) {p : ℕ} (hp : p.Prime)
    {r : ℕ} (h2 : 2 ≤ r) (j : ℕ) :
    vdkStab_StableRangeLE (MvPolynomial (Fin j) (ZMod p)) r →
      Function.Injective (K2Stab (r + 3) (MvPolynomial (Fin j) (ZMod p))) := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact vdkRowExt_fieldStab p hp (r + 3) (by omega)
    refine (injective_iff_map_eq_one _).mpr fun u hu ↦ ?_
    refine h p hp j r hj0 hj u (fun i hi ψ ↦ ?_) hu
    have hv : K2Stab (r + 3) (MvPolynomial (Fin i) (ZMod p)) (K2Map ψ u) = 1 :=
      (k2InjStab_K2Stab_K2Map ψ u).trans
        ((DFunLike.congr_arg (K2Map (I := Fin (r + 3 + 1)) ψ) hu).trans
          (map_one (K2Map (I := Fin (r + 3 + 1)) ψ)))
    have hi' : vdkStab_StableRangeLE (MvPolynomial (Fin i) (ZMod p)) r :=
      vdkRowCoreX_stableRangeLE_of_retract
        (MvPolynomial.rename (R := ZMod p) (Fin.castLE hi.le)).toRingHom
        (MvPolynomial.killCompl (R := ZMod p) (Fin.castLE_injective hi.le)).toRingHom
        (RingHom.ext fun x ↦ MvPolynomial.killCompl_rename_app (Fin.castLE_injective hi.le) x)
        hj
    exact ih i hi hi' (hv.trans (map_one (K2Stab (r + 3) (MvPolynomial (Fin i) (ZMod p)))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_injective_of_diag

/-- **Strength**: the diagonal statement is equivalent to plain injective stability of
`K2Stab (r + 3)` over `F_p[s_1, …, s_k]` for `k > 0` and `sr ≤ r`. -/
theorem vdkRowCoreX_diag_iff_injective : vdkInj_DiagStatement ↔
    ∀ p : ℕ, p.Prime → ∀ k r : ℕ, 0 < k →
      vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) r →
        Function.Injective (K2Stab (r + 3) (MvPolynomial (Fin k) (ZMod p))) := by
  refine ⟨fun h p hp k r hk hsr ↦
    vdkRowCoreX_injective_of_diag h hp (vdkRowCoreX_two_le hp hk hsr) k hsr, fun h ↦ ?_⟩
  intro p hp k r hk hsr u _ hu
  exact h p hp k r hk hsr (hu.trans (map_one (K2Stab (r + 3) (MvPolynomial (Fin k) (ZMod p)))).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_diag_iff_injective

/-- **The diagonal statement gives the row-core residual**, through the coset row data. -/
theorem vdkRowCoreX_rowCore_of_diag (h : vdkInj_DiagStatement) : vdkDiag_RowCoreStatement := by
  intro p hp k r hk hsr
  have hK := vdkRowCoreX_injective_of_diag h hp (vdkRowCoreX_two_le hp hk hsr) k hsr
  exact ⟨VdKRowCoset (r + 3) (MvPolynomial (Fin k) (ZMod p)), ⟨0, by omega⟩,
    ⟨Quotient.mk (QuotientGroup.rightRel
      (vdkRowParSubgroup (r + 3) (MvPolynomial (Fin k) (ZMod p)))) 1⟩,
    ⟨vdkDiag_RowCore.ofRowData
      (vdkRowDataOfInjective (vdkRowParInjective_of_K2Stab_injective hK)) _⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_rowCore_of_diag

/-- **LOUD: equivalence.**  `vdkInj_DiagStatement` and `vdkDiag_RowCoreStatement` are
equivalent, so no residual strictly between them exists. -/
theorem vdkRowCoreX_diag_iff_rowCore : vdkInj_DiagStatement ↔ vdkDiag_RowCoreStatement :=
  ⟨vdkRowCoreX_rowCore_of_diag, vdkDiag_diag_of_rowCore⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_diag_iff_rowCore

end GroupApproximation.BooneHigman.Metabelian.ElemFP
