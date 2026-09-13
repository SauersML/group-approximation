import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetPlacement
import GroupApproximation.Algebra.ReturnTowerEmbeddings
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the placement inside the return kernel

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1752–1755:

> Over $\F_2$, Theorem~\ref{thm:core-mf-radical} kills the whole
> return kernel in the embedded group in the stated rank ranges.
> That kernel contains the phase-zero placement of every $g\in K_n(J)$,
> which $\Phi$ sends to $(1-p_C)I_n+g$.

For a return tower `τ` with `a_0 = b_0 = p_C` and a ring isomorphism `θ : A ≃+* P_C`, the phase-zero
placement of `DynamicRankBudgetPlacement` is carried back to `GL_{nr}(A)` along the block transport
`τ.blockTransport θ n` (`Algebra/ReturnTowerEmbeddings`):

* `glEmbedding_returnPlacement`: the embedding `τ.glEmbedding θ n` sends it to `g`;
* `returnPlacement_sub_one_mem`: if the deviation of `g` has entries in an ideal `I_R` of `R`, and
  `θ` pulls corner elements of `I_R` back into an ideal `I_A` of `A` (printed "The return transient
  ideal is therefore $J=p_CIp_C$", tex 1750), then its deviation has entries in `I_A`;
* `units_map_mapMatrix_eq_one_of_forall_mem_ker`: a unit whose deviation has entries in `ker f` lies
  in the kernel of `GL(f)`, so the placement lies in the return kernel.
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

open MFQuotientUnits ReturnTowerUnits

section Kernel

variable {A B : Type*} [Ring A] [Ring B] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A unit whose deviation has all entries in `ker f` is in the kernel of `GL(f)`. -/
theorem units_map_mapMatrix_eq_one_of_forall_mem_ker (f : A →+* B) (y : (Matrix ι ι A)ˣ)
    (h : ∀ p q, ((y : Matrix ι ι A) - 1) p q ∈ TwoSidedIdeal.ker f) :
    Units.map (RingHom.mapMatrix f).toMonoidHom y = 1 := by
  refine Units.ext (Matrix.ext fun p q => ?_)
  have hp := (TwoSidedIdeal.mem_ker f).1 (h p q)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at hp
  change ((y : Matrix ι ι A).map f) p q = (1 : Matrix ι ι B) p q
  rw [Matrix.map_apply, hp]
  by_cases hpq : p = q
  · subst hpq
    simp
  · simp [Matrix.one_apply_ne hpq]

end Kernel

variable {R A : Type*} [Ring R] [Ring A] {N r : ℕ} (τ : ReturnTowerUnits R N r)
  (θ : A ≃+* τ.Base)

theorem coe_base_sub (x y : τ.Base) : ((x - y : τ.Base) : R) = (x : R) - (y : R) :=
  rfl

/-- **"which $\Phi$ sends to $(1-p_C)I_n+g$"**, in `GL_{nr}(A)`: the embedding sends the transported
placement to `g`. -/
theorem glEmbedding_returnPlacement (n : ℕ) (hr : 0 < r) (ha : τ.a (τ.lo ⟨0, hr⟩) = τ.p)
    (hb : τ.b (τ.lo ⟨0, hr⟩) = τ.p) (g : (Matrix (Fin n) (Fin n) R)ˣ)
    (hg : IsCornerDeviation τ (g : Matrix (Fin n) (Fin n) R)) :
    τ.glEmbedding θ n ((τ.blockTransport θ n).symm (placementUnit τ hr ha hb g hg)) = g := by
  rw [glEmbedding_eq, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    unitizeGL_placementUnit]

/-- The block identity, entrywise through `θ`. -/
theorem coe_theta_one_apply (n : ℕ) (i j : Fin n) (a b : Fin r) :
    ((θ ((1 : Matrix (Fin (n * r)) (Fin (n * r)) A) (finProdFinEquiv (i, a))
        (finProdFinEquiv (j, b))) : τ.Base) : R) =
      (((1 : Matrix (Fin n) (Fin n) (Matrix (Fin r) (Fin r) τ.Base)) i j a b : τ.Base) : R) := by
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl, map_one]
    · rw [if_neg (fun h => hab (Prod.ext_iff.1 (finProdFinEquiv.injective h)).2), if_neg hab,
        map_zero]
  · rw [if_neg (fun h => hij (Prod.ext_iff.1 (finProdFinEquiv.injective h)).1), if_neg hij,
      map_zero, Matrix.zero_apply]

/-- **The transported placement lies in the return kernel** (tex 1754, "That kernel contains the
phase-zero placement"): its deviation has entries in `I_A` as soon as the deviation of `g` has
entries in `I_R` and `θ` pulls corner elements of `I_R` back into `I_A`. -/
theorem returnPlacement_sub_one_mem (n : ℕ) (hr : 0 < r) (ha : τ.a (τ.lo ⟨0, hr⟩) = τ.p)
    (hb : τ.b (τ.lo ⟨0, hr⟩) = τ.p) (g : (Matrix (Fin n) (Fin n) R)ˣ)
    (hg : IsCornerDeviation τ (g : Matrix (Fin n) (Fin n) R)) (I_R : TwoSidedIdeal R)
    (I_A : TwoSidedIdeal A) (hgI : ∀ i j, ((g : Matrix (Fin n) (Fin n) R) - 1) i j ∈ I_R)
    (hJ : ∀ c : A, ((θ c : τ.Base) : R) ∈ I_R → c ∈ I_A) (p q : Fin (n * r)) :
    (((τ.blockTransport θ n).symm (placementUnit τ hr ha hb g hg) :
        Matrix (Fin (n * r)) (Fin (n * r)) A) - 1) p q ∈ I_A := by
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective q
  apply hJ
  have hbt := coe_blockTransport_apply τ θ n
    ((τ.blockTransport θ n).symm (placementUnit τ hr ha hb g hg)) i j a b
  rw [MulEquiv.apply_symm_apply, coe_placementUnit] at hbt
  have e2 : placement τ hr (g : Matrix (Fin n) (Fin n) R) i j a b -
      (1 : Matrix (Fin n) (Fin n) (Matrix (Fin r) (Fin r) τ.Base)) i j a b =
      (placement τ hr (g : Matrix (Fin n) (Fin n) R) - 1) i j a b := by
    rw [Matrix.sub_apply, Matrix.sub_apply]
  rw [Matrix.sub_apply, map_sub, coe_base_sub, ← hbt, coe_theta_one_apply, ← coe_base_sub, e2,
    coe_placement_sub_one_apply τ hr hg i j a b]
  split_ifs
  · exact hgI i j
  · exact I_R.zero_mem

end GroupApproximation.ChainCore.DynamicRankBudget

/-! ### Audit -/

#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.units_map_mapMatrix_eq_one_of_forall_mem_ker
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.glEmbedding_returnPlacement
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.coe_theta_one_apply
#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.returnPlacement_sub_one_mem
