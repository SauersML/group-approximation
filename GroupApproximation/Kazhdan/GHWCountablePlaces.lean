import GroupApproximation.Kazhdan.GHWPlaces
import GroupApproximation.Kazhdan.GHWArchimedeanBound
import GroupApproximation.Meta.AxiomGuard

/-!
# The Guentner--Higson--Weinberger assembly over countably many places

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring` (tex lines 1146--1147):

> Every countable subgroup of `GL_2` over a field has the Haagerup property …

In characteristic zero no finite family of complex embeddings suffices in general.  The polynomials
of degree at most `n` in a transcendental `t` form a free abelian group of rank `n + 1`, which embeds
in `ℂ^m ≅ ℝ^{2m}` and so is not discrete once `n + 1 > 2m`; then the finiteness hypothesis of
`hasHaagerupProperty_of_places` fails.  This module allows countably many archimedean places.

* **Scaling** (`AffineAction.smul`): multiplying the translation part by `c` preserves the cocycle
  identity, because the linear part is linear.
* **Weights** (`AffineAction.exists_weights`): a countable family of affine actions of a countable
  group admits positive weights `w_i` with `(w_i b_i g)_i ∈ ℓ²` for every `g`.  Enumerate the group
  by `e : ℕ → G`, inject the index set by `f : ι → ℕ`, and put `M_i = ∑_{k ≤ f i} ‖b_i (e k)‖` and
  `w_i = 2^{-f i} / (1 + M_i)`.  Then `w_i ‖b_i (e k)‖ ≤ 2^{-f i}` whenever `k ≤ f i`, which holds
  for all but finitely many `i`.
* **Countable sums** (`AffineAction.countableSum`, `hasHaagerupProperty_of_countable_sum`): the
  `ℓ²`-sum of the scaled actions is an affine isometric action, and `‖b g‖ ≤ R` forces
  `‖b_i g‖ ≤ R / w_i` for every `i`.  So the sum is proper as soon as every set
  `{g : ‖b_i g‖ ≤ C_i for all i}` is finite.
* **The assembly** (`hasHaagerupProperty_of_countable_places`): the tree actions and determinant
  valuations at finitely many discrete valuations, and, at each of countably many embeddings
  `σ_i : K →+* ℂ`, the affine action of `archimedeanAffineBound_places` together with the
  translation by `log |σ_i(det)|`.  Bounded translation parts bound every entry at every place, with
  a bound depending on the place.
-/

namespace GroupApproximation
namespace Haagerup

open scoped ENNReal

universe u v

namespace AffineAction

variable {G : Type u} [Group G]

/-- The affine action with the same linear part and the translation part scaled by `c`. -/
noncomputable def smul (A : AffineAction.{u, v} G) (c : ℝ) : AffineAction.{u, v} G where
  E := A.E
  π := A.π
  b g := c • A.b g
  isCocycle g h := by
    show c • A.b (g * h) = c • A.b g + A.π g (c • A.b h)
    rw [A.isCocycle g h, smul_add, map_smul]

theorem smul_b (A : AffineAction.{u, v} G) (c : ℝ) (g : G) : (A.smul c).b g = c • A.b g :=
  rfl

theorem norm_smul_b (A : AffineAction.{u, v} G) (c : ℝ) (g : G) :
    ‖(A.smul c).b g‖ = |c| * ‖A.b g‖ := by
  have h : ‖c • A.b g‖ = |c| * ‖A.b g‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  exact h

/-- The `ℓ²`-sum of a family of affine actions whose translation parts are square-summable. -/
noncomputable def countableSum {ι : Type} (A : ι → AffineAction.{u, v} G)
    (hmem : ∀ g, Memℓp (fun i ↦ (A i).b g) 2) : AffineAction.{u, v} G where
  E := lp (fun i ↦ (A i).E) 2
  π := lpRepresentation fun i ↦ (A i).π
  b g := ⟨fun i ↦ (A i).b g, hmem g⟩
  isCocycle g h := by
    apply lp.ext
    funext i
    rw [lp.coeFn_add, Pi.add_apply]
    exact (A i).isCocycle g h

theorem norm_b_le_norm_countableSum_b {ι : Type} (A : ι → AffineAction.{u, v} G)
    (hmem : ∀ g, Memℓp (fun i ↦ (A i).b g) 2) (g : G) (i : ι) :
    ‖(A i).b g‖ ≤ ‖(countableSum A hmem).b g‖ :=
  lp.norm_apply_le_norm (E := fun i ↦ (A i).E) (p := 2) (by norm_num)
    (⟨fun i ↦ (A i).b g, hmem g⟩ : lp (fun i ↦ (A i).E) 2) i

/-- **Weights.**  A countable family of affine actions of a countable group admits positive
weights that put the scaled translation parts into `ℓ²`. -/
theorem exists_weights [Countable G] {ι : Type} [Countable ι] (A : ι → AffineAction.{u, v} G) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∀ g, Memℓp (fun i ↦ ((A i).smul (w i)).b g) 2 := by
  obtain ⟨e, he⟩ := exists_surjective_nat G
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  obtain ⟨M, hM0, hMle⟩ :
      ∃ M : ι → ℝ, (∀ i, 0 ≤ M i) ∧ ∀ i k, k ≤ f i → ‖(A i).b (e k)‖ ≤ M i := by
    refine ⟨fun i ↦ ∑ k ∈ Finset.range (f i + 1), ‖(A i).b (e k)‖,
      fun i ↦ Finset.sum_nonneg fun k _ ↦ norm_nonneg ((A i).b (e k)), fun i k hki ↦ ?_⟩
    exact Finset.single_le_sum (fun j _ ↦ norm_nonneg ((A i).b (e j)))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hki))
  have hw : ∀ i, 0 < (1 / 2 : ℝ) ^ f i / (1 + M i) :=
    fun i ↦ div_pos (pow_pos (by norm_num) _) (by linarith [hM0 i])
  have hbound : ∀ i k, k ≤ f i →
      ‖((A i).smul ((1 / 2 : ℝ) ^ f i / (1 + M i))).b (e k)‖ ^ 2 ≤ (1 / 2 : ℝ) ^ f i := by
    intro i k hki
    have hq : ‖(A i).b (e k)‖ / (1 + M i) ≤ 1 := by
      rw [div_le_iff₀ (by linarith [hM0 i])]
      linarith [hMle i k hki]
    have hx0 : 0 ≤ (1 / 2 : ℝ) ^ f i := by positivity
    have hx1 : (1 / 2 : ℝ) ^ f i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hn : ‖((A i).smul ((1 / 2 : ℝ) ^ f i / (1 + M i))).b (e k)‖ ≤ (1 / 2 : ℝ) ^ f i := by
      rw [norm_smul_b, abs_of_pos (hw i)]
      calc (1 / 2 : ℝ) ^ f i / (1 + M i) * ‖(A i).b (e k)‖
          = (1 / 2 : ℝ) ^ f i * (‖(A i).b (e k)‖ / (1 + M i)) := by ring
        _ ≤ (1 / 2 : ℝ) ^ f i * 1 := mul_le_mul_of_nonneg_left hq hx0
        _ = (1 / 2 : ℝ) ^ f i := mul_one _
    have hn0 := norm_nonneg (((A i).smul ((1 / 2 : ℝ) ^ f i / (1 + M i))).b (e k))
    nlinarith [mul_le_mul hn hn hn0 hx0, mul_le_mul_of_nonneg_left hx1 hx0]
  refine ⟨fun i ↦ (1 / 2 : ℝ) ^ f i / (1 + M i), hw, fun g ↦ ?_⟩
  obtain ⟨k, rfl⟩ := he g
  have hfin : (f ⁻¹' {n | n < k}).Finite :=
    (Set.finite_lt_nat k).preimage fun _ _ _ _ h ↦ hf h
  refine memℓp_gen ?_
  have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  simp only [e2, Real.rpow_two]
  refine Summable.of_norm_bounded_eventually (summable_geometric_two.comp_injective hf) ?_
  refine Filter.eventually_cofinite.mpr (hfin.subset fun i hi ↦ ?_)
  simp only [Set.mem_setOf_eq] at hi
  show f i < k
  by_contra hki
  exact hi ((Real.norm_of_nonneg (sq_nonneg _)).le.trans (hbound i k (not_lt.mp hki)))

end AffineAction

/-- **Countable sums of affine actions.**  A countable group has the Haagerup property if, for some
countable family of affine actions, bounding each translation part by its own constant leaves only
finitely many group elements. -/
theorem hasHaagerupProperty_of_countable_sum {G : Type u} [Group G] [Countable G]
    {ι : Type} [Countable ι] (A : ι → AffineAction.{u, v} G)
    (hproper : ∀ C : ι → ℝ, {g : G | ∀ i, ‖(A i).b g‖ ≤ C i}.Finite) :
    HasHaagerupProperty.{u, v} G := by
  obtain ⟨w, hw, hmem⟩ := AffineAction.exists_weights A
  refine ⟨{ E := (AffineAction.countableSum (fun i ↦ (A i).smul (w i)) hmem).E
            π := (AffineAction.countableSum (fun i ↦ (A i).smul (w i)) hmem).π
            b := (AffineAction.countableSum (fun i ↦ (A i).smul (w i)) hmem).b
            isCocycle := (AffineAction.countableSum (fun i ↦ (A i).smul (w i)) hmem).isCocycle
            proper := fun R ↦ (hproper fun i ↦ R / w i).subset fun g hg i ↦ ?_ }⟩
  have h1 : ‖((A i).smul (w i)).b g‖ ≤
      ‖(AffineAction.countableSum (fun i ↦ (A i).smul (w i)) hmem).b g‖ :=
    AffineAction.norm_b_le_norm_countableSum_b (fun i ↦ (A i).smul (w i)) hmem g i
  have h2 : ‖(AffineAction.countableSum (fun i ↦ (A i).smul (w i)) hmem).b g‖ ≤ R := hg
  rw [AffineAction.norm_smul_b, abs_of_pos (hw i)] at h1
  show ‖(A i).b g‖ ≤ R / w i
  rw [le_div_iff₀ (hw i)]
  linarith

end Haagerup

namespace GHW

open ValuedMatrixTwo Haagerup

/-- **The GHW assembly over countably many places.**  Let `ρ : Γ →* GL_2(K)` be injective, with all
matrix entries in `S`, let `v_j` be finitely many additive discrete valuations of `K`, each with a
uniformizer, and let `σ_i : K →+* ℂ` be countably many ring homomorphisms.  If
`{a ∈ S : |σ_i a| ≤ C_i for all i, v_j a ≥ -N for all j}` is finite for all `C` and `N`, then the
countable group `Γ` has the Haagerup property.  The archimedean input at each `σ_i` is
`archimedeanAffineBound_places ghwArchimedeanAffineBound`. -/
theorem hasHaagerupProperty_of_countable_places {K : Type} [Field K] {Γ : Type} [Group Γ]
    [Countable Γ] (ρ : Γ →* GL (Fin 2) K) (hρ : Function.Injective ρ) {k : ℕ}
    (v : Fin k → AddValuation K (WithTop ℤ)) (π : Fin k → K) (hπ : ∀ j, v j (π j) = 1)
    {ι : Type} [Countable ι] (σ : ι → (K →+* ℂ))
    (S : Set K)
    (hS : ∀ (γ : Γ) (a b : Fin 2), ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b ∈ S)
    (hfin : ∀ (C : ι → ℝ) (N : ℕ), {a : K | a ∈ S ∧ (∀ i, ‖σ i a‖ ≤ C i) ∧
      ∀ j, (((-(N : ℤ)) : ℤ) : WithTop ℤ) ≤ v j a}.Finite) :
    HasHaagerupProperty.{0, 0} Γ := by
  classical
  choose A hA using fun i ↦ archimedeanAffineBound_places ghwArchimedeanAffineBound ρ (σ i)
  let fam : (Fin k ⊕ Fin k) ⊕ (ι ⊕ ι) → AffineAction.{0, 0} Γ :=
    Sum.elim (Sum.elim (fun j ↦ valTreeAction ρ (v j) (hπ j)) fun j ↦ intAction (detValHom ρ (v j)))
      (Sum.elim A fun i ↦ realAction (logDetHom ρ (σ i)))
  refine hasHaagerupProperty_of_countable_sum fam fun C ↦ ?_
  let Rv : Fin k → ℝ := fun j ↦ max (C (Sum.inl (Sum.inl j))) (C (Sum.inl (Sum.inr j)))
  let Rs : ι → ℝ := fun i ↦ max (C (Sum.inr (Sum.inl i))) (C (Sum.inr (Sum.inr i)))
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ j, Rv j ^ 2 + Rv j < N := by
    choose Nj hNj using fun j ↦ exists_nat_gt (Rv j ^ 2 + Rv j)
    exact ⟨Finset.univ.sup Nj, fun j ↦
      (hNj j).trans_le (Nat.cast_le.mpr (Finset.le_sup (Finset.mem_univ j)))⟩
  let C' : ι → ℝ := fun i ↦ max 1 (2 * Real.exp (Rs i) * Real.exp (Rs i ^ 2))
  let F : Set K := {a : K | a ∈ S ∧ (∀ i, ‖σ i a‖ ≤ C' i) ∧
    ∀ j, (((-(N : ℤ)) : ℤ) : WithTop ℤ) ≤ v j a}
  haveI : Finite F := (hfin C' N).to_subtype
  have hmem : ∀ γ : Γ, (∀ idx, ‖(fam idx).b γ‖ ≤ C idx) →
      ∀ a b : Fin 2, ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b ∈ F := by
    intro γ hγ a b
    refine Set.mem_setOf.mpr ⟨hS γ a b, fun i ↦ ?_, fun j ↦ ?_⟩
    · have h1 : ‖(A i).b γ‖ ≤ Rs i := (hγ (Sum.inr (Sum.inl i))).trans (le_max_left _ _)
      have h2 : ‖(realAction (logDetHom ρ (σ i))).b γ‖ ≤ Rs i :=
        (hγ (Sum.inr (Sum.inr i))).trans (le_max_right _ _)
      exact norm_sigma_entry_le_of_bounds ρ (σ i) (A i) (hA i) h1 h2 a b
    · have ht : ‖(valTreeAction ρ (v j) (hπ j)).b γ‖ ≤ Rv j :=
        (hγ (Sum.inl (Sum.inl j))).trans (le_max_left _ _)
      have hd : ‖(intAction (detValHom ρ (v j))).b γ‖ ≤ Rv j :=
        (hγ (Sum.inl (Sum.inr j))).trans (le_max_right _ _)
      have hR0 : 0 ≤ Rv j := (norm_nonneg _).trans ht
      have hRN : Rv j ^ 2 ≤ N ∧ Rv j ≤ N :=
        ⟨by nlinarith [hN j], by nlinarith [hN j, sq_nonneg (Rv j)]⟩
      by_cases hab : ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b = 0
      · rw [hab, AddValuation.map_zero]
        exact le_top
      · have h := neg_le_vz_entry_of_bounds ρ (v j) (hπ j) hRN ht hd a b hab
        rw [← coe_vz (v j) hab]
        exact WithTop.coe_le_coe.mpr h
  have hfinSet : Finite {γ : Γ | ∀ idx, ‖(fam idx).b γ‖ ≤ C idx} := by
    refine Finite.of_injective (fun γ ↦ fun a b : Fin 2 ↦ (⟨_, hmem γ.1 γ.2 a b⟩ : F)) ?_
    intro γ δ h
    apply Subtype.ext
    apply hρ
    refine Matrix.GeneralLinearGroup.ext fun a b ↦ ?_
    exact congrArg Subtype.val (congrFun (congrFun h a) b)
  exact Set.finite_coe_iff.mp hfinSet

end GHW
end GroupApproximation

#audit_axioms GroupApproximation.Haagerup.AffineAction.exists_weights
#audit_axioms GroupApproximation.Haagerup.hasHaagerupProperty_of_countable_sum
#audit_axioms GroupApproximation.GHW.hasHaagerupProperty_of_countable_places
