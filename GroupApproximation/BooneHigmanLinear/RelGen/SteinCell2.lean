import GroupApproximation.BooneHigmanLinear.RelGen.SteinCell1
import Mathlib.Algebra.Group.Subgroup.Pointwise
import GroupApproximation.Meta.AxiomGuard

/-!
# Stein's theorem, part 5: the column, row and `K`-block groups at a new index `L`

Lane bh-pal-wire, k2-poly H.L3. Let `K` be a finset and `L ∉ K` a new index. Over an ideal `J`:

* `colG K L = ⟨x_iL(J) : i ∈ K⟩`, `colExG K L b = ⟨x_iL(J) : i ∈ K, i ≠ b⟩`,
  `rowG K L = ⟨x_Lj(J) : j ∈ K⟩`, `colBG K b = ⟨x_kb(J) : k ∈ K⟩`;
* `qGroup K = ⟨x_ij(J) : i, j ∈ K⟩ ⊔ H̄(R, J)`.

Facts used by the big-cell step (`RelGen.SteinCell3`):

* `split_col`: every `c ∈ colG` is `x_bL(d) · c'` with `d ∈ J` and `c' ∈ colExG` (the column is
  abelian);
* `row_mul_colEx`: `x_Lb(m) c' = c' q₀ x_Lb(m)` with `q₀ ∈ colBG K b`, for `c' ∈ colExG`;
* `qGroup_conj_rowG`, `qGroup_conj_colG`: `qGroup K` normalizes `rowG` and `colG`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R] (J : Ideal R)

/-- `⟨x_iL(J) : i ∈ K⟩`. -/
abbrev colG (K : Finset I) (L : I) : Subgroup (SteinbergGroup I R) :=
  rootGroup I J (fun i j => i ∈ K ∧ j = L)

/-- `⟨x_iL(J) : i ∈ K, i ≠ b⟩`. -/
abbrev colExG (K : Finset I) (L b : I) : Subgroup (SteinbergGroup I R) :=
  rootGroup I J (fun i j => i ∈ K ∧ i ≠ b ∧ j = L)

/-- `⟨x_Lj(J) : j ∈ K⟩`. -/
abbrev rowG (K : Finset I) (L : I) : Subgroup (SteinbergGroup I R) :=
  rootGroup I J (fun i j => i = L ∧ j ∈ K)

/-- `⟨x_kb(J) : k ∈ K⟩`. -/
abbrev colBG (K : Finset I) (b : I) : Subgroup (SteinbergGroup I R) :=
  rootGroup I J (fun i j => i ∈ K ∧ j = b)

/-- `⟨x_ij(J) : i, j ∈ K⟩ ⊔ H̄(R, J)`. -/
abbrev qGroup (K : Finset I) : Subgroup (SteinbergGroup I R) :=
  rootGroup I J (fun i j => i ∈ K ∧ j ∈ K) ⊔ hBar I J

variable {J}

/-- `x_bL(d)` commutes with every element of `colExG K L b`. -/
theorem commute_colEx {K : Finset I} {L b : I} (hbL : b ≠ L) (d : R) {c : SteinbergGroup I R}
    (hc : c ∈ colExG J K L b) : Commute (x b L hbL d) c := by
  have hle : colExG J K L b ≤ Subgroup.centralizer {x b L hbL d} := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, j, hij, s, ⟨-, -, rfl⟩, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_col hbL hij d s).eq.symm
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commute_colEx

/-- **The column splits.** Every `c ∈ colG K L` is `x_bL(d) c'` with `d ∈ J`, `c' ∈ colExG`. -/
theorem split_col {K : Finset I} {L b : I} (hbL : b ≠ L) {c : SteinbergGroup I R}
    (hc : c ∈ colG J K L) : ∃ d ∈ J, ∃ c' ∈ colExG J K L b, c = x b L hbL d * c' := by
  rw [colG, rootGroup] at hc
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨i, j, hij, s, ⟨hi, rfl⟩, hs, rfl⟩ := hc
    by_cases hib : i = b
    · subst hib
      exact ⟨s, hs, 1, Subgroup.one_mem _, by rw [mul_one]⟩
    · exact ⟨0, J.zero_mem, _, x_mem_rootGroup hij ⟨hi, hib, rfl⟩ hs, by rw [x_zero, one_mul]⟩
  | one => exact ⟨0, J.zero_mem, 1, Subgroup.one_mem _, by rw [x_zero, one_mul]⟩
  | mul c₁ c₂ _ _ h₁ h₂ =>
    obtain ⟨d₁, hd₁, c₁', hc₁', rfl⟩ := h₁
    obtain ⟨d₂, hd₂, c₂', hc₂', rfl⟩ := h₂
    refine ⟨d₁ + d₂, J.add_mem hd₁ hd₂, c₁' * c₂', Subgroup.mul_mem _ hc₁' hc₂', ?_⟩
    rw [← x_mul, show x b L hbL d₁ * c₁' * (x b L hbL d₂ * c₂') =
      x b L hbL d₁ * (c₁' * x b L hbL d₂) * c₂' by group, ← (commute_colEx hbL d₂ hc₁').eq]
    group
  | inv c _ h₁ =>
    obtain ⟨d, hd, c', hc', rfl⟩ := h₁
    refine ⟨-d, neg_mem hd, c'⁻¹, Subgroup.inv_mem _ hc', ?_⟩
    rw [mul_inv_rev, x_neg, ← ((commute_colEx hbL d hc').inv_inv).eq]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.split_col

/-- Elements of `colBG K b` commute with elements of `colExG K L b` (`L ∉ K`). -/
theorem commute_colB_colEx {K : Finset I} {L b : I} (hLK : L ∉ K) {q c : SteinbergGroup I R}
    (hq : q ∈ colBG J K b) (hc : c ∈ colExG J K L b) : Commute q c := by
  have hle : colBG J K b ≤ Subgroup.centralizer (colExG J K L b : Set (SteinbergGroup I R)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, b', hkb, s, ⟨hk, rfl⟩, -, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro c hc
    have hle2 : colExG J K L b ≤ Subgroup.centralizer {x k b hkb s} := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, j, hij, t, ⟨hi, hib, rfl⟩, -, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hkL : k ≠ L := fun e => hLK (e ▸ hk)
      exact (x_commute_of_ne k b i L hkb hij (fun e => hib e.symm) (fun e => hkL e.symm) s
        t).eq.symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle2 hc)
  exact (Subgroup.mem_centralizer_iff.mp (hle hq) c hc).symm

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commute_colB_colEx

/-- **The row moves past the reduced column.** For `b ∈ K`, `L ∉ K` and `c' ∈ colExG K L b`,
`x_Lb(m) c' = c' q₀ x_Lb(m)` with `q₀ ∈ colBG K b`. -/
theorem row_mul_colEx {K : Finset I} {L b : I} (hLK : L ∉ K) (hLb : L ≠ b) (m : R)
    {c : SteinbergGroup I R} (hc : c ∈ colExG J K L b) :
    ∃ q ∈ colBG J K b, x L b hLb m * c = c * q * x L b hLb m := by
  rw [colExG, rootGroup] at hc
  induction hc using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨k, j, hkj, e, ⟨hk, hkb, rfl⟩, he, rfl⟩ := hc
    refine ⟨x k b hkb (-e * m), x_mem_rootGroup hkb ⟨hk, rfl⟩
      (J.mul_mem_right m (neg_mem he)), ?_⟩
    have h1 : (x k L hkj e)⁻¹ * x L b hLb m * x k L hkj e = x k b hkb (-e * m) * x L b hLb m :=
      calc (x k L hkj e)⁻¹ * x L b hLb m * x k L hkj e
          = x k L hkj (-e) * x L b hLb m * (x k L hkj (-e))⁻¹ := by rw [x_neg, inv_inv]
        _ = ⁅x k L hkj (-e), x L b hLb m⁆ * x L b hLb m := conj_eq_commutator_mul _ _
        _ = x k b hkb (-e * m) * x L b hLb m := by rw [x_commutator k L b hkj hLb hkb]
    calc x L b hLb m * x k L hkj e
        = x k L hkj e * ((x k L hkj e)⁻¹ * x L b hLb m * x k L hkj e) := by group
      _ = x k L hkj e * (x k b hkb (-e * m) * x L b hLb m) := by rw [h1]
      _ = _ := by group
  | one => exact ⟨1, Subgroup.one_mem _, by group⟩
  | mul c₁ c₂ _ h₂m h₁ h₂ =>
    obtain ⟨q₁, hq₁, e₁⟩ := h₁
    obtain ⟨q₂, hq₂, e₂⟩ := h₂
    refine ⟨q₁ * q₂, Subgroup.mul_mem _ hq₁ hq₂, ?_⟩
    have hcomm : q₁ * c₂ = c₂ * q₁ := (commute_colB_colEx hLK hq₁ h₂m).eq
    calc x L b hLb m * (c₁ * c₂)
        = (x L b hLb m * c₁) * c₂ := by group
      _ = c₁ * q₁ * (x L b hLb m * c₂) := by rw [e₁]; group
      _ = c₁ * (q₁ * c₂) * q₂ * x L b hLb m := by rw [e₂]; group
      _ = c₁ * c₂ * (q₁ * q₂) * x L b hLb m := by rw [hcomm]; group
  | inv c hcm h₁ =>
    obtain ⟨q, hq, e⟩ := h₁
    refine ⟨q⁻¹, Subgroup.inv_mem _ hq, ?_⟩
    have hqc : q⁻¹ * c = c * q⁻¹ := ((commute_colB_colEx hLK hq hcm).inv_left).eq
    exact (calc c⁻¹ * q⁻¹ * x L b hLb m
        = c⁻¹ * q⁻¹ * (x L b hLb m * c) * c⁻¹ := by group
      _ = c⁻¹ * q⁻¹ * (c * q * x L b hLb m) * c⁻¹ := by rw [e]
      _ = c⁻¹ * (q⁻¹ * c) * q * x L b hLb m * c⁻¹ := by group
      _ = c⁻¹ * (c * q⁻¹) * q * x L b hLb m * c⁻¹ := by rw [hqc]
      _ = x L b hLb m * c⁻¹ := by group).symm

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.row_mul_colEx

section Normalize

variable (third : ThirdIndex I)
include third

/-- `qGroup K` normalizes `rowG K L` (`L ∉ K`). -/
theorem qGroup_le_normalizer_rowG {K : Finset I} {L : I} (hLK : L ∉ K) :
    qGroup J K ≤ (rowG J K L).normalizer := by
  rw [qGroup, rootGroup, ← Subgroup.closure_eq (hBar I J), ← Subgroup.closure_union]
  refine closure_le_normalizer ?_ ?_
  · rintro g (⟨i, j, hij, s, ⟨hi, hj⟩, hs, rfl⟩ | hg) y hy
    · refine conj_x_rootGroup hij s ?_ ?_ ?_ hy
      · rintro ⟨rfl, -⟩
        exact hLK hj
      · rintro j' ⟨rfl, -⟩
        exact absurd hj hLK
      · rintro i' ⟨rfl, -⟩ -
        exact ⟨rfl, hj⟩
    · exact hBar_conj_rootGroup third hg hy
  · rintro g (⟨i, j, hij, s, hP, hs, rfl⟩ | hg)
    · exact Or.inl ⟨i, j, hij, -s, hP, neg_mem hs, by rw [x_neg]⟩
    · exact Or.inr (Subgroup.inv_mem _ hg)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.qGroup_le_normalizer_rowG

/-- `qGroup K` normalizes `colG K L` (`L ∉ K`). -/
theorem qGroup_le_normalizer_colG {K : Finset I} {L : I} (hLK : L ∉ K) :
    qGroup J K ≤ (colG J K L).normalizer := by
  rw [qGroup, rootGroup, ← Subgroup.closure_eq (hBar I J), ← Subgroup.closure_union]
  refine closure_le_normalizer ?_ ?_
  · rintro g (⟨i, j, hij, s, ⟨hi, hj⟩, hs, rfl⟩ | hg) y hy
    · refine conj_x_rootGroup hij s ?_ ?_ ?_ hy
      · rintro ⟨-, rfl⟩
        exact hLK hi
      · rintro j' ⟨-, rfl⟩ -
        exact ⟨hi, rfl⟩
      · rintro i' ⟨-, rfl⟩
        exact absurd hi hLK
    · exact hBar_conj_rootGroup third hg hy
  · rintro g (⟨i, j, hij, s, hP, hs, rfl⟩ | hg)
    · exact Or.inl ⟨i, j, hij, -s, hP, neg_mem hs, by rw [x_neg]⟩
    · exact Or.inr (Subgroup.inv_mem _ hg)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.qGroup_le_normalizer_colG

end Normalize

end GroupApproximation.BooneHigmanLinear.RelGen
