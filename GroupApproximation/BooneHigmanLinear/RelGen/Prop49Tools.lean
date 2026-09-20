import GroupApproximation.BooneHigmanLinear.RelGen.CEltCentral
import GroupApproximation.BooneHigmanLinear.RelGen.SteinNormal
import GroupApproximation.BooneHigmanLinear.RelGen.Lemma46Mem
import GroupApproximation.Meta.AxiomGuard

/-!
# Tools for L–S Proposition 4.9

Lane bh-pal-wire, k2-poly H.L3.

* `commutator_closure_le`: for a normal `T`, `⁅⟨S₁⟩, ⟨S₂⟩⁆ ≤ T` as soon as `⁅a, b⁆ ∈ T` for
  `a ∈ S₁`, `b ∈ S₂`.
* `sup_normal_of_commutator_mem`: if `⁅d, g⁆ ∈ N` for all `d ∈ D` and all `g`, with `N` normal,
  then `N ⊔ D` is normal.
* `hBar_map_le`: a ring map sends `H̄(R, J)` into `H̄(S, J')` when it sends `1 + J` into `1 + J'`.
* `commutator_x_mem_relKer`: `⁅x_kl(u), x_ij(v)⁆ ∈ St̄(R, J)` when `u v ∈ J` and
  `(k, l) ≠ (j, i)`.
* `commutator_x_hBar_mem`: `⁅x_kl(u), g⁆ ∈ St̄(R, J')` for `g ∈ H̄(R, J)` and `u J ⊆ J'`.
* `commutator_cElt_mem_relKer`: `⁅c_ij(s, t), g⁆ ∈ St̄(R, J)` for every `g` when `s t ∈ J`, since
  `c_ij(s, t)` is central modulo `J` (`cElt_central_of_mul_eq_zero`).
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h)

/-- For a normal `T`, commutators of generators in `T` give `⁅⟨S₁⟩, ⟨S₂⟩⁆ ≤ T`. -/
theorem commutator_closure_le {G : Type*} [Group G] {T : Subgroup G} (hT : T.Normal)
    {S₁ S₂ : Set G} (hgen : ∀ a ∈ S₁, ∀ b ∈ S₂, ⁅a, b⁆ ∈ T) :
    ⁅Subgroup.closure S₁, Subgroup.closure S₂⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  have key : ∀ a ∈ S₁, ∀ y ∈ Subgroup.closure S₂, ⁅a, y⁆ ∈ T := by
    intro a ha y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact hgen a ha y hy
    | one => rw [commutatorElement_one_right]; exact T.one_mem
    | mul y₁ y₂ _ _ h₁ h₂ =>
      rw [show ⁅a, y₁ * y₂⁆ = ⁅a, y₁⁆ * (y₁ * ⁅a, y₂⁆ * y₁⁻¹) by
        simp only [commutatorElement_def]; group]
      exact T.mul_mem h₁ (hT.conj_mem _ h₂ y₁)
    | inv y _ h₁ =>
      rw [show ⁅a, y⁻¹⁆ = y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ by simp only [commutatorElement_def]; group]
      exact hT.conj_mem _ (T.inv_mem h₁) y⁻¹
  intro g₁ hg₁ g₂ hg₂
  induction hg₁ using Subgroup.closure_induction with
  | mem a ha => exact key a ha g₂ hg₂
  | one => rw [commutatorElement_one_left]; exact T.one_mem
  | mul a₁ a₂ _ _ h₁ h₂ =>
    rw [commutator_mul_left']
    exact T.mul_mem (hT.conj_mem _ h₂ a₁) h₁
  | inv a _ h₁ =>
    rw [show ⁅a⁻¹, g₂⁆ = a⁻¹ * ⁅a, g₂⁆⁻¹ * a⁻¹⁻¹ by simp only [commutatorElement_def]; group]
    exact hT.conj_mem _ (T.inv_mem h₁) a⁻¹

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commutator_closure_le

/-- If `⁅d, g⁆ ∈ N` for all `d ∈ D` and all `g`, with `N` normal, then `N ⊔ D` is normal. -/
theorem sup_normal_of_commutator_mem {G : Type*} [Group G] {N D : Subgroup G} (hN : N.Normal)
    (hD : ∀ d ∈ D, ∀ g : G, ⁅d, g⁆ ∈ N) : (N ⊔ D).Normal := by
  have e : N ⊔ D = Subgroup.closure ((N : Set G) ∪ D) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hle : ⁅N ⊔ D, Subgroup.closure (Set.univ : Set G)⁆ ≤ N := by
    rw [e]
    refine commutator_closure_le hN fun a ha b _ => ?_
    rcases ha with ha | ha
    · rw [show ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) by simp only [commutatorElement_def]; group]
      exact N.mul_mem ha (hN.conj_mem _ (N.inv_mem ha) b)
    · exact hD a ha b
  refine ⟨fun y hy g => ?_⟩
  have hc : ⁅y, g⁆ ∈ N :=
    hle (Subgroup.commutator_mem_commutator hy (Subgroup.subset_closure (Set.mem_univ g)))
  rw [show g * y * g⁻¹ = ⁅y, g⁆⁻¹ * y by simp only [commutatorElement_def]; group]
  exact (N ⊔ D).mul_mem (Subgroup.mem_sup_left (N.inv_mem hc)) hy

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.sup_normal_of_commutator_mem

variable {I : Type*} [Fintype I] [DecidableEq I] {R S : Type*} [CommRing R] [CommRing S]

/-- A ring map sending `1 + J` into `1 + J'` sends `H̄(R, J)` into `H̄(S, J')`. -/
theorem hBar_map_le (f : R →+* S) {J : Ideal R} {J' : Ideal S}
    (hf : ∀ u : Rˣ, u ∈ unitsOneAdd J → Units.map f.toMonoidHom u ∈ unitsOneAdd J') :
    (hBar I J).map (ringMap f) ≤ hBar I J' := by
  refine Subgroup.map_le_iff_le_comap.mpr ((Subgroup.closure_le _).mpr ?_)
  rintro _ (⟨i, j, hij, u, hu, rfl⟩ | ⟨i, j, hij, u, v, huv, rfl⟩)
  · show ringMap f (h i j hij u) ∈ hBar I J'
    rw [ringMap_h]
    exact h_mem_hBar hij (hf u hu)
  · show ringMap f (h i j hij (u * v) * (h i j hij u)⁻¹ * (h i j hij v)⁻¹) ∈ hBar I J'
    simp only [map_mul, map_inv, ringMap_h]
    rcases huv with hu | hv
    · exact csym_mem_hBar_left hij (hf u hu) _
    · exact csym_mem_hBar_right hij _ (hf v hv)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.hBar_map_le

variable {J : Ideal R}

/-- `⁅x_kl(u), x_ij(v)⁆ ∈ St̄(R, J)` when `u v ∈ J` and `(k, l) ≠ (j, i)`. -/
theorem commutator_x_mem_relKer {k l i j : I} (hkl : k ≠ l) (hij : i ≠ j) {u v : R}
    (huv : u * v ∈ J) (hne : ¬(k = j ∧ l = i)) :
    ⁅x k l hkl u, x i j hij v⁆ ∈ relKer I J := by
  by_cases h1 : l = i
  · subst h1
    have hkj : k ≠ j := fun e => hne ⟨e, rfl⟩
    rw [x_commutator k l j hkl hij hkj]
    exact mem_relKer_of_x hkj huv
  · by_cases h2 : j = k
    · subst h2
      have hil : i ≠ l := fun e => h1 e.symm
      rw [← commutatorElement_inv, x_commutator i j l hij hkl hil, ← x_neg]
      exact mem_relKer_of_x hil (neg_mem (by rw [mul_comm]; exact huv))
    · rw [(x_commute_of_ne k l i j hkl hij h1 h2 u v).commutator_eq]
      exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commutator_x_mem_relKer

/-- `⁅x_kl(u), g⁆ ∈ St̄(R, J')` for `g ∈ H̄(R, J)` when `u J ⊆ J'`: `g` acts on `x_kl` by a
scalar `c ≡ 1 mod J`, so the commutator is `x_kl(u - c u)`. -/
theorem commutator_x_hBar_mem (third : ThirdIndex I) {J' : Ideal R} {k l : I} (hkl : k ≠ l)
    {u : R} (hu : ∀ c ∈ J, u * c ∈ J') {g : SteinbergGroup I R} (hg : g ∈ hBar I J) :
    ⁅x k l hkl u, g⁆ ∈ relKer I J' := by
  obtain ⟨c, hc⟩ := hBar_conj_x third hkl hg
  have hc1 : (c : R) - 1 ∈ J := scalar_sub_one_mem hkl (hBar_le_relKer hg) (hc 1)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc g, ← x_neg, hc, x_mul]
  refine mem_relKer_of_x hkl ?_
  rw [show u + (c : R) * -u = -(u * ((c : R) - 1)) by ring]
  exact neg_mem (hu _ hc1)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commutator_x_hBar_mem

/-- If `s t ∈ J`, then `⁅c_ij(s, t), g⁆ ∈ St̄(R, J)` for every `g`. -/
theorem commutator_cElt_mem_relKer (third : ThirdIndex I) {i j : I} (hij : i ≠ j) {s t : R}
    (hst : s * t ∈ J) (g : SteinbergGroup I R) : ⁅cElt i j hij s t, g⁆ ∈ relKer I J := by
  refine mem_relKer_iff_ringMap.mpr ?_
  rw [map_commutatorElement, ringMap_cElt]
  exact (cElt_central_of_mul_eq_zero hij (mk_mul_mk_eq_zero hst) third _).commutator_eq

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commutator_cElt_mem_relKer

end GroupApproximation.BooneHigmanLinear.RelGen
