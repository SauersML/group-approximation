import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarNormRoots
import GroupApproximation.Meta.AxiomGuard

/-!
# `H(J)` is normal (given a third index)

Lane `bh-met-92f`.  The remaining case is the conjugate of `z_ij(a, r)` by `x_ij(s)`.  Pick
`m ∉ {i, j}`.  By `k2KarInj_conj_opp`,
`z_ij(a, r) = ⁅x_jm(r a) x_im(a), x_mi(-r) x_mj(1)⁆`.  Conjugating by `x_ij(s)` gives
`⁅X, Y⁆` with `X = x_im(s r a) x_jm(r a) x_im(a) ∈ H(J)` and
`Y = x_mi(-r) x_mj(r s + 1)`.  Now `⁅X, Y⁆ = X · (Y X⁻¹ Y⁻¹)`, and `Y`-conjugates of
`x_jm(b)` and `x_im(b)` (`b ∈ J`) lie in `H(J)` by the cases of `ElemFPK2KarNormRoots` only.
So there is no circularity.  Then `k2KarNorm_H_normal`: `H(J)` is normal in `St(ι, R)` when any
two indices miss a third one.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

section KarNormHard

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] {J : Ideal R}

/-- `(k, l) = (i, j)`, using a third index `m`. -/
theorem k2KarNorm_conj_z_same (i j m : ι) (hij : i ≠ j) (hmi : m ≠ i) (hmj : m ≠ j) (s : R)
    {a : R} (ha : a ∈ J) (r : R) :
    x i j hij s * k2KarNorm_z i j hij a r * (x i j hij s)⁻¹ ∈ k2KarNorm_H ι J := by
  have him : i ≠ m := Ne.symm hmi
  have hjm : j ≠ m := Ne.symm hmj
  have ez : k2KarNorm_z i j hij a r =
      ⁅x j m hjm (r * a) * x i m him a, x m i hmi (-r) * x m j hmj 1⁆ := by
    have e := k2KarInj_conj_opp i j m hij him hjm r a 1
    simp only [mul_one, one_mul] at e
    rw [k2KarNorm_z]
    exact e
  have hX : x i j hij s * (x j m hjm (r * a) * x i m him a) * (x i j hij s)⁻¹ =
      x i m him (s * (r * a)) * x j m hjm (r * a) * x i m him a := by
    rw [k2KarNorm_conj_mul,
      k2KarNorm_conj_of_commute (x_commute_of_ne i j i m hij him hij.symm hmi s a),
      ← x_commutator i j m hij hjm him s (r * a), commutatorElement_def]
    group
  have hY : x i j hij s * (x m i hmi (-r) * x m j hmj 1) * (x i j hij s)⁻¹ =
      x m i hmi (-r) * x m j hmj (-(-r * s) + 1) := by
    have c : x i j hij s * x m i hmi (-r) * (x i j hij s)⁻¹ =
        x m j hmj (-(-r * s)) * x m i hmi (-r) := by
      rw [x_neg m j hmj, ← x_commutator m i j hmi hij hmj (-r) s, commutatorElement_def]
      group
    rw [k2KarNorm_conj_mul,
      k2KarNorm_conj_of_commute (x_commute_of_ne i j m j hij hmj hjm hij.symm s 1), c,
      (x_commute_of_ne m j m i hmj hmi hjm him (-(-r * s)) (-r)).eq, mul_assoc, x_mul]
  obtain ⟨X, hXd⟩ : ∃ X : SteinbergGroup ι R,
      X = x i m him (s * (r * a)) * x j m hjm (r * a) * x i m him a := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : SteinbergGroup ι R,
      Y = x m i hmi (-r) * x m j hmj (-(-r * s) + 1) := ⟨_, rfl⟩
  have hra : r * a ∈ J := Ideal.mul_mem_left J r ha
  have hXm : X ∈ k2KarNorm_H ι J := by
    rw [hXd]
    exact mul_mem (mul_mem (k2KarNorm_x_mem i m him (Ideal.mul_mem_left J s hra))
      (k2KarNorm_x_mem j m hjm hra)) (k2KarNorm_x_mem i m him ha)
  have hQj : ∀ b ∈ J, Y * x j m hjm b * Y⁻¹ ∈ k2KarNorm_H ι J := by
    intro b hb
    rw [hYd, k2KarNorm_conj_conj]
    exact k2KarNorm_conj_z_right j m i hjm hmi hij.symm (-r) hb (-(-r * s) + 1)
  have hQi : ∀ b ∈ J, Y * x i m him b * Y⁻¹ ∈ k2KarNorm_H ι J := by
    intro b hb
    rw [hYd, k2KarNorm_conj_conj, k2KarNorm_C1 i m j him hmj hij b, k2KarNorm_conj_mul]
    exact mul_mem
      (k2KarNorm_conj_x m i hmi (-r) i j hij (neg_mem (Ideal.mul_mem_right _ J hb)))
      (k2KarNorm_z_mem i m him hb (-r))
  have hXinv : X⁻¹ = x i m him (-a) * x j m hjm (-(r * a)) * x i m him (-(s * (r * a))) := by
    rw [hXd]
    simp only [x_neg]
    group
  have hconj : Y * X⁻¹ * Y⁻¹ ∈ k2KarNorm_H ι J := by
    rw [hXinv, k2KarNorm_conj_mul, k2KarNorm_conj_mul]
    exact mul_mem (mul_mem (hQi _ (neg_mem ha)) (hQj _ (neg_mem hra)))
      (hQi _ (neg_mem (Ideal.mul_mem_left J s hra)))
  rw [ez, k2KarNorm_conj_commutator, hX, hY, ← hXd, ← hYd, commutatorElement_def,
    show X * Y * X⁻¹ * Y⁻¹ = X * (Y * X⁻¹ * Y⁻¹) by group]
  exact mul_mem hXm hconj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_z_same

/-- Every conjugate of `z_ij(a, r)` by a root `x_kl(s)` lies in `H(J)` (third index given). -/
theorem k2KarNorm_conj_z (h3 : ∀ i j : ι, ∃ m : ι, m ≠ i ∧ m ≠ j) (k l : ι) (hkl : k ≠ l)
    (s : R) (i j : ι) (hij : i ≠ j) {a : R} (ha : a ∈ J) (r : R) :
    x k l hkl s * k2KarNorm_z i j hij a r * (x k l hkl s)⁻¹ ∈ k2KarNorm_H ι J := by
  obtain ⟨m, hmi, hmj⟩ := h3 i j
  by_cases hki : k = i
  · subst hki
    by_cases hlj : l = j
    · subst hlj
      exact k2KarNorm_conj_z_same _ _ m hij hmi hmj s ha r
    · exact k2KarNorm_conj_z_rowp _ _ _ hij hkl (Ne.symm hlj) s ha r
  · by_cases hkj : k = j
    · subst hkj
      by_cases hli : l = i
      · subst hli
        exact k2KarNorm_conj_z_opp _ _ hij s ha r
      · exact k2KarNorm_conj_z_right _ _ _ hij hkl (Ne.symm hli) s ha r
    · by_cases hli : l = i
      · subst hli
        exact k2KarNorm_conj_z_left _ _ _ hij hkl hkj s ha r
      · by_cases hlj : l = j
        · subst hlj
          exact k2KarNorm_conj_z_colq _ _ _ hij hki hkl s ha r
        · exact k2KarNorm_conj_z_far k l hkl i j hij hki hkj hli hlj s ha r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_conj_z

/-- A subgroup stable under conjugation by every root `x_kl(s)` is normal. -/
theorem k2KarNorm_normal_of_roots {H : Subgroup (SteinbergGroup ι R)}
    (h : ∀ (k l : ι) (hkl : k ≠ l) (s : R) (n : SteinbergGroup ι R), n ∈ H →
      x k l hkl s * n * (x k l hkl s)⁻¹ ∈ H) : H.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  intro g _
  refine PresentedGroup.generated_by _ _ ?_ g
  rintro ⟨k, l, hkl, s⟩
  change x k l hkl s ∈ Subgroup.normalizer (H : Set (SteinbergGroup ι R))
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨h k l hkl s n, fun hn ↦ ?_⟩
  have e : n = x k l hkl (-s) * (x k l hkl s * n * (x k l hkl s)⁻¹) * (x k l hkl (-s))⁻¹ := by
    rw [x_neg]
    group
  rw [e]
  exact h k l hkl (-s) _ hn

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_normal_of_roots

/-- **`H(J)` is normal** in `St(ι, R)` when any two indices miss a third one. -/
theorem k2KarNorm_H_normal (h3 : ∀ i j : ι, ∃ m : ι, m ≠ i ∧ m ≠ j) :
    (k2KarNorm_H ι J).Normal := by
  refine k2KarNorm_normal_of_roots fun k l hkl s n hn ↦ ?_
  change n ∈ Subgroup.closure (k2KarNorm_gens ι J) at hn
  induction hn using Subgroup.closure_induction with
  | mem n hn =>
      obtain ⟨i, j, hij, a, ha, r, rfl⟩ := hn
      exact k2KarNorm_conj_z h3 k l hkl s i j hij ha r
  | one =>
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
  | mul u v _ _ hu hv =>
      rw [k2KarNorm_conj_mul]
      exact mul_mem hu hv
  | inv u _ hu =>
      rw [k2KarNorm_conj_inv]
      exact inv_mem hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_H_normal

end KarNormHard

end GroupApproximation.BooneHigman.Metabelian.ElemFP
