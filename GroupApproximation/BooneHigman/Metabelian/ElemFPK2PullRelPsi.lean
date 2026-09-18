import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PullRelU
import GroupApproximation.Meta.AxiomGuard

/-!
# The homomorphism `Ψ : St(M, L[X]) → H ⋊ St(M, L)`

Lane `bh-met-91g`, `Ψ` module.  Fix `q : k2PullRel_ker s M →* H` and an action
`α : St(M, L) →* MulAut H` satisfying `k2PullRel_F1`, `k2PullRel_F2` and `k2PullRel_F3`.

* `k2PullRel_elt q α i j hij h = (u_ij(h), x_ij(h(0)))`, an element of `H ⋊[α] St(M, L)`.
* `k2PullRel_elt_add`, `k2PullRel_elt_comm`, `k2PullRel_elt_adj`: these elements satisfy the
  three Steinberg relations.  In the first component this is `k2PullRel_u_add`, `_u_comm` and
  `_u_adj`, after `F1`, `F2`, `F3` evaluate the twisting.  In the second it is the relation in
  `St(M, L)`.
* `k2PullRel_psi`: the resulting homomorphism, with `Ψ(x_ij(h)) = k2PullRel_elt … h`
  (`k2PullRel_psi_x`) and `Ψ(C(d)) = inr d` (`k2PullRel_psi_C`), since `u_ij(C t) = 1`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open scoped commutatorElement

section PullRelPsi

variable {A : Type*} [CommRing A] {s : A} {M : ℕ} {H : Type*} [Group H]
  (q : k2PullRel_ker s M →* H) (α : SteinbergGroup (Fin M) (Localization.Away s) →* MulAut H)

/-- `u_ij(C t) = 1`, because `lift (C t) = 0`. -/
theorem k2PullRel_u_C (i j : Fin M) (hij : i ≠ j) (t : Localization.Away s) :
    k2PullRel_u q i j hij (Polynomial.C t) = 1 := by
  unfold k2PullRel_u
  have h1 : (⟨x i j hij (k2PullRel_lift s (Polynomial.C t)), k2PullRel_x_lift_mem i j hij _⟩ :
      k2PullRel_ker s M) = 1 := by
    refine Subtype.ext ?_
    change x i j hij (k2PullRel_lift s (Polynomial.C t)) = 1
    rw [k2PullRel_lift_C, x_zero]
  rw [h1, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_u_C

/-- The image `(u_ij(h), x_ij(h(0)))` of `x_ij(h)`. -/
noncomputable def k2PullRel_elt (i j : Fin M) (hij : i ≠ j)
    (h : Polynomial (Localization.Away s)) :
    H ⋊[α] SteinbergGroup (Fin M) (Localization.Away s) :=
  ⟨k2PullRel_u q i j hij h, x i j hij (h.eval 0)⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_elt

theorem k2PullRel_elt_left (i j : Fin M) (hij : i ≠ j) (h : Polynomial (Localization.Away s)) :
    (k2PullRel_elt q α i j hij h).left = k2PullRel_u q i j hij h :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_elt_left

theorem k2PullRel_elt_right (i j : Fin M) (hij : i ≠ j) (h : Polynomial (Localization.Away s)) :
    (k2PullRel_elt q α i j hij h).right = x i j hij (h.eval 0) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_elt_right

theorem k2PullRel_elt_add (hF1 : k2PullRel_F1 q α) (i j : Fin M) (hij : i ≠ j)
    (a b : Polynomial (Localization.Away s)) :
    k2PullRel_elt q α i j hij a * k2PullRel_elt q α i j hij b =
      k2PullRel_elt q α i j hij (a + b) := by
  refine SemidirectProduct.ext ?_ ?_
  · simp only [SemidirectProduct.mul_left, k2PullRel_elt_left, k2PullRel_elt_right]
    rw [hF1 i j i j hij hij hij.symm hij.symm]
    exact k2PullRel_u_add q i j hij a b
  · simp only [SemidirectProduct.mul_right, k2PullRel_elt_right]
    rw [x_mul, Polynomial.eval_add]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_elt_add

theorem k2PullRel_elt_comm (hF1 : k2PullRel_F1 q α) (i j k l : Fin M) (hij : i ≠ j)
    (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i) (a b : Polynomial (Localization.Away s)) :
    k2PullRel_elt q α i j hij a * k2PullRel_elt q α k l hkl b =
      k2PullRel_elt q α k l hkl b * k2PullRel_elt q α i j hij a := by
  refine SemidirectProduct.ext ?_ ?_
  · simp only [SemidirectProduct.mul_left, k2PullRel_elt_left, k2PullRel_elt_right]
    rw [hF1 k l i j hkl hij hli hjk, hF1 i j k l hij hkl hjk hli]
    exact k2PullRel_u_comm q i j k l hij hkl hjk hli a b
  · simp only [SemidirectProduct.mul_right, k2PullRel_elt_right]
    exact (x_commute_of_ne i j k l hij hkl hjk hli _ _).eq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_elt_comm

theorem k2PullRel_elt_adj (hF1 : k2PullRel_F1 q α) (hF2 : k2PullRel_F2 q α)
    (hF3 : k2PullRel_F3 q α) (i j k : Fin M) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : Polynomial (Localization.Away s)) :
    k2PullRel_elt q α i j hij a * k2PullRel_elt q α j k hjk b =
      k2PullRel_elt q α i k hik (a * b) * k2PullRel_elt q α j k hjk b *
        k2PullRel_elt q α i j hij a := by
  refine SemidirectProduct.ext ?_ ?_
  · simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, k2PullRel_elt_left,
      k2PullRel_elt_right, map_mul, MulAut.mul_apply]
    rw [hF2 i j k hij hjk hik, hF3 i j k hij hjk hik,
      map_mul (α (x i k hik ((a * b).eval 0))), hF1 j k i k hjk hik hik.symm hjk.symm,
      hF1 i j i k hij hik hij.symm hik.symm, hF1 i k i k hik hik hik.symm hik.symm]
    exact k2PullRel_u_adj q i j k hij hjk hik a b
  · simp only [SemidirectProduct.mul_right, k2PullRel_elt_right]
    rw [Polynomial.eval_mul]
    exact (k2PullRel_comm_iff _ _ _).mp (x_commutator i j k hij hjk hik _ _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_elt_adj

/-- The image of a Steinberg generator. -/
noncomputable def k2PullRel_gen
    (g : SteinbergGenerator (Fin M) (Polynomial (Localization.Away s))) :
    H ⋊[α] SteinbergGroup (Fin M) (Localization.Away s) :=
  k2PullRel_elt q α g.row g.column g.row_ne_column g.coefficient

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_gen

theorem k2PullRel_gen_relation (hF1 : k2PullRel_F1 q α) (hF2 : k2PullRel_F2 q α)
    (hF3 : k2PullRel_F3 q α)
    (w : FreeGroup (SteinbergGenerator (Fin M) (Polynomial (Localization.Away s))))
    (hw : w ∈ SteinbergGroup.relations (I := Fin M) (R := Polynomial (Localization.Away s))) :
    FreeGroup.lift (k2PullRel_gen q α) w = 1 := by
  change SteinbergGroup.IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      change k2PullRel_elt q α i j hij a * k2PullRel_elt q α i j hij b *
        (k2PullRel_elt q α i j hij (a + b))⁻¹ = 1
      rw [mul_inv_eq_one]
      exact k2PullRel_elt_add q α hF1 i j hij a b
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅k2PullRel_elt q α i j hij a, k2PullRel_elt q α k l hkl b⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact k2PullRel_elt_comm q α hF1 i j k l hij hkl hjk hli a b
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      change ⁅k2PullRel_elt q α i j hij a, k2PullRel_elt q α j k hjk b⁆ *
        (k2PullRel_elt q α i k hik (a * b))⁻¹ = 1
      rw [mul_inv_eq_one, k2PullRel_comm_iff]
      exact k2PullRel_elt_adj q α hF1 hF2 hF3 i j k hij hjk hik a b

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_gen_relation

/-- `Ψ : St(M, L[X]) →* H ⋊[α] St(M, L)`, `x_ij(h) ↦ (u_ij(h), x_ij(h(0)))`. -/
noncomputable def k2PullRel_psi (hF1 : k2PullRel_F1 q α) (hF2 : k2PullRel_F2 q α)
    (hF3 : k2PullRel_F3 q α) :
    SteinbergGroup (Fin M) (Polynomial (Localization.Away s)) →*
      H ⋊[α] SteinbergGroup (Fin M) (Localization.Away s) :=
  PresentedGroup.toGroup (f := k2PullRel_gen q α) (k2PullRel_gen_relation q α hF1 hF2 hF3)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_psi

theorem k2PullRel_psi_x (hF1 : k2PullRel_F1 q α) (hF2 : k2PullRel_F2 q α)
    (hF3 : k2PullRel_F3 q α) (i j : Fin M) (hij : i ≠ j)
    (h : Polynomial (Localization.Away s)) :
    k2PullRel_psi q α hF1 hF2 hF3 (x i j hij h) = k2PullRel_elt q α i j hij h := by
  exact PresentedGroup.toGroup.of _

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_psi_x

/-- `Ψ(C(d)) = inr d` for `d ∈ St(M, L)`. -/
theorem k2PullRel_psi_C (hF1 : k2PullRel_F1 q α) (hF2 : k2PullRel_F2 q α)
    (hF3 : k2PullRel_F3 q α) (d : SteinbergGroup (Fin M) (Localization.Away s)) :
    k2PullRel_psi q α hF1 hF2 hF3 (ringMap Polynomial.C d) = SemidirectProduct.inr d := by
  have hh : (k2PullRel_psi q α hF1 hF2 hF3).comp (ringMap (I := Fin M) Polynomial.C) =
      SemidirectProduct.inr := by
    refine PresentedGroup.ext ?_
    rintro ⟨i, j, hij, t⟩
    change k2PullRel_psi q α hF1 hF2 hF3 (ringMap Polynomial.C (x i j hij t)) =
      SemidirectProduct.inr (x i j hij t)
    rw [ringMap_x, k2PullRel_psi_x]
    refine SemidirectProduct.ext ?_ ?_
    · rw [k2PullRel_elt_left, SemidirectProduct.left_inr, k2PullRel_u_C]
    · rw [k2PullRel_elt_right, SemidirectProduct.right_inr, Polynomial.eval_C]
  exact DFunLike.congr_fun hh d

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PullRel_psi_C

end PullRelPsi

end GroupApproximation.BooneHigman.Metabelian.ElemFP
