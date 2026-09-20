import GroupApproximation.BooneHigmanLinear.RelGen.SteinNormal
import GroupApproximation.Meta.AxiomGuard

/-!
# Stein's theorem, part 4: root groups and their normalizers

Lane bh-pal-wire, k2-poly H.L3 (towards the `U⁺ H̄ U⁻` form of L–S Theorem 4.8). Throughout,
`J` is an ideal and `rootGroup I J P = ⟨x_ij(s) : P i j, s ∈ J⟩` (`RelGen.Defs`).

* `x_mem_rootGroup`, `rootGroup_mono`.
* `conj_mem_rootGroup_of_forall`: a subgroup conjugates `rootGroup I J P` into itself if its
  generators do.
* `hBar_conj_rootGroup`: `H̄(R, J)` normalizes every `rootGroup I J P`, since it acts on each root
  by a scalar.
* `conj_x_rootGroup`: `x_kl(η)` normalizes `rootGroup I J P` when `(l, k) ∉ P`, and `P` is closed
  under the two commutator moves `(l, j) ↦ (k, j)` and `(i, k) ↦ (i, l)`.
* `commute_col`: the column roots `x_iL`, `x_i'L` commute.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup

variable {I : Type*} [Fintype I] [DecidableEq I] {R : Type*} [CommRing R] {J : Ideal R}

theorem x_mem_rootGroup {P : I → I → Prop} {i j : I} (hij : i ≠ j) (hP : P i j) {s : R}
    (hs : s ∈ J) : x i j hij s ∈ rootGroup I J P :=
  Subgroup.subset_closure ⟨i, j, hij, s, hP, hs, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.x_mem_rootGroup

theorem rootGroup_mono {P Q : I → I → Prop} (hPQ : ∀ i j, P i j → Q i j) :
    rootGroup I J P ≤ rootGroup I J Q := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨i, j, hij, s, hP, hs, rfl⟩
  exact ⟨i, j, hij, s, hPQ i j hP, hs, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.rootGroup_mono

theorem rootGroup_le_xGroup (P : I → I → Prop) : rootGroup I J P ≤ xGroup I J := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨i, j, hij, s, -, hs, rfl⟩
  exact ⟨i, j, hij, s, hs, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.rootGroup_le_xGroup

/-- If `g` conjugates each generator of `rootGroup I J P` into it, it normalizes it. -/
theorem conj_mem_rootGroup_of_forall {P : I → I → Prop} {g : SteinbergGroup I R}
    (hgen : ∀ (i j : I) (hij : i ≠ j) (s : R), P i j → s ∈ J →
      g * x i j hij s * g⁻¹ ∈ rootGroup I J P)
    {y : SteinbergGroup I R} (hy : y ∈ rootGroup I J P) : g * y * g⁻¹ ∈ rootGroup I J P := by
  rw [rootGroup] at hy
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, j, hij, s, hP, hs, rfl⟩ := hy
    exact hgen i j hij s hP hs
  | one => simp only [mul_one, mul_inv_cancel, Subgroup.one_mem]
  | mul y₁ y₂ _ _ h₁ h₂ =>
    rw [show g * (y₁ * y₂) * g⁻¹ = (g * y₁ * g⁻¹) * (g * y₂ * g⁻¹) by group]
    exact Subgroup.mul_mem _ h₁ h₂
  | inv y _ h =>
    rw [show g * y⁻¹ * g⁻¹ = (g * y * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ h

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_mem_rootGroup_of_forall

/-- A set closed under inverses whose elements conjugate `H` into itself generates a subgroup
contained in the normalizer of `H`. -/
theorem closure_le_normalizer {G : Type*} [Group G] {H : Subgroup G} {S : Set G}
    (hS : ∀ g ∈ S, ∀ y ∈ H, g * y * g⁻¹ ∈ H) (hSinv : ∀ g ∈ S, g⁻¹ ∈ S) :
    Subgroup.closure S ≤ H.normalizer := by
  refine (Subgroup.closure_le _).mpr fun g hg => Subgroup.mem_normalizer_iff.mpr fun y => ?_
  refine ⟨hS g hg y, fun hy => ?_⟩
  have e := hS g⁻¹ (hSinv g hg) _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at e

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.closure_le_normalizer

theorem conj_mem_of_mem_normalizer {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ H.normalizer) {y : G} (hy : y ∈ H) : g * y * g⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.mp hg y).mp hy

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_mem_of_mem_normalizer

variable (third : ThirdIndex I)
include third

/-- `H̄(R, J)` normalizes every root group over `J`. -/
theorem hBar_conj_rootGroup {P : I → I → Prop} {g : SteinbergGroup I R} (hg : g ∈ hBar I J)
    {y : SteinbergGroup I R} (hy : y ∈ rootGroup I J P) : g * y * g⁻¹ ∈ rootGroup I J P := by
  refine conj_mem_rootGroup_of_forall (fun i j hij s hP hs => ?_) hy
  obtain ⟨c, hc⟩ := hBar_conj_x third hij hg
  rw [hc]
  exact x_mem_rootGroup hij hP (J.mul_mem_left _ hs)

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.hBar_conj_rootGroup

omit third in
/-- `x_kl(η)` normalizes `rootGroup I J P` when `(l, k) ∉ P` and `P` is closed under the
commutator moves `(l, j) ↦ (k, j)` (`k ≠ j`) and `(i, k) ↦ (i, l)` (`i ≠ l`). -/
theorem conj_x_rootGroup {P : I → I → Prop} {k l : I} (hkl : k ≠ l) (η : R)
    (hopp : ¬P l k) (h1 : ∀ j, P l j → k ≠ j → P k j) (h2 : ∀ i, P i k → i ≠ l → P i l)
    {y : SteinbergGroup I R} (hy : y ∈ rootGroup I J P) :
    x k l hkl η * y * (x k l hkl η)⁻¹ ∈ rootGroup I J P := by
  refine conj_mem_rootGroup_of_forall (fun c d hcd s hP hs => ?_) hy
  by_cases hc : l = c
  · subst hc
    have hkd : k ≠ d := fun e => hopp (e ▸ hP)
    rw [conj_eq_commutator_mul, x_commutator k l d hkl hcd hkd]
    exact Subgroup.mul_mem _ (x_mem_rootGroup hkd (h1 d hP hkd) (J.mul_mem_left η hs))
      (x_mem_rootGroup hcd hP hs)
  · by_cases hd : d = k
    · subst hd
      have hcl : c ≠ l := fun e => hc e.symm
      rw [conj_eq_commutator_mul, ← commutatorElement_inv, x_commutator c k l hcd hkl hcl,
        ← x_neg]
      exact Subgroup.mul_mem _
        (x_mem_rootGroup hcl (h2 c hP hcl) (neg_mem (J.mul_mem_right η hs)))
        (x_mem_rootGroup hcd hP hs)
    · rw [(x_commute_of_ne k l c d hkl hcd hc hd η s).eq, mul_inv_cancel_right]
      exact x_mem_rootGroup hcd hP hs

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_x_rootGroup

omit third in
/-- Column roots `x_iL`, `x_i'L` commute. -/
theorem commute_col {i i' L : I} (hiL : i ≠ L) (hi'L : i' ≠ L) (a b : R) :
    Commute (x i L hiL a) (x i' L hi'L b) :=
  x_commute_of_ne i L i' L hiL hi'L hi'L.symm hiL.symm a b

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commute_col

omit third in
/-- Row roots `x_Lj`, `x_Lj'` commute. -/
theorem commute_row {j j' L : I} (hLj : L ≠ j) (hLj' : L ≠ j') (a b : R) :
    Commute (x L j hLj a) (x L j' hLj' b) :=
  x_commute_of_ne L j L j' hLj hLj' hLj.symm hLj'.symm a b

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.commute_row

end GroupApproximation.BooneHigmanLinear.RelGen
