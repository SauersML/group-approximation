import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarIndPair
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarRelStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# `k2KarRel_PairStatement` is proved outright

Lane `bh-met-93e`, statement module.  Notation: `L = A_s`, `P = k2DilateSt_pullback s ⊆ A × L[X]`.

* `k2KarInd_snd_injective`: for a domain `A` and `s ≠ 0`, `snd : P → L[X]` is injective.  If
  `snd b = 0` then `λ (fst b) = (snd b)(0) = 0`, and `λ : A → L` is injective.  Hence `P` has no
  zero divisors (`k2KarInd_mul_eq_zero`) and `1 ≠ 0` in `P` (`k2KarInd_one_ne_zero`).
* `k2KarInd_padMat_eq_one`: if `St(snd) y = 1` then `padMat y = 1` over `P` (entrywise, by
  injectivity of `snd` and naturality of `padMat`).
* **`k2KarInd_boundedAt_two`**: `k2KarRel_BoundedAt s 2` for every domain `A`, `s ≠ 0`.  For
  `y = g x_ij(b) g⁻¹ · g₂ x_kl(c) g₂⁻¹`, conjugate by `g₂` and apply `k2KarInd_stab_pair` over `P`.
* **`k2KarInd_pairStatement : k2KarRel_PairStatement`**, with no hypotheses.
* `k2KarInd_step_iff`: the inductive-step family
  `∀ m, BoundedAt s m → BoundedAt s (m + 1)` is **EQUIVALENT to `R1 = k2Karoubi_InjAt s`**.

## LOUD: status

* `k2KarRel_PairStatement` (the isolated statement of lane `bh-met-92u`) is now **PROVED**.
* The pair proof **never uses `fst b = 0`**: two conjugates of root elements over a domain
  whose product has trivial matrix die after one stabilization.  So all of the difficulty of
  `R1` is in products of at least three relative conjugates.
* The inductive step `BoundedAt s m → BoundedAt s (m + 1)`, taken for all `m`, is not weaker
  than `R1`: `k2KarInd_step_iff` proves it equivalent.  It is therefore not claimed here.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral

section KarIndStatement

variable {A : Type*} [CommRing A] [IsDomain A] {s : A}

theorem k2KarInd_algebraMap_injective (hs : s ≠ 0) :
    Function.Injective (algebraMap A (Localization.Away s)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_algebraMap_injective

theorem k2KarInd_isDomain (hs : s ≠ 0) : IsDomain (Localization.Away s) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hs)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_isDomain

/-- `snd : P → L[X]` is injective. -/
theorem k2KarInd_snd_injective (hs : s ≠ 0) : Function.Injective (k2PullRel_snd s) := by
  rw [injective_iff_map_eq_zero]
  intro b hb
  have h0 : algebraMap A (Localization.Away s) (k2PullRel_fst s b) = 0 := by
    rw [← k2PullRel_eval_snd, hb, Polynomial.eval_zero]
  refine k2PullRel_ext ?_ (by rw [hb, map_zero])
  rw [map_zero]
  exact (injective_iff_map_eq_zero _).mp (k2KarInd_algebraMap_injective hs) _ h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_snd_injective

theorem k2KarInd_mul_eq_zero (hs : s ≠ 0) (a b : k2DilateSt_pullback s) (h : a * b = 0) :
    a = 0 ∨ b = 0 := by
  haveI := k2KarInd_isDomain hs
  have e : k2PullRel_snd s a * k2PullRel_snd s b = 0 := by
    rw [← map_mul (k2PullRel_snd s), h, map_zero]
  have hi := (injective_iff_map_eq_zero _).mp (k2KarInd_snd_injective hs)
  rcases mul_eq_zero.mp e with e | e
  · exact Or.inl (hi a e)
  · exact Or.inr (hi b e)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_mul_eq_zero

theorem k2KarInd_one_ne_zero (hs : s ≠ 0) : (1 : k2DilateSt_pullback s) ≠ 0 := by
  haveI := k2KarInd_isDomain hs
  intro h
  have e : k2PullRel_snd s 1 = k2PullRel_snd s 0 := by rw [h]
  rw [map_one, map_zero] at e
  exact one_ne_zero e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_one_ne_zero

/-- Over `P`, trivial `snd`-image forces trivial elementary matrix. -/
theorem k2KarInd_padMat_eq_one (hs : s ≠ 0) {n : ℕ} {y : St n (k2DilateSt_pullback s)}
    (hy : ringMap (k2PullRel_snd s) y = 1) : padMat y = 1 := by
  refine Matrix.ext fun p q ↦ k2KarInd_snd_injective hs ?_
  rw [← k2KarInd_padMat_ringMap (k2PullRel_snd s) y p q, hy,
    map_one (padMat (R := Polynomial (Localization.Away s)) (n := n))]
  by_cases hpq : p = q
  · rw [hpq, Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hpq, Matrix.one_apply_ne hpq, map_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_padMat_eq_one

/-- **`R1` for products of two relative conjugates**, over any domain, `s ≠ 0`. -/
theorem k2KarInd_boundedAt_two (hs : s ≠ 0) : k2KarRel_BoundedAt s 2 := by
  intro M l hlen hl hsnd
  rcases l with _ | ⟨z, _ | ⟨w, _ | ⟨u, l⟩⟩⟩
  · exact k2KarRel_boundedAt_one s M [] (by simp) hl hsnd
  · exact k2KarRel_boundedAt_one s M [z] (by simp) hl hsnd
  · obtain ⟨g, i, j, hij, b, _, rfl⟩ := hl z (by simp)
    obtain ⟨g₂, i₂, j₂, hij₂, c, _, rfl⟩ := hl w (by simp)
    rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one] at hsnd ⊢
    have e : g * x i j hij b * g⁻¹ * (g₂ * x i₂ j₂ hij₂ c * g₂⁻¹) =
        g₂ * (g₂⁻¹ * g * x i j hij b * (g₂⁻¹ * g)⁻¹ * x i₂ j₂ hij₂ c) * g₂⁻¹ := by
      group
    rw [e] at hsnd ⊢
    rw [map_mul, map_mul, map_inv, conj_eq_one_iff] at hsnd
    exact cubeDiagDilate_stDies_conj g₂ (k2KarInd_stDies_of_stab
      (k2KarInd_stab_pair (k2KarInd_mul_eq_zero hs) (k2KarInd_one_ne_zero hs) (g₂⁻¹ * g)
        i j hij b i₂ j₂ hij₂ c (k2KarInd_padMat_eq_one hs hsnd)))
  · rw [List.length_cons, List.length_cons, List.length_cons] at hlen
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_boundedAt_two

end KarIndStatement

section KarIndEndpoint

/-- **`k2KarRel_PairStatement` holds.** -/
theorem k2KarInd_pairStatement : k2KarRel_PairStatement :=
  fun _ hp _ _ _ h0 _ ↦ by
    haveI := Fact.mk hp
    exact k2KarInd_boundedAt_two (Polynomial.C_ne_zero.2 h0)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_pairStatement

/-- **LOUD**: the inductive-step family is equivalent to `R1` (`BoundedAt s 1` is proved). -/
theorem k2KarInd_step_iff {A : Type*} [CommRing A] (s : A) :
    (∀ m, k2KarRel_BoundedAt s m → k2KarRel_BoundedAt s (m + 1)) ↔ k2Karoubi_InjAt s := by
  refine ⟨fun h ↦ k2KarRel_injAt_of_boundedAt fun m ↦ ?_,
    fun h m _ ↦ k2KarRel_boundedAt_of_injAt h (m + 1)⟩
  induction m with
  | zero => exact k2KarRel_boundedAt_mono (Nat.zero_le 1) (k2KarRel_boundedAt_one s)
  | succ m ih => exact h m ih

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarInd_step_iff

end KarIndEndpoint

end GroupApproximation.BooneHigman.Metabelian.ElemFP
