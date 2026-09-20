import GroupApproximation.BooneHigmanLinear.RelGen.ZTools
import GroupApproximation.Meta.AxiomGuard

/-!
# L–S Lemma 4.7: `K(A[X], M[X]) = St̄(A[X], X·M[X]) · [St(X·A[X]), St̄(A, M)]` (k2-poly H.L3)

Lane k2-hl3b. A. Lavrenov and S. Sinchuk, arXiv:1909.02637, §4.2, Lemma 4.7, in type A over an
index type `I`. Here `St̄(A, M)` sits in `St_I(A[X])` through the constants `C`, and
`St(Φ, X·A[X])` is `xGroup I (X)`. The proof is L–S's, from Stein–Tits–Vaserstein
(`Thm42Statement`, taken as a hypothesis so that this file does not wait for its build):

* `H := St̄(A[X], X·M[X]) ⊔ ⁅St(X·A[X]), C(St̄(A, M))⁆` is normalized by `C(St̄(A, M))`, since the
  first term is normal and `k ⁅g, h⁆ k⁻¹ = ⁅g, k⁆⁻¹ ⁅g, k h⁆`.
* So `P := {g ∈ St̄(A[X], M[X]) | g · C(g(0))⁻¹ ∈ H}` is a subgroup (`lemma47Aux`).
* It contains every `z_ij(f, ξ)`, `f ∈ M[X]`: write `c = C(f(0))`, `ξ₀ = C(ξ(0))`, `y = x_ji(ξ - ξ₀)`
  and `w = z_ij(c, ξ₀) = C(z_ij(f(0), ξ(0)))`. Then `z_ij(f, ξ) = y⁻¹ w y · z_ij(f - c, ξ)`, and
  `z_ij(f, ξ) · w⁻¹ = ⁅y⁻¹, w⁆ · (w · z_ij(f - c, ξ) · w⁻¹)`, with `f - c ∈ X·M[X]`.
* By Theorem 4.2, `St̄(A[X], M[X]) ≤ P`; on `K` we have `g(0) = 1`, so `g ∈ H`.

The reverse inclusion needs no hypothesis: evaluation at `0` kills `X·A[X]`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open scoped commutatorElement
open GroupApproximation.SteinbergGroup

/-- **L–S Lemma 4.7.** `K(A[X], M[X]) = St̄(A[X], X·M[X]) · [St(Φ, X·A[X]), St̄(A, M)]`, with
`St̄(A, M)` in `St_I(A[X])` through the constants. -/
def Lemma47Statement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I], ThirdIndex I →
    ∀ (A : Type) [CommRing A] (M : Ideal A),
      polyKer I M = relKer I (xPolyIdeal M) ⊔
        ⁅xGroup I (Ideal.span {(Polynomial.X : Polynomial A)}),
          (relKer I M).map (ringMap (Polynomial.C : A →+* Polynomial A))⁆

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.Lemma47Statement

section Aux

variable (I : Type*) [Fintype I] [DecidableEq I] {A : Type*} [CommRing A] (M : Ideal A)

/-- `St̄(A, M)` inside `St_I(A[X])`, through the constants. -/
abbrev constRelKer : Subgroup (SteinbergGroup I (Polynomial A)) :=
  (relKer I M).map (ringMap (Polynomial.C : A →+* Polynomial A))

/-- The right-hand side of L–S Lemma 4.7. -/
abbrev lemma47Sub : Subgroup (SteinbergGroup I (Polynomial A)) :=
  relKer I (xPolyIdeal M) ⊔
    ⁅xGroup I (Ideal.span {(Polynomial.X : Polynomial A)}), constRelKer I M⁆

/-- The subgroup `{g ∈ St̄(A[X], M[X]) | g · C(g(0))⁻¹ ∈ H}`, for `H` normalized by
`C(St̄(A, M))`. -/
def lemma47Aux (H : Subgroup (SteinbergGroup I (Polynomial A)))
    (hH : ∀ k ∈ constRelKer I M, ∀ y ∈ H, k * y * k⁻¹ ∈ H) :
    Subgroup (SteinbergGroup I (Polynomial A)) where
  carrier := {g | g ∈ relKer I (polyIdeal M) ∧
    g * (ringMap (Polynomial.C : A →+* Polynomial A)
      (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) g))⁻¹ ∈ H}
  one_mem' := And.intro (relKer I (polyIdeal M)).one_mem (by simpa using H.one_mem)
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine And.intro ((relKer I (polyIdeal M)).mul_mem ha hb) ?_
    have hka : ringMap (Polynomial.C : A →+* Polynomial A)
        (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) a) ∈ constRelKer I M :=
      Subgroup.mem_map_of_mem _
        (ringMap_mem_relKer (Polynomial.evalRingHom 0 : Polynomial A →+* A)
          (polyIdeal_le_comap_evalZero M) ha)
    have e : ∀ u v cu cv : SteinbergGroup I (Polynomial A),
        u * v * (cu * cv)⁻¹ = u * cu⁻¹ * (cu * (v * cv⁻¹) * cu⁻¹) := fun _ _ _ _ => by group
    rw [map_mul, map_mul, e]
    exact H.mul_mem ha' (hH _ hka _ hb')
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine And.intro ((relKer I (polyIdeal M)).inv_mem ha) ?_
    have hka : (ringMap (Polynomial.C : A →+* Polynomial A)
        (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) a))⁻¹ ∈ constRelKer I M :=
      Subgroup.inv_mem _ (Subgroup.mem_map_of_mem _
        (ringMap_mem_relKer (Polynomial.evalRingHom 0 : Polynomial A →+* A)
          (polyIdeal_le_comap_evalZero M) ha))
    have e : ∀ u cu : SteinbergGroup I (Polynomial A),
        u⁻¹ * (cu⁻¹)⁻¹ = cu⁻¹ * (u * cu⁻¹)⁻¹ * (cu⁻¹)⁻¹ := fun _ _ => by group
    rw [map_inv, map_inv, e]
    exact hH _ hka _ (H.inv_mem ha')

theorem mem_lemma47Aux {H : Subgroup (SteinbergGroup I (Polynomial A))}
    {hH : ∀ k ∈ constRelKer I M, ∀ y ∈ H, k * y * k⁻¹ ∈ H} {g : SteinbergGroup I (Polynomial A)} :
    g ∈ lemma47Aux I M H hH ↔ g ∈ relKer I (polyIdeal M) ∧
      g * (ringMap (Polynomial.C : A →+* Polynomial A)
        (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) g))⁻¹ ∈ H :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.mem_lemma47Aux

variable {I}

/-- `lemma47Sub` is normalized by `C(St̄(A, M))`. -/
theorem conj_mem_lemma47Sub {k : SteinbergGroup I (Polynomial A)} (hk : k ∈ constRelKer I M)
    {y : SteinbergGroup I (Polynomial A)} (hy : y ∈ lemma47Sub I M) :
    k * y * k⁻¹ ∈ lemma47Sub I M :=
  conj_mem_sup_of_normal (K2Found.relSt_normal I _)
    (fun _ hc => conj_mem_commutator_of_mem_right hk hc) hy

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.conj_mem_lemma47Sub

/-- The generators `z_ij(f, ξ)`, `f ∈ M[X]`, lie in `lemma47Aux` for `H = lemma47Sub`. -/
theorem zElt_mem_lemma47Aux {i j : I} (hij : i ≠ j) {f : Polynomial A} (hf : f ∈ polyIdeal M)
    (ξ : Polynomial A) :
    zElt i j hij f ξ ∈
      lemma47Aux I M (lemma47Sub I M) (fun _ hk _ hy => conj_mem_lemma47Sub M hk hy) := by
  refine (mem_lemma47Aux I M).mpr ⟨zElt_mem_relKer hij hf ξ, ?_⟩
  rw [ringMap_zElt, ringMap_zElt]
  have hf0 : (Polynomial.evalRingHom 0 : Polynomial A →+* A) f ∈ M :=
    polyIdeal_le_comap_evalZero M hf
  -- `y = x_ji(ξ - ξ₀)`, `w = z_ij(c, ξ₀)`, `n = z_ij(f - c, ξ)`.
  have hy : x j i hij.symm (ξ - Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) ξ))
      ∈ xGroup I (Ideal.span {(Polynomial.X : Polynomial A)}) :=
    Subgroup.subset_closure ⟨j, i, hij.symm, _, sub_C_evalZero_mem_span_X ξ, rfl⟩
  have hw : zElt i j hij (Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) f))
      (Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) ξ)) ∈ constRelKer I M :=
    ⟨zElt i j hij _ _, zElt_mem_relKer hij hf0 _, ringMap_zElt _ i j hij _ _⟩
  have hn : zElt i j hij (f - Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) f)) ξ
      ∈ relKer I (xPolyIdeal M) :=
    zElt_mem_relKer hij (sub_C_evalZero_mem_xPolyIdeal hf) ξ
  have e1 : zElt i j hij f ξ =
      zElt i j hij (Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) f)) ξ *
        zElt i j hij (f - Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) f)) ξ := by
    rw [← zElt_add]
    congr 1
    ring
  have e2 : (x j i hij.symm
        (ξ - Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) ξ)))⁻¹ *
      zElt i j hij (Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) f))
        (Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) ξ)) *
      x j i hij.symm (ξ - Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) ξ)) =
      zElt i j hij (Polynomial.C ((Polynomial.evalRingHom 0 : Polynomial A →+* A) f)) ξ := by
    rw [x_inv_mul_zElt_mul_x]
    congr 1
    ring
  have key : ∀ y w n : SteinbergGroup I (Polynomial A),
      y⁻¹ * w * y * n * w⁻¹ = ⁅y⁻¹, w⁆ * (w * n * w⁻¹) := fun _ _ _ => by
    simp only [commutatorElement_def]
    group
  rw [e1, ← e2, key]
  exact (lemma47Sub I M).mul_mem
    ((le_sup_right : _ ≤ lemma47Sub I M) (Subgroup.commutator_mem_commutator
      (Subgroup.inv_mem _ hy) hw))
    ((le_sup_left : _ ≤ lemma47Sub I M) ((K2Found.relSt_normal I _).conj_mem _ hn _))

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.zElt_mem_lemma47Aux

/-- The easy inclusion: `St̄(A[X], X·M[X]) · [St(X·A[X]), C(St̄(A, M))] ≤ K(A[X], M[X])`. -/
theorem lemma47Sub_le_polyKer : lemma47Sub I M ≤ polyKer I M := by
  refine sup_le (fun g hg => Subgroup.mem_inf.mpr ⟨relKer_mono Ideal.mul_le_left hg,
    relKer_xPolyIdeal_le_ker M hg⟩) ?_
  rw [Subgroup.commutator_le]
  rintro g hg _ ⟨h, hh, rfl⟩
  have hC : ringMap (Polynomial.C : A →+* Polynomial A) h ∈ relKer I (polyIdeal M) :=
    ringMap_mem_relKer (Polynomial.C : A →+* Polynomial A) (J' := polyIdeal M)
      Ideal.le_comap_map hh
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [commutatorElement_def]
    exact (relKer I (polyIdeal M)).mul_mem
      ((K2Found.relSt_normal I _).conj_mem _ hC g) ((relKer I (polyIdeal M)).inv_mem hC)
  · rw [MonoidHom.mem_ker, map_commutatorElement, MonoidHom.mem_ker.mp (xGroup_span_X_le_ker hg),
      commutatorElement_one_left]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.lemma47Sub_le_polyKer

end Aux

/-- **L–S Lemma 4.7** from Stein–Tits–Vaserstein. -/
theorem lemma47_of_thm42 (h42 : Thm42Statement) : Lemma47Statement := by
  intro I _ _ third A _ M
  show polyKer I M = lemma47Sub I M
  refine le_antisymm (fun g hg => ?_) (lemma47Sub_le_polyKer M)
  obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
  have hP : relKer I (polyIdeal M) ≤
      lemma47Aux I M (lemma47Sub I M) (fun _ hk _ hy => conj_mem_lemma47Sub M hk hy) := by
    rw [h42 I third (Polynomial A) (polyIdeal M), Subgroup.closure_le]
    rintro _ ⟨i, j, hij, f, ξ, -, hf, rfl⟩
    exact zElt_mem_lemma47Aux M hij hf ξ
  have h := ((mem_lemma47Aux I M).mp (hP hg1)).2
  rwa [MonoidHom.mem_ker.mp hg2, map_one, inv_one, mul_one] at h

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.lemma47_of_thm42

end GroupApproximation.BooneHigmanLinear.RelGen
