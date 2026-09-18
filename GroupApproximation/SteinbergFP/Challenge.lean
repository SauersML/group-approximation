import GroupApproximation.SteinbergFP.Embedding
import Mathlib.Algebra.RingQuot
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# Kourovka 14.10(c) in the form of the Palomar challenge

`Palomar/BooneHigmanChallenge.lean` states Kourovka Problem 14.10(c) (Problem 2.7 of
Belk–Bleak–Matucci–Zaremsky) with its own vocabulary: the ring `R_L` is a `RingQuot` of the free
algebra `ℤ⟨Fin 6⟩` by the nine defining relations, and `St_n(R)` is presented on symbols
`(i, j, r) : Fin n × Fin n × R`.  This file repeats those five definitions with the same bodies,
under the names `chalGenerator`, `chalRelation`, `ChalResolventRing`, `chalSteinbergRelations`
and `ChalSteinbergGroup`, and proves the challenge statement over them
(`explicit_fp_overgroup_of_all_gl_n_q`).  The bodies agree with the challenge's, so the
challenge statement follows by unfolding definitions.

Two isomorphisms carry `steinberg_ten_resolvent_contains_all_gl` over:

* `ChalResolventRing ≃+* ResolventRing` (`resolventEquiv`): both are presented by the same nine
  relations, one as a `RingQuot` and one as a quotient by a two-sided ideal;
* `ChalSteinbergGroup n R ≃* St_{Fin n}(R)` (`steinbergEquiv`): the symbols `(i, i, r)` are
  trivial, and the remaining relators are the repository's Steinberg relators.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

open SteinbergGroup

/-! ## The challenge's definitions -/

/-- The generators `s₁, s₂, t₁, t₂, N, A` of `R_L`, numbered `0, …, 5`. -/
def chalGenerator (i : Fin 6) : FreeAlgebra ℤ (Fin 6) :=
  FreeAlgebra.ι ℤ i

/-- The nine defining relations of `R_L`: `tᵢ sⱼ = δᵢⱼ`, `s₁ t₁ + s₂ t₂ = 1`,
`N s₁ = s₁ (N + 1)`, `N s₂ = 0` and `A (N + 1) = 1 = (N + 1) A`. -/
def chalRelation (a b : FreeAlgebra ℤ (Fin 6)) : Prop :=
  let s₁ := chalGenerator 0
  let s₂ := chalGenerator 1
  let t₁ := chalGenerator 2
  let t₂ := chalGenerator 3
  let N := chalGenerator 4
  let A := chalGenerator 5
  (a, b) ∈ ({(t₁ * s₁, 1), (t₁ * s₂, 0), (t₂ * s₁, 0), (t₂ * s₂, 1),
    (s₁ * t₁ + s₂ * t₂, 1), (N * s₁, s₁ * (N + 1)), (N * s₂, 0), (A * (N + 1), 1),
    ((N + 1) * A, 1)} : Set (FreeAlgebra ℤ (Fin 6) × FreeAlgebra ℤ (Fin 6)))

/-- The ring `R_L = ℤ⟨s₁, s₂, t₁, t₂, N, A⟩` modulo the nine relations above. -/
abbrev ChalResolventRing : Type :=
  RingQuot chalRelation

/-- The Steinberg relations on the symbols `x_ij(r)`: `x_ii(r) = 1`,
`x_ij(r) x_ij(s) = x_ij(r + s)`, `[x_ij(r), x_jk(s)] = x_ik(r s)` for distinct `i, j, k`,
and `[x_ij(r), x_kl(s)] = 1` for `i ≠ j`, `k ≠ l`, `j ≠ k`, `i ≠ l`. -/
def chalSteinbergRelations (n : ℕ) (R : Type) [Ring R] : Set (FreeGroup (Fin n × Fin n × R)) :=
  {w | (∃ (i : Fin n) (r : R), w = FreeGroup.of (i, i, r)) ∨
    (∃ (i j : Fin n) (r s : R),
      w = FreeGroup.of (i, j, r) * FreeGroup.of (i, j, s) * (FreeGroup.of (i, j, r + s))⁻¹) ∨
    (∃ (i j k : Fin n) (r s : R), i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      w = FreeGroup.of (i, j, r) * FreeGroup.of (j, k, s) * (FreeGroup.of (i, j, r))⁻¹ *
        (FreeGroup.of (j, k, s))⁻¹ * (FreeGroup.of (i, k, r * s))⁻¹) ∨
    (∃ (i j k l : Fin n) (r s : R), i ≠ j ∧ k ≠ l ∧ j ≠ k ∧ i ≠ l ∧
      w = FreeGroup.of (i, j, r) * FreeGroup.of (k, l, s) * (FreeGroup.of (i, j, r))⁻¹ *
        (FreeGroup.of (k, l, s))⁻¹)}

/-- The Steinberg group `St_n(R)`. -/
abbrev ChalSteinbergGroup (n : ℕ) (R : Type) [Ring R] : Type :=
  PresentedGroup (chalSteinbergRelations n R)

/-! ## The two presentations of `R_L` -/

section Ring

/-- Every relator of `resolventRelatorList` vanishes under a ring homomorphism that sends the
generators to a resolvent tuple. -/
theorem relator_eq_zero {B : Type*} [Ring B] (f : FreeAlgebra ℤ (Fin 6) →+* B)
    (h : IsResolventTuple (f (gen 0)) (f (gen 1)) (f (gen 2)) (f (gen 3)) (f (gen 4))
      (f (gen 5)))
    {x : FreeAlgebra ℤ (Fin 6)} (hx : x ∈ resolventRelatorList) : f x = 0 := by
  simp only [resolventRelatorList, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_sub, map_mul, map_add, map_one]
  · rw [h.t₁s₁, sub_self]
  · exact h.t₁s₂
  · exact h.t₂s₁
  · rw [h.t₂s₂, sub_self]
  · rw [h.sum, sub_self]
  · rw [h.Ns₁]; noncomm_ring
  · exact h.Ns₂
  · calc f (gen 5) * f (gen 4) + f (gen 5) - 1 = f (gen 5) * (f (gen 4) + 1) - 1 := by
          noncomm_ring
      _ = 0 := by rw [h.AN, sub_self]
  · calc f (gen 4) * f (gen 5) + f (gen 5) - 1 = (f (gen 4) + 1) * f (gen 5) - 1 := by
          noncomm_ring
      _ = 0 := by rw [h.NA, sub_self]

/-- The quotient map of the challenge presentation. -/
abbrev chalMk : FreeAlgebra ℤ (Fin 6) →+* ChalResolventRing :=
  RingQuot.mkRingHom chalRelation

theorem chalMk_rel {a b : FreeAlgebra ℤ (Fin 6)} (h : chalRelation a b) : chalMk a = chalMk b :=
  RingQuot.mkRingHom_rel h

/-- The generators of the challenge presentation form a resolvent tuple. -/
theorem chal_isResolventTuple :
    IsResolventTuple (chalMk (chalGenerator 0)) (chalMk (chalGenerator 1))
      (chalMk (chalGenerator 2)) (chalMk (chalGenerator 3)) (chalMk (chalGenerator 4))
      (chalMk (chalGenerator 5)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using chalMk_rel (a := chalGenerator 2 * chalGenerator 0) (b := 1)
      (by simp [chalRelation])
  · simpa using chalMk_rel (a := chalGenerator 2 * chalGenerator 1) (b := 0)
      (by simp [chalRelation])
  · simpa using chalMk_rel (a := chalGenerator 3 * chalGenerator 0) (b := 0)
      (by simp [chalRelation])
  · simpa using chalMk_rel (a := chalGenerator 3 * chalGenerator 1) (b := 1)
      (by simp [chalRelation])
  · simpa using chalMk_rel
      (a := chalGenerator 0 * chalGenerator 2 + chalGenerator 1 * chalGenerator 3) (b := 1)
      (by simp [chalRelation])
  · simpa using chalMk_rel (a := chalGenerator 4 * chalGenerator 0)
      (b := chalGenerator 0 * (chalGenerator 4 + 1)) (by simp [chalRelation])
  · simpa using chalMk_rel (a := chalGenerator 4 * chalGenerator 1) (b := 0)
      (by simp [chalRelation])
  · simpa using chalMk_rel (a := chalGenerator 5 * (chalGenerator 4 + 1)) (b := 1)
      (by simp [chalRelation])
  · simpa using chalMk_rel (a := (chalGenerator 4 + 1) * chalGenerator 5) (b := 1)
      (by simp [chalRelation])

/-- `R_L → ChalResolventRing`. -/
def toChal : ResolventRing →+* ChalResolventRing :=
  (TwoSidedIdeal.span resolventRelators).ringCon.lift chalMk (by
    have hspan : TwoSidedIdeal.span resolventRelators ≤ TwoSidedIdeal.ker chalMk := by
      rw [TwoSidedIdeal.span_le]
      intro x hx
      rw [SetLike.mem_coe, TwoSidedIdeal.mem_ker]
      exact relator_eq_zero chalMk chal_isResolventTuple hx
    intro x y hxy
    have hm := (TwoSidedIdeal.mem_ker _).mp (hspan ((TwoSidedIdeal.rel_iff _ x y).mp hxy))
    rw [map_sub, sub_eq_zero] at hm
    exact hm)

/-- `ChalResolventRing → R_L`. -/
def toRes : ChalResolventRing →+* ResolventRing :=
  RingQuot.lift ⟨resolventMk, fun a b h ↦ by
    simp only [chalRelation, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [map_mul, map_add, map_one, map_zero]
    · exact isResolventTuple.t₁s₁
    · exact isResolventTuple.t₁s₂
    · exact isResolventTuple.t₂s₁
    · exact isResolventTuple.t₂s₂
    · exact isResolventTuple.sum
    · exact isResolventTuple.Ns₁
    · exact isResolventTuple.Ns₂
    · exact isResolventTuple.AN
    · exact isResolventTuple.NA⟩

theorem toRes_chalMk (x : FreeAlgebra ℤ (Fin 6)) : toRes (chalMk x) = resolventMk x :=
  RingQuot.lift_mkRingHom_apply _ _ _

theorem toChal_resolventMk (x : FreeAlgebra ℤ (Fin 6)) : toChal (resolventMk x) = chalMk x :=
  rfl

/-- **The two presentations of `R_L` agree.** -/
def resolventEquiv : ChalResolventRing ≃+* ResolventRing :=
  RingEquiv.ofRingHom toRes toChal
    (RingCon.Quotient.hom_ext (RingHom.ext fun x ↦ by
      change toRes (toChal (resolventMk x)) = resolventMk x
      rw [toChal_resolventMk, toRes_chalMk]))
    (RingQuot.ringQuot_ext _ _ (RingHom.ext fun x ↦ by
      change toChal (toRes (chalMk x)) = chalMk x
      rw [toRes_chalMk, toChal_resolventMk]))

end Ring

/-! ## The two presentations of `St_n(R)` -/

section Group

variable (n : ℕ) (R : Type) [Ring R]

/-- The challenge relators are trivial in the challenge group. -/
theorem chal_mk_eq_one {w : FreeGroup (Fin n × Fin n × R)} (hw : w ∈ chalSteinbergRelations n R) :
    PresentedGroup.mk (chalSteinbergRelations n R) w = 1 :=
  PresentedGroup.one_of_mem hw

variable {n R}

/-- The image of a challenge symbol. -/
def chalGen (g : Fin n × Fin n × R) : SteinbergGroup (Fin n) R :=
  if h : g.1 = g.2.1 then 1 else x g.1 g.2.1 h g.2.2

theorem chalGen_self (i : Fin n) (r : R) : chalGen (i, i, r) = 1 :=
  dif_pos rfl

theorem chalGen_of_ne {i j : Fin n} (h : i ≠ j) (r : R) : chalGen (i, j, r) = x i j h r :=
  dif_neg h

variable (n R)

/-- `ChalSteinbergGroup n R → St_{Fin n}(R)`. -/
def fromChal : ChalSteinbergGroup n R →* SteinbergGroup (Fin n) R :=
  PresentedGroup.toGroup (f := chalGen) (by
    rintro w (⟨i, r, rfl⟩ | ⟨i, j, r, s, rfl⟩ | ⟨i, j, k, r, s, hij, hjk, hik, rfl⟩ |
      ⟨i, j, k, l, r, s, hij, hkl, hjk, hil, rfl⟩)
    · rw [FreeGroup.lift_apply_of, chalGen_self]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      by_cases hij : i = j
      · subst hij
        rw [chalGen_self, chalGen_self, chalGen_self, one_mul, inv_one, one_mul]
      · rw [chalGen_of_ne hij, chalGen_of_ne hij, chalGen_of_ne hij, x_mul, mul_inv_cancel]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [chalGen_of_ne hij, chalGen_of_ne hjk, chalGen_of_ne hik, ← commutatorElement_def,
        x_commutator i j k hij hjk hik, mul_inv_cancel]
    · simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [chalGen_of_ne hij, chalGen_of_ne hkl, ← commutatorElement_def]
      exact (x_commute_of_ne i j k l hij hkl hjk (Ne.symm hil) r s).commutator_eq)

theorem fromChal_of (g : Fin n × Fin n × R) : fromChal n R (PresentedGroup.of g) = chalGen g :=
  PresentedGroup.toGroup.of _

/-- `St_{Fin n}(R) → ChalSteinbergGroup n R`. -/
def toChalSt : SteinbergGroup (Fin n) R →* ChalSteinbergGroup n R :=
  PresentedGroup.toGroup
    (f := fun g : SteinbergGenerator (Fin n) R ↦ PresentedGroup.of (g.row, g.column, g.coefficient))
    (by
      intro w hw
      change SteinbergGroup.IsRelation w at hw
      cases hw with
      | add i j hij a b =>
          have h := chal_mk_eq_one n R (Or.inr (Or.inl ⟨i, j, a, b, rfl⟩))
          simp only [map_mul, map_inv] at h
          simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
          exact h
      | commute i j k l hij hkl hjk hli a b =>
          have h := chal_mk_eq_one n R
            (Or.inr (Or.inr (Or.inr ⟨i, j, k, l, a, b, hij, hkl, hjk, Ne.symm hli, rfl⟩)))
          simp only [map_mul, map_inv] at h
          simp only [commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
          exact h
      | adjacent i j k hij hjk hik a b =>
          have h := chal_mk_eq_one n R
            (Or.inr (Or.inr (Or.inl ⟨i, j, k, a, b, hij, hjk, hik, rfl⟩)))
          simp only [map_mul, map_inv] at h
          simp only [commutatorElement_def, map_mul, map_inv, FreeGroup.lift_apply_of]
          exact h)

theorem toChalSt_x (i j : Fin n) (h : i ≠ j) (r : R) :
    toChalSt n R (x i j h r) = PresentedGroup.of (i, j, r) :=
  PresentedGroup.toGroup.of _

/-- **The two presentations of `St_n(R)` agree.** -/
def steinbergEquiv : ChalSteinbergGroup n R ≃* SteinbergGroup (Fin n) R :=
  MonoidHom.toMulEquiv (fromChal n R) (toChalSt n R)
    (by
      apply PresentedGroup.ext
      rintro ⟨i, j, r⟩
      change toChalSt n R (fromChal n R (PresentedGroup.of (i, j, r))) = PresentedGroup.of (i, j, r)
      rw [fromChal_of]
      by_cases h : i = j
      · subst h
        rw [chalGen_self, map_one]
        exact (chal_mk_eq_one n R (Or.inl ⟨i, r, rfl⟩)).symm
      · rw [chalGen_of_ne h, toChalSt_x])
    (by
      apply PresentedGroup.ext
      rintro ⟨i, j, h, r⟩
      change fromChal n R (toChalSt n R (x i j h r)) = x i j h r
      rw [toChalSt_x, fromChal_of, chalGen_of_ne h])

end Group

/-! ## The challenge statement -/

/-- **Kourovka 14.10(c), BBMZ Problem 2.7**, in the form of `Palomar/BooneHigmanChallenge.lean`:
the explicit finitely presented group `St_10(R_L)` contains every `GL_n(ℚ)`. -/
theorem explicit_fp_overgroup_of_all_gl_n_q :
    Group.IsFinitelyPresented (ChalSteinbergGroup 10 ChalResolventRing) ∧
      ∀ n : ℕ, ∃ f : Matrix.GeneralLinearGroup (Fin n) ℚ →*
        ChalSteinbergGroup 10 ChalResolventRing, Function.Injective f := by
  let e : ChalSteinbergGroup 10 ChalResolventRing ≃* SteinbergGroup (Fin 10) ResolventRing :=
    (steinbergEquiv 10 ChalResolventRing).trans (coefficientEquiv resolventEquiv)
  obtain ⟨hfp, hgl⟩ := steinberg_ten_resolvent_contains_all_gl
  refine ⟨?_, fun n ↦ ?_⟩
  · haveI := hfp
    exact Group.IsFinitelyPresented.equiv e.symm
  · obtain ⟨f, hf⟩ := hgl n
    exact ⟨e.symm.toMonoidHom.comp f, e.symm.injective.comp hf⟩

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.resolventEquiv
#audit_axioms GroupApproximation.SteinbergFP.steinbergEquiv
#audit_axioms GroupApproximation.SteinbergFP.explicit_fp_overgroup_of_all_gl_n_q
