import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitLongReduce
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCPivotYComplete
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# The replicate stem swap lands in an antichain subgroup (lane bh-met-92m)

Notation as in `EnvelopeHigmanVCOrbitLongPath`: `t = m(a, b)` with `a`, `b` incomparable.
Write `R a b Q = a · pathSet [] ∪ b · pathSet Q` (`higmanVCOrbitStem_R`, an antichain).

**Claim** (`higmanVCOrbitStem_rep_mem_H`): for every letter `y` and every `m`,
`m(a, b yᵐ⁺¹) · t · m(b, a y) ∈ H_{R a b yᵐ}`.
* `m = 0`: `t m(b, a y) t⁻¹ = m(a, b y)` (`higmanVCOrbitStem_conj`) and `m(a, b y)² = 1`
  make the product equal to `t`, which splits over `a i`, `b i`.
* `m → m + 1`: apply the claim to the pivot `(a, b y)`.  Then
  `A t W = (A T' W') (W' t)`, where `T' = m(a, b y)`, `W = m(b, a y)` and
  `W' = m(b y, a y)`.  The identity uses only `t W t⁻¹ = T'` and `W'² = 1`.  Also
  `W' t = m(a y, b y)⁻¹ t` is the one-letter path peel, and `R a (b y) yᵐ ⊆ R a b yᵐ⁺¹`.
This is an induction in which the pivot moves; it carries antichain membership, not `S`
membership.  It does not use the circular identity `m(a, b y r) t = L⁻¹ (t P t⁻¹) t w`.
It was checked on permutations of words in `V_d` by `scratchpad/bh-met-92m/check_stem.py`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- The replicate antichain `a · pathSet [] ∪ b · pathSet Q`. -/
def higmanVCOrbitStem_R {d : ℕ} (a b Q : List (Fin d)) : Finset (List (Fin d)) :=
  (higmanVCOrbitAll_pathSet ([] : List (Fin d))).image (a ++ ·) ∪
    (higmanVCOrbitAll_pathSet Q).image (b ++ ·)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_R

theorem higmanVCOrbitStem_mem_R_a {d : ℕ} {a b Q e u : List (Fin d)}
    (he : e ∈ higmanVCOrbitAll_pathSet ([] : List (Fin d))) (hu : a ++ e = u) :
    u ∈ higmanVCOrbitStem_R a b Q := by
  rw [higmanVCOrbitStem_R]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, hu⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_mem_R_a

theorem higmanVCOrbitStem_mem_R_b {d : ℕ} {a b Q e u : List (Fin d)}
    (he : e ∈ higmanVCOrbitAll_pathSet Q) (hu : b ++ e = u) :
    u ∈ higmanVCOrbitStem_R a b Q := by
  rw [higmanVCOrbitStem_R]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, hu⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_mem_R_b

/-- The replicate antichain is an antichain. -/
theorem higmanVCOrbitStem_R_isAC {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (Q : List (Fin d)) :
    higmanVCTreeNFWitPivot_IsAC (higmanVCOrbitStem_R a b Q) := by
  have hA := higmanVCOrbitAll_pathSet_isAC ([] : List (Fin d))
  have hB := higmanVCOrbitAll_pathSet_isAC Q
  intro u hu v hv huv hpre
  simp only [higmanVCOrbitStem_R, Finset.mem_union, Finset.mem_image] at hu hv
  rcases hu with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · rcases hv with ⟨e', he', rfl⟩ | ⟨e', -, rfl⟩
    · exact hA e he e' he' (fun h => huv (by rw [h])) ((List.prefix_append_right_inj a).mp hpre)
    · exact higmanVCOrbitGap_incomp_append hab hba e e' hpre
  · rcases hv with ⟨e', -, rfl⟩ | ⟨e', he', rfl⟩
    · exact higmanVCOrbitGap_incomp_append hba hab e e' hpre
    · exact hB e he e' he' (fun h => huv (by rw [h])) ((List.prefix_append_right_inj b).mp hpre)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_R_isAC

/-- Moving the pivot from `(a, b)` to `(a, b y)` stays inside the antichain. -/
theorem higmanVCOrbitStem_R_sub {d : ℕ} (a b Q : List (Fin d)) (y : Fin d) :
    higmanVCOrbitStem_R a (b ++ [y]) Q ⊆ higmanVCOrbitStem_R a b (y :: Q) := by
  intro u hu
  simp only [higmanVCOrbitStem_R, Finset.mem_union, Finset.mem_image] at hu
  rcases hu with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · exact higmanVCOrbitStem_mem_R_a he rfl
  · refine higmanVCOrbitStem_mem_R_b (e := y :: e) ?_ (by simp)
    rw [higmanVCOrbitAll_pathSet]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_R_sub

/-- The pivot conjugates `m(b, a y)` to `m(a, b y)`. -/
theorem higmanVCOrbitStem_conj {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (y : Fin d) :
    higmanVCCommon_mk d (FreeGroup.of (a, b)) *
        higmanVCCommon_mk d (FreeGroup.of (b, a ++ [y])) *
        (higmanVCCommon_mk d (FreeGroup.of (a, b)))⁻¹ =
      higmanVCCommon_mk d (FreeGroup.of (a, b ++ [y])) :=
  higmanVCOrbitGen_conj hab hba (mapsCone_coneSwap_right hab hba)
    ((mapsCone_coneSwap_left hab hba).append [y])
    (higmanVCOrbitGen_incomp hba hab (List.prefix_refl b) (List.prefix_append a [y]))
    (higmanVCOrbitGen_incomp hab hba (List.prefix_append a [y]) (List.prefix_refl b))
    (higmanVCOrbitGen_incomp hab hba (List.prefix_refl a) (List.prefix_append b [y]))
    (higmanVCOrbitGen_incomp hba hab (List.prefix_append b [y]) (List.prefix_refl a))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_conj

/-- The base identity: `T' T W = T` when `T W T⁻¹ = T'` and `T'² = 1`. -/
theorem higmanVCOrbitStem_base_eq {G : Type*} [Group G] {T W T' : G}
    (hc : T * W * T⁻¹ = T') (hsq : T' * T' = 1) : T' * T * W = T := by
  calc T' * T * W = T' * (T * W * T⁻¹) * T := by group
    _ = T := by rw [hc, hsq, one_mul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_base_eq

/-- The step identity: `A T W = (A T' W') (W' T)` when `T W T⁻¹ = T'` and `W'² = 1`. -/
theorem higmanVCOrbitStem_step_eq {G : Type*} [Group G] {A T W T' W' : G}
    (hc : T * W * T⁻¹ = T') (hsq : W' * W' = 1) :
    A * T * W = A * T' * W' * (W' * T) := by
  calc A * T * W = A * (T * W * T⁻¹) * T := by group
    _ = A * T' * (W' * W') * T := by rw [hc, hsq, mul_one]
    _ = A * T' * W' * (W' * T) := by group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_step_eq

/-- The pivot lies in the subgroup of `R a b []`. -/
theorem higmanVCOrbitStem_t_mem {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) :
    higmanVCCommon_mk d (FreeGroup.of (a, b)) ∈
      higmanVCTreeNFWitPivot_H d (higmanVCOrbitStem_R a b []) := by
  rw [higmanVCCommon_mk_split hab hba, higmanVC_splitAll]
  exact higmanVCOrbitGen_split_mem a b (List.finRange d) fun i _ =>
    higmanVCLeafExp_letter_mem_H
      (higmanVCOrbitStem_mem_R_a (higmanVCOrbitAll_mem_child [] i) (by simp))
      (higmanVCOrbitStem_mem_R_b (higmanVCOrbitAll_mem_child [] i) (by simp))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitStem_t_mem
