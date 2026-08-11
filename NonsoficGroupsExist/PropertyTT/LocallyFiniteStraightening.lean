import NonsoficGroupsExist.PropertyTT.FiniteSubgroupAverage
import NonsoficGroupsExist.PropertyTT.WeakUltralimit

/-!
# Straightening quasi-cocycles on an exhaustively locally finite subgroup

Let `A` be covered by a sequence of finite subgroups.  For a quasi-cocycle
`b` and `a ∈ A`, average

`rho(x⁻¹) (b (x * a) - b x)`

over the finite stages.  Every summand differs from `b a` by at most the
defect.  A weak ultralimit therefore exists.  Right translation by a fixed
element eventually permutes the finite stages, so the limiting map is an
honest cocycle on `A` and remains uniformly defect-close to `b` there.

This is the direct invariant-averaging argument needed below; no amenability
or relative-rigidity theorem is assumed.
-/

namespace NonsoficGroupsExist

open Filter
open scoped InnerProductSpace

universe u v

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A sequence of subgroups eventually contains every member of `A`. -/
def ExhaustsSubgroup (A : Subgroup G) (F : ℕ → Subgroup G) : Prop :=
  (∀ n, F n ≤ A) ∧
    ∀ a : A, ∃ N : ℕ, ∀ n, N ≤ n → (a : G) ∈ F n

/-- A monotone chain whose supremum is `A` exhausts `A` in the concrete
eventual-membership sense used by finite averaging. -/
theorem exhaustsSubgroup_of_monotone_iSup
    (A : Subgroup G) (F : ℕ → Subgroup G) (hmono : Monotone F)
    (hsup : ⨆ n, F n = A) : ExhaustsSubgroup A F := by
  refine ⟨?_, ?_⟩
  · intro n
    rw [← hsup]
    exact le_iSup F n
  · intro a
    have haSup : (a : G) ∈ ⨆ n, F n := by
      rw [hsup]
      exact a.property
    obtain ⟨N, hN⟩ :=
      (Subgroup.mem_iSup_of_directed hmono.directed_le).mp haSup
    exact ⟨N, fun n hn ↦ hmono hn hN⟩

/-- The translated quasi-increment based at `x`. -/
def straighteningIncrement
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (b : G → E) (x : G) (a : G) : E :=
  rho x⁻¹ (b (x * a) - b x)

/-- The finite-stage average of translated quasi-increments. -/
noncomputable def straighteningStage
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (b : G → E)
    (F : Subgroup G) (hfinite : Finite F) (a : G) : E := by
  letI := hfinite
  letI := Fintype.ofFinite F
  exact ((Nat.card F : ℂ)⁻¹) •
    ∑ x : F, straighteningIncrement rho b x a

omit [CompleteSpace E] in
/-- A translated quasi-increment differs from the original value only by
the quasi-cocycle defect. -/
theorem norm_straighteningIncrement_sub_le
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D) (x a : G) :
    ‖straighteningIncrement rho b x a - b a‖ ≤ D := by
  have herr := hb.2 x a
  have hid : straighteningIncrement rho b x a - b a =
      rho x⁻¹ (b (x * a) - b x - rho x (b a)) := by
    unfold straighteningIncrement
    rw [map_sub, map_sub]
    simp
  rw [hid, (rho x⁻¹).norm_map]
  exact herr

omit [CompleteSpace E] in
/-- Each finite-stage average remains defect-close to `b a`. -/
theorem norm_straighteningStage_sub_le
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D)
    (F : Subgroup G) (hfinite : Finite F) (a : G) :
    ‖straighteningStage rho b F hfinite a - b a‖ ≤ D := by
  letI := hfinite
  letI := Fintype.ofFinite F
  let f : F → E := fun x ↦ straighteningIncrement rho b x a - b a
  have hf (x : F) : ‖f x‖ ≤ D :=
    norm_straighteningIncrement_sub_le hb x a
  have havg := norm_cardInv_smul_sum_le f hf
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hid :
      ((Nat.card F : ℂ)⁻¹ • ∑ x : F, f x) =
        straighteningStage rho b F hfinite a - b a := by
    unfold straighteningStage
    dsimp [f]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card]
    rw [smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hcard, one_smul]
  rw [← hid]
  exact havg

omit [CompleteSpace E] in
/-- Uniform norm bound for every finite-stage average. -/
theorem norm_straighteningStage_le
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D)
    (F : Subgroup G) (hfinite : Finite F) (a : G) :
    ‖straighteningStage rho b F hfinite a‖ ≤ ‖b a‖ + D := by
  calc
    ‖straighteningStage rho b F hfinite a‖ ≤
        ‖straighteningStage rho b F hfinite a - b a‖ + ‖b a‖ := by
      have := norm_add_le
        (straighteningStage rho b F hfinite a - b a) (b a)
      simpa only [sub_add_cancel] using this
    _ ≤ D + ‖b a‖ := add_le_add
      (norm_straighteningStage_sub_le hb F hfinite a) le_rfl
    _ = ‖b a‖ + D := add_comm _ _

omit [CompleteSpace E] in
/-- The translated increments satisfy an exact telescoping identity.  No
cocycle hypothesis on `b` is used here. -/
theorem straighteningIncrement_mul
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (b : G → E) (x a c : G) :
    straighteningIncrement rho b x (a * c) =
      straighteningIncrement rho b x a +
        rho a (straighteningIncrement rho b (x * a) c) := by
  unfold straighteningIncrement
  have hmap : rho a * rho (x * a)⁻¹ = rho x⁻¹ := by
    rw [← rho.map_mul]
    congr 1
    group
  have hsplit : b (x * (a * c)) - b x =
      (b (x * a) - b x) + (b ((x * a) * c) - b (x * a)) := by
    rw [mul_assoc]
    abel
  rw [hsplit, map_add]
  congr 1
  change rho x⁻¹ (b ((x * a) * c) - b (x * a)) =
    (rho a * rho (x * a)⁻¹) (b ((x * a) * c) - b (x * a))
  rw [hmap]

omit [CompleteSpace E] in
/-- Right translation by a member of a finite subgroup permutes the sum of
translated increments. -/
theorem sum_straighteningIncrement_mul_right
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (b : G → E)
    (F : Subgroup G) [Fintype F] (a : F) (c : G) :
    (∑ x : F, straighteningIncrement rho b ((x : G) * a) c) =
      ∑ x : F, straighteningIncrement rho b x c := by
  exact Fintype.sum_equiv (Equiv.mulRight a)
    (fun x : F ↦ straighteningIncrement rho b ((x : G) * a) c)
    (fun x : F ↦ straighteningIncrement rho b x c)
    (fun _ ↦ rfl)

omit [CompleteSpace E] in
/-- Once `a` belongs to the finite stage, finite averaging turns the
telescoping identity into the exact cocycle identity. -/
theorem straighteningStage_mul
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (b : G → E)
    (F : Subgroup G) (hfinite : Finite F) (a c : G) (ha : a ∈ F) :
    straighteningStage rho b F hfinite (a * c) =
      straighteningStage rho b F hfinite a +
        rho a (straighteningStage rho b F hfinite c) := by
  letI := hfinite
  letI := Fintype.ofFinite F
  let aa : F := ⟨a, ha⟩
  unfold straighteningStage
  simp_rw [straighteningIncrement_mul]
  rw [Finset.sum_add_distrib, smul_add, map_smul, map_sum]
  congr 1
  have hsum := sum_straighteningIncrement_mul_right rho b F aa c
  have hmapped := congrArg
    (fun z : E ↦ ((Nat.card F : ℂ)⁻¹) • rho a z) hsum
  simpa only [map_sum] using hmapped

/-- Weak-limit straightening along an exhaustive finite-subgroup chain. -/
noncomputable def straightenedCocycle
    (rho : G →* (E ≃ₗᵢ[ℂ] E)) (b : G → E) (D : ℝ)
    (hb : IsQuasiCocycle rho b D)
    (F : ℕ → Subgroup G) (hfinite : ∀ n, Finite (F n))
    (a : G) : E :=
  weakUltralimit
    (fun n ↦ straighteningStage rho b (F n) (hfinite n) a)
    (‖b a‖ + D)
    (fun n ↦ norm_straighteningStage_le hb (F n) (hfinite n) a)

/-- The straightened value stays within one defect of the original
quasi-cocycle value. -/
theorem norm_straightenedCocycle_sub_le
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D)
    (F : ℕ → Subgroup G) (hfinite : ∀ n, Finite (F n)) (a : G) :
    ‖straightenedCocycle rho b D hb F hfinite a - b a‖ ≤ D := by
  let stage : ℕ → E := fun n ↦
    straighteningStage rho b (F n) (hfinite n) a
  let constant : ℕ → E := fun _ ↦ b a
  have hstage : ∀ n, ‖stage n‖ ≤ ‖b a‖ + D := fun n ↦
    norm_straighteningStage_le hb (F n) (hfinite n) a
  have hconstant : ∀ n, ‖constant n‖ ≤ ‖b a‖ := fun _ ↦ le_rfl
  have hdist : ∀ n, ‖stage n - constant n‖ ≤ D := fun n ↦
    norm_straighteningStage_sub_le hb (F n) (hfinite n) a
  have h := norm_weakUltralimit_sub_le stage constant
    (‖b a‖ + D) ‖b a‖ D hstage hconstant hdist
  rw [weakUltralimit_const (b a) ‖b a‖ le_rfl] at h
  exact h

/-- Along an exhaustive finite-subgroup chain, the straightened map obeys
the exact cocycle identity whenever the first factor belongs to the
exhausted subgroup. -/
theorem straightenedCocycle_mul_of_exhausts
    {rho : G →* (E ≃ₗᵢ[ℂ] E)} {b : G → E} {D : ℝ}
    (hb : IsQuasiCocycle rho b D)
    (A : Subgroup G) (F : ℕ → Subgroup G)
    (hfinite : ∀ n, Finite (F n)) (hexhausts : ExhaustsSubgroup A F)
    (a c : G) (ha : a ∈ A) :
    straightenedCocycle rho b D hb F hfinite (a * c) =
      straightenedCocycle rho b D hb F hfinite a +
        rho a (straightenedCocycle rho b D hb F hfinite c) := by
  let stageAC : ℕ → E := fun n ↦
    straighteningStage rho b (F n) (hfinite n) (a * c)
  let stageA : ℕ → E := fun n ↦
    straighteningStage rho b (F n) (hfinite n) a
  let stageC : ℕ → E := fun n ↦
    straighteningStage rho b (F n) (hfinite n) c
  let movedC : ℕ → E := fun n ↦ rho a (stageC n)
  let combined : ℕ → E := fun n ↦ stageA n + movedC n
  let CAC : ℝ := ‖b (a * c)‖ + D
  let CA : ℝ := ‖b a‖ + D
  let CC : ℝ := ‖b c‖ + D
  have hAC : ∀ n, ‖stageAC n‖ ≤ CAC := fun n ↦
    norm_straighteningStage_le hb (F n) (hfinite n) (a * c)
  have hA : ∀ n, ‖stageA n‖ ≤ CA := fun n ↦
    norm_straighteningStage_le hb (F n) (hfinite n) a
  have hC : ∀ n, ‖stageC n‖ ≤ CC := fun n ↦
    norm_straighteningStage_le hb (F n) (hfinite n) c
  have hmovedC : ∀ n, ‖movedC n‖ ≤ CC := fun n ↦ by
    simpa [movedC] using hC n
  have hcombined : ∀ n, ‖combined n‖ ≤ CA + CC := fun n ↦ by
    calc
      ‖combined n‖ ≤ ‖stageA n‖ + ‖movedC n‖ := by
        exact norm_add_le _ _
      _ ≤ CA + CC := add_le_add (hA n) (hmovedC n)
  obtain ⟨N, hN⟩ := hexhausts.2 ⟨a, ha⟩
  have hlarge : ∀ᶠ n in hyperfilter ℕ, N ≤ n :=
    Nat.hyperfilter_le_atTop (eventually_ge_atTop N)
  have heventual : stageAC =ᶠ[hyperfilter ℕ] combined := by
    filter_upwards [hlarge] with n hn
    exact straighteningStage_mul rho b (F n) (hfinite n) a c (hN n hn)
  have hEq := weakUltralimit_eq_of_eventuallyEq
    stageAC combined CAC (CA + CC) hAC hcombined heventual
  have hAdd := weakUltralimit_add stageA movedC CA CC hA hmovedC hcombined
  have hMap := weakUltralimit_linearIsometryEquiv
    (rho a) stageC CC hC hmovedC
  have hfinal : weakUltralimit stageAC CAC hAC =
      weakUltralimit stageA CA hA +
        rho a (weakUltralimit stageC CC hC) := by
    rw [hEq, hAdd, hMap]
  simpa [straightenedCocycle, stageAC, stageA, stageC, CAC, CA, CC]
    using hfinal

end NonsoficGroupsExist
