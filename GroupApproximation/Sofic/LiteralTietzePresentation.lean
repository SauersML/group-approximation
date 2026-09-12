import GroupApproximation.Sofic.LiteralSixGenerator
import GroupApproximation.Sofic.LiteralBaseRelations

/-!
# The Tietze-eliminated six-letter presentation

The manuscript states that the eight-generator, forty-one-relator
presentation of `E` has a Tietze-equivalent presentation on the six
letters `v₁,x,y,z,t,c` with thirty-two relators, obtained by substituting
`v₃ = x v₁ x⁻¹` and `v₂ = x² v₁ x⁻²` and deleting nine relators.  This
file carries out that elimination formally.

The nine deletions are exactly the ones the manuscript names:

* the two defining relations `x v₁ x⁻¹ v₃⁻¹` and `x v₃ x⁻¹ v₂⁻¹`, which
  become trivial *in the free group* once the substitution is made;
* the remaining `x`-action relation `x v₂ x⁻¹ v₁⁻¹`, which needs `x³ = 1`;
* the stable-letter relations for `v₂` and `v₃`, which follow from the one
  for `v₁` together with `t x t⁻¹ = x`;
* the `c`-commutation relations for `v₂` and `v₃`, and the centrality
  relations for `v₂` and `v₃`, which follow from those for `v₁` and `x`
  because a centralizer is a subgroup.

Everything below the first bullet is a genuine derivation rather than a
free identity, which is why the elimination is a theorem and not a
definition.
-/

namespace GroupApproximation
namespace LiteralTietzePresentation

open LiteralNonMFPresentation LiteralSixGenerator

noncomputable section

/-! ## The six retained letters -/

abbrev sv1 : FreeGroup SixGenerator := FreeGroup.of 0
abbrev sx : FreeGroup SixGenerator := FreeGroup.of 1
abbrev sy : FreeGroup SixGenerator := FreeGroup.of 2
abbrev sz : FreeGroup SixGenerator := FreeGroup.of 3
abbrev st : FreeGroup SixGenerator := FreeGroup.of 4
abbrev sc : FreeGroup SixGenerator := FreeGroup.of 5

/-- The Tietze substitution on the six base letters: `v₃` and `v₂` are
replaced by their defining words in `v₁` and `x`. -/
def substBase (i : BaseGenerator) : FreeGroup SixGenerator :=
  if i = v1Index then sv1
  else if i = v2Index then sx * (sx * sv1 * sx⁻¹) * sx⁻¹
  else if i = v3Index then sx * sv1 * sx⁻¹
  else if i = xIndex then sx
  else if i = yIndex then sy
  else sz

/-- The substitution on the full eight-letter alphabet. -/
def subst : Generator → FreeGroup SixGenerator
  | Sum.inl i => substBase i
  | Sum.inr j => if j = 0 then st else sc

/-- The induced substitution homomorphism on free words. -/
def substHom : FreeGroup Generator →* FreeGroup SixGenerator :=
  FreeGroup.lift subst

@[simp] theorem substHom_of (g : Generator) :
    substHom (FreeGroup.of g) = subst g := FreeGroup.lift_apply_of

@[simp] theorem substBase_v1 : substBase v1Index = sv1 := rfl
@[simp] theorem substBase_v2 :
    substBase v2Index = sx * (sx * sv1 * sx⁻¹) * sx⁻¹ := rfl
@[simp] theorem substBase_v3 : substBase v3Index = sx * sv1 * sx⁻¹ := rfl
@[simp] theorem substBase_x : substBase xIndex = sx := rfl
@[simp] theorem substBase_y : substBase yIndex = sy := rfl
@[simp] theorem substBase_z : substBase zIndex = sz := rfl

@[simp] theorem subst_stable : subst Generator.stable = st := rfl
@[simp] theorem subst_lamp : subst Generator.lamp = sc := rfl
@[simp] theorem subst_base (i : BaseGenerator) :
    subst (Generator.base i) = substBase i := rfl

theorem substHom_embedBaseWord (w : FreeGroup BaseGenerator) :
    substHom (embedBaseWord w) = FreeGroup.lift substBase w := by
  change (substHom.comp embedBaseWord) w = _
  apply freeGroup_hom_eq_on_generators
  intro i
  simp [embedBaseWord]

/-! ## The thirty-two retained relators -/

/-- The seventeen base relators surviving the elimination: all twenty
except the three `x`-action relations. -/
def retainedBaseList : List (FreeGroup BaseGenerator) :=
  [baseRelXCube, baseRelYCube, baseRelZSq, baseRelXZCube,
   baseRelYZCube, baseRelXInvZXY, baseRelYInvZYX, baseRelXYSix,
   baseRelV12, baseRelV13, baseRelV23,
   baseRelYV1, baseRelYV2, baseRelYV3,
   baseRelZV1, baseRelZV2, baseRelZV3]

/-- The four base letters that survive as letters. -/
def retainedIndices : List BaseGenerator := [v1Index, xIndex, yIndex, zIndex]

/-- The six letters of the eliminated alphabet, inside the original one. -/
def retainedLetters : List Generator :=
  [Generator.base v1Index, Generator.base xIndex, Generator.base yIndex,
   Generator.base zIndex, Generator.stable, Generator.lamp]

/-- The thirty-two relators of the eliminated presentation, before
substitution: seventeen base relators, four stable-letter relations, the
lamp square together with its four commutations, and six centrality
relations.  This is a list rather than a `Finset` precisely so that the
count is the displayed one: a `Finset` would silently identify any two
relators that happened to coincide, and settling whether two free-group
words coincide is exactly the decision this file cannot afford. -/
def retainedList : List (FreeGroup Generator) :=
  (retainedBaseList.map embedBaseWord) ++
    ((retainedIndices.map stableRelator) ++
      (((lampWord ^ 2) :: retainedIndices.map fun i ↦
          commutatorWord lampWord (vertexLetter i)) ++
        (retainedLetters.map fun g ↦
          commutatorWord markedWord (FreeGroup.of g))))

/-- The thirty-two relators of the eliminated presentation. -/
def tietzeRelatorList : List (FreeGroup SixGenerator) :=
  retainedList.map substHom

/-- **Thirty-two relators**, exactly as displayed. -/
@[simp] theorem tietzeRelatorList_length : tietzeRelatorList.length = 32 := rfl

/-- The group presented on six letters by the thirty-two relators. -/
abbrev TietzeGroup : Type := PresentedGroup {r | r ∈ tietzeRelatorList}

/-- The quotient map onto the eliminated presentation. -/
abbrev tietzeWord : FreeGroup SixGenerator →* TietzeGroup :=
  PresentedGroup.mk {r | r ∈ tietzeRelatorList}

/-- Every retained relator dies in the eliminated presentation. -/
theorem tietzeWord_substHom_retained {r : FreeGroup Generator}
    (hr : r ∈ retainedList) : tietzeWord (substHom r) = 1 :=
  PresentedGroup.one_of_mem (List.mem_map_of_mem hr)

/-! ## Membership of the retained relators -/

theorem mem_retainedIndices_v1 : v1Index ∈ retainedIndices :=
  List.Mem.head _
theorem mem_retainedIndices_x : xIndex ∈ retainedIndices :=
  List.Mem.tail _ (List.Mem.head _)
theorem mem_retainedIndices_y : yIndex ∈ retainedIndices :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem mem_retainedIndices_z : zIndex ∈ retainedIndices :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem mem_retainedLetters_v1 : Generator.base v1Index ∈ retainedLetters :=
  List.Mem.head _
theorem mem_retainedLetters_x : Generator.base xIndex ∈ retainedLetters :=
  List.Mem.tail _ (List.Mem.head _)
theorem mem_retainedLetters_y : Generator.base yIndex ∈ retainedLetters :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
theorem mem_retainedLetters_z : Generator.base zIndex ∈ retainedLetters :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
theorem mem_retainedLetters_stable : Generator.stable ∈ retainedLetters :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.head _))))
theorem mem_retainedLetters_lamp : Generator.lamp ∈ retainedLetters :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))

theorem embed_mem_retained {r : FreeGroup BaseGenerator}
    (hr : r ∈ retainedBaseList) : embedBaseWord r ∈ retainedList :=
  List.mem_append_left _ (List.mem_map_of_mem hr)

theorem stable_mem_retained {i : BaseGenerator} (hi : i ∈ retainedIndices) :
    stableRelator i ∈ retainedList :=
  List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem hi))

theorem lampSq_mem_retainedList : lampWord ^ 2 ∈ retainedList :=
  List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (List.Mem.head _)))

theorem lampComm_mem_retained {i : BaseGenerator} (hi : i ∈ retainedIndices) :
    commutatorWord lampWord (vertexLetter i) ∈ retainedList :=
  List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (List.Mem.tail _
      (List.mem_map_of_mem (f := fun i ↦ commutatorWord lampWord (vertexLetter i))
        hi))))

theorem markedComm_mem_retained {g : Generator} (hg : g ∈ retainedLetters) :
    commutatorWord markedWord (FreeGroup.of g) ∈ retainedList :=
  List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _
      (List.mem_map_of_mem (f := fun g ↦ commutatorWord markedWord (FreeGroup.of g))
        hg)))

/-! ## Commutator bookkeeping -/

theorem commutatorWord_eq_one_of_commute {G : Type*} [Group G] {g h : G}
    (hc : Commute g h) : commutatorWord g h = 1 := by
  rw [commutatorWord, hc.eq]
  group

theorem substHom_commutatorWord (a b : FreeGroup Generator) :
    substHom (commutatorWord a b) =
      commutatorWord (substHom a) (substHom b) := by
  simp [commutatorWord]

/-! ## The relations available in the eliminated presentation -/

abbrev qv1 : TietzeGroup := tietzeWord sv1
abbrev qx : TietzeGroup := tietzeWord sx
abbrev qt : TietzeGroup := tietzeWord st
abbrev qc : TietzeGroup := tietzeWord sc

/-- The image of the marked word in the eliminated presentation. -/
abbrev qmark : TietzeGroup := tietzeWord (substHom markedWord)

theorem qx_cube : qx ^ 3 = 1 := by
  have h := tietzeWord_substHom_retained
    (embed_mem_retained (r := baseRelXCube) (by decide))
  rwa [substHom_embedBaseWord, baseRelXCube, map_pow,
    FreeGroup.lift_apply_of, substBase_x, map_pow] at h

theorem qt_conj_qv1 : qt * qv1 * qt⁻¹ = qv1 ^ 2 := by
  have h := tietzeWord_substHom_retained
    (stable_mem_retained mem_retainedIndices_v1)
  have hs : substHom (stableRelator v1Index) = st * sv1 * st⁻¹ * (sv1 ^ 2)⁻¹ := by
    rw [stableRelator, compressedGeneratorWord, compressedBaseWord]
    simp [substHom_embedBaseWord]
  rw [hs] at h
  simp only [map_mul, map_inv, map_pow] at h
  exact mul_inv_eq_one.mp h

theorem qt_conj_qx : qt * qx * qt⁻¹ = qx := by
  have h := tietzeWord_substHom_retained
    (stable_mem_retained mem_retainedIndices_x)
  have hs : substHom (stableRelator xIndex) = st * sx * st⁻¹ * sx⁻¹ := by
    have hc : compressedGeneratorWord xIndex = vertexLetter xIndex := rfl
    rw [stableRelator, hc]
    simp
  rw [hs] at h
  simp only [map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

theorem commute_of_commutatorWord_eq_one {G : Type*} [Group G] {g h : G}
    (hc : commutatorWord g h = 1) : Commute g h :=
  mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)

theorem map_commutatorWord' {G H : Type*} [Group G] [Group H] (f : G →* H)
    (a b : G) : f (commutatorWord a b) = commutatorWord (f a) (f b) := by
  simp [commutatorWord]

theorem qc_commute_qv1 : Commute qc qv1 := by
  have h := tietzeWord_substHom_retained
    (lampComm_mem_retained mem_retainedIndices_v1)
  rw [substHom_commutatorWord, map_commutatorWord'] at h
  simp only [substHom_of, subst_lamp, subst_base, substBase_v1] at h
  exact commute_of_commutatorWord_eq_one h

theorem qc_commute_qx : Commute qc qx := by
  have h := tietzeWord_substHom_retained
    (lampComm_mem_retained mem_retainedIndices_x)
  rw [substHom_commutatorWord, map_commutatorWord'] at h
  simp only [substHom_of, subst_lamp, subst_base, substBase_x] at h
  exact commute_of_commutatorWord_eq_one h

theorem qmark_commute_qv1 : Commute qmark qv1 := by
  have h := tietzeWord_substHom_retained
    (markedComm_mem_retained mem_retainedLetters_v1)
  rw [substHom_commutatorWord, map_commutatorWord'] at h
  simp only [substHom_of, subst_base, substBase_v1] at h
  exact commute_of_commutatorWord_eq_one h

theorem qmark_commute_qx : Commute qmark qx := by
  have h := tietzeWord_substHom_retained
    (markedComm_mem_retained mem_retainedLetters_x)
  rw [substHom_commutatorWord, map_commutatorWord'] at h
  simp only [substHom_of, subst_base, substBase_x] at h
  exact commute_of_commutatorWord_eq_one h

theorem baseIndex_cases :
    ∀ i : BaseGenerator, i ≠ v2Index → i ≠ v3Index →
      i = v1Index ∨ i = xIndex ∨ i = yIndex ∨ i = zIndex := by
  decide

theorem letter_cases :
    ∀ g : Generator, g ≠ Generator.base v2Index → g ≠ Generator.base v3Index →
      g = Generator.base v1Index ∨ g = Generator.base xIndex ∨
        g = Generator.base yIndex ∨ g = Generator.base zIndex ∨
        g = Generator.stable ∨ g = Generator.lamp := by
  decide

theorem mem_retainedIndices_of_ne (i : BaseGenerator) (h2 : i ≠ v2Index)
    (h3 : i ≠ v3Index) : i ∈ retainedIndices := by
  rcases baseIndex_cases i h2 h3 with rfl | rfl | rfl | rfl
  exacts [mem_retainedIndices_v1, mem_retainedIndices_x,
    mem_retainedIndices_y, mem_retainedIndices_z]

theorem mem_retainedLetters_of_ne (g : Generator)
    (h2 : g ≠ Generator.base v2Index) (h3 : g ≠ Generator.base v3Index) :
    g ∈ retainedLetters := by
  rcases letter_cases g h2 h3 with rfl | rfl | rfl | rfl | rfl | rfl
  exacts [mem_retainedLetters_v1, mem_retainedLetters_x,
    mem_retainedLetters_y, mem_retainedLetters_z,
    mem_retainedLetters_stable, mem_retainedLetters_lamp]

/-! ## The eliminated letters behave -/

/-- The substituted image of `v₃`. -/
abbrev qv3 : TietzeGroup := qx * qv1 * qx⁻¹

/-- The substituted image of `v₂`. -/
abbrev qv2 : TietzeGroup := qx * (qx * qv1 * qx⁻¹) * qx⁻¹

theorem qt_conj_qv3 : qt * qv3 * qt⁻¹ = qv3 ^ 2 := by
  calc qt * (qx * qv1 * qx⁻¹) * qt⁻¹
      = (qt * qx * qt⁻¹) * (qt * qv1 * qt⁻¹) * (qt * qx * qt⁻¹)⁻¹ := by group
    _ = qx * qv1 ^ 2 * qx⁻¹ := by rw [qt_conj_qx, qt_conj_qv1]
    _ = (qx * qv1 * qx⁻¹) * (qx * qv1 * qx⁻¹) := by rw [pow_two qv1]; group
    _ = (qx * qv1 * qx⁻¹) ^ 2 := (pow_two _).symm

theorem qt_conj_qv2 : qt * qv2 * qt⁻¹ = qv2 ^ 2 := by
  calc qt * (qx * (qx * qv1 * qx⁻¹) * qx⁻¹) * qt⁻¹
      = (qt * qx * qt⁻¹) * ((qt * qx * qt⁻¹) * (qt * qv1 * qt⁻¹) *
          (qt * qx * qt⁻¹)⁻¹) * (qt * qx * qt⁻¹)⁻¹ := by group
    _ = qx * (qx * qv1 ^ 2 * qx⁻¹) * qx⁻¹ := by rw [qt_conj_qx, qt_conj_qv1]
    _ = (qx * (qx * qv1 * qx⁻¹) * qx⁻¹) *
        (qx * (qx * qv1 * qx⁻¹) * qx⁻¹) := by rw [pow_two qv1]; group
    _ = (qx * (qx * qv1 * qx⁻¹) * qx⁻¹) ^ 2 := (pow_two _).symm

theorem qc_commute_qv3 : Commute qc qv3 :=
  (qc_commute_qx.mul_right qc_commute_qv1).mul_right qc_commute_qx.inv_right

theorem qc_commute_qv2 : Commute qc qv2 :=
  (qc_commute_qx.mul_right qc_commute_qv3).mul_right qc_commute_qx.inv_right

theorem qmark_commute_qv3 : Commute qmark qv3 :=
  (qmark_commute_qx.mul_right qmark_commute_qv1).mul_right
    qmark_commute_qx.inv_right

theorem qmark_commute_qv2 : Commute qmark qv2 :=
  (qmark_commute_qx.mul_right qmark_commute_qv3).mul_right
    qmark_commute_qx.inv_right

/-- Structural search for membership in a list literal.  Never decides
equality of free-group words: that unfolds the quotient and exhausts the
whnf budget. -/
syntax "mem_list_search" : tactic
macro_rules
  | `(tactic| mem_list_search) =>
      `(tactic| refine List.Mem.tail _ ?_; mem_list_search)
macro_rules
  | `(tactic| mem_list_search) => `(tactic| exact List.Mem.head _)

/-- Discharge one of the seventeen retained base-relator cases. -/
syntax "retainedBase" : tactic
macro_rules
  | `(tactic| retainedBase) =>
      `(tactic| exact tietzeWord_substHom_retained
          (embed_mem_retained (by mem_list_search)))

/-! ## Every original relator dies after substitution -/

theorem tietzeWord_substHom_relator {r : FreeGroup Generator}
    (hr : r ∈ relators) : tietzeWord (substHom r) = 1 := by
  simp only [relators, Finset.mem_union] at hr
  rcases hr with ((hbase | hstable) | hlamp) | hmarked
  · obtain ⟨r₀, hr₀, rfl⟩ := Finset.mem_image.mp hbase
    rw [mem_baseRelators_iff] at hr₀
    rcases hr₀ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · -- `x v₁ x⁻¹ v₃⁻¹`: trivial in the free group after substitution
      have hw : substHom (embedBaseWord baseRelXV1) = 1 := by
        rw [substHom_embedBaseWord]
        simp only [baseRelXV1, map_mul, map_inv, FreeGroup.lift_apply_of,
          substBase_x, substBase_v1, substBase_v3]
        group
      rw [hw, map_one]
    · -- `x v₂ x⁻¹ v₁⁻¹`: this is the one needing `x³ = 1`
      have hw : substHom (embedBaseWord baseRelXV2) =
          sx * sx * sx * sv1 * (sx * sx * sx)⁻¹ * sv1⁻¹ := by
        rw [substHom_embedBaseWord]
        simp only [baseRelXV2, map_mul, map_inv, FreeGroup.lift_apply_of,
          substBase_x, substBase_v1, substBase_v2]
        group
      have h3 : qx * qx * qx = 1 := by
        have h := qx_cube
        rwa [pow_succ, pow_succ, pow_one] at h
      rw [hw]
      simp only [map_mul, map_inv, h3]
      group
    · -- `x v₃ x⁻¹ v₂⁻¹`: trivial in the free group after substitution
      have hw : substHom (embedBaseWord baseRelXV3) = 1 := by
        rw [substHom_embedBaseWord]
        simp only [baseRelXV3, map_mul, map_inv, FreeGroup.lift_apply_of,
          substBase_x, substBase_v2, substBase_v3]
        group
      rw [hw, map_one]
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
    · retainedBase
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hstable
    by_cases h2 : i = v2Index
    · subst h2
      have hw : substHom (stableRelator v2Index) =
          st * (sx * (sx * sv1 * sx⁻¹) * sx⁻¹) * st⁻¹ *
            ((sx * (sx * sv1 * sx⁻¹) * sx⁻¹) ^ 2)⁻¹ := by
        have hc : compressedGeneratorWord v2Index = embedBaseWord (bv2 ^ 2) := rfl
        rw [stableRelator, hc]
        simp [substHom_embedBaseWord]
      rw [hw]
      simp only [map_mul, map_inv, map_pow]
      rw [mul_inv_eq_one]
      exact qt_conj_qv2
    · by_cases h3 : i = v3Index
      · subst h3
        have hw : substHom (stableRelator v3Index) =
            st * (sx * sv1 * sx⁻¹) * st⁻¹ * ((sx * sv1 * sx⁻¹) ^ 2)⁻¹ := by
          have hc : compressedGeneratorWord v3Index = embedBaseWord (bv3 ^ 2) := rfl
          rw [stableRelator, hc]
          simp [substHom_embedBaseWord]
        rw [hw]
        simp only [map_mul, map_inv, map_pow]
        rw [mul_inv_eq_one]
        exact qt_conj_qv3
      · exact tietzeWord_substHom_retained
          (stable_mem_retained (mem_retainedIndices_of_ne i h2 h3))
  · rcases Finset.mem_union.mp hlamp with hsq | himg
    · rw [Finset.mem_singleton.mp hsq]
      exact tietzeWord_substHom_retained lampSq_mem_retainedList
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp himg
      by_cases h2 : i = v2Index
      · subst h2
        rw [substHom_commutatorWord, map_commutatorWord']
        simp only [substHom_of, subst_lamp, subst_base, substBase_v2,
          map_mul, map_inv]
        exact commutatorWord_eq_one_of_commute qc_commute_qv2
      · by_cases h3 : i = v3Index
        · subst h3
          rw [substHom_commutatorWord, map_commutatorWord']
          simp only [substHom_of, subst_lamp, subst_base, substBase_v3,
            map_mul, map_inv]
          exact commutatorWord_eq_one_of_commute qc_commute_qv3
        · exact tietzeWord_substHom_retained
            (lampComm_mem_retained (mem_retainedIndices_of_ne i h2 h3))
  · obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hmarked
    by_cases h2 : g = Generator.base v2Index
    · subst h2
      rw [substHom_commutatorWord, map_commutatorWord']
      simp only [substHom_of, subst_base, substBase_v2, map_mul, map_inv]
      exact commutatorWord_eq_one_of_commute qmark_commute_qv2
    · by_cases h3 : g = Generator.base v3Index
      · subst h3
        rw [substHom_commutatorWord, map_commutatorWord']
        simp only [substHom_of, subst_base, substBase_v3, map_mul, map_inv]
        exact commutatorWord_eq_one_of_commute qmark_commute_qv3
      · exact tietzeWord_substHom_retained
          (markedComm_mem_retained (mem_retainedLetters_of_ne g h2 h3))

/-! ## The eliminated letters are the words they were replaced by -/

theorem marked_v3_eq : (v3 : MarkedGroup) = x * v1 * x⁻¹ := by
  have h := congrArg baseMap LiteralBaseRelations.x_conj_v1
  simpa [LiteralBaseRelations.x, LiteralBaseRelations.v1,
    LiteralBaseRelations.v3] using h.symm

theorem marked_v2_eq : (v2 : MarkedGroup) = x * (x * v1 * x⁻¹) * x⁻¹ := by
  have h := congrArg baseMap LiteralBaseRelations.x_conj_v3
  have h2 : (v2 : MarkedGroup) = x * v3 * x⁻¹ := by
    simpa [LiteralBaseRelations.x, LiteralBaseRelations.v2,
      LiteralBaseRelations.v3] using h.symm
  rw [h2, marked_v3_eq]

theorem sixIndex_cases :
    ∀ i : BaseGenerator, i ≠ v1Index → i ≠ v2Index → i ≠ v3Index →
      i ≠ xIndex → i ≠ yIndex → i = zIndex := by
  decide

/-- Substituting and then evaluating the six retained letters is the same
as evaluating the original eight. -/
theorem sixGeneratorHom_substHom (w : FreeGroup Generator) :
    sixGeneratorHom (substHom w) = wordInMarkedGroup w := by
  refine freeGroup_hom_eq_on_generators
    (f := sixGeneratorHom.comp substHom) (g := wordInMarkedGroup) ?_ w
  rintro (i | j)
  · by_cases h1 : i = v1Index
    · subst h1
      simp [sixGenerator]
    · by_cases h2 : i = v2Index
      · subst h2
        simp only [MonoidHom.comp_apply, substHom_of, subst_base,
          substBase_v2, map_mul, map_inv, sixGeneratorHom_of, sixGenerator]
        exact marked_v2_eq.symm
      · by_cases h3 : i = v3Index
        · subst h3
          simp only [MonoidHom.comp_apply, substHom_of, subst_base,
            substBase_v3, map_mul, map_inv, sixGeneratorHom_of, sixGenerator]
          exact marked_v3_eq.symm
        · by_cases h4 : i = xIndex
          · subst h4
            simp [sixGenerator]
          · by_cases h5 : i = yIndex
            · subst h5
              simp [sixGenerator]
            · rw [sixIndex_cases i h1 h2 h3 h4 h5]
              simp [sixGenerator]
  · by_cases hj : j = 0
    · subst hj
      simp [sixGenerator, subst]
    · have : j = 1 := by omega
      subst this
      simp [sixGenerator, subst]

/-! ## The retained relators are original relators -/

theorem retainedBase_subset {r : FreeGroup BaseGenerator}
    (hr : r ∈ retainedBaseList) : r ∈ baseRelators := by
  rw [mem_baseRelators_iff]
  simp only [retainedBaseList, List.mem_cons, List.not_mem_nil, or_false] at hr
  tauto

theorem retained_subset_relators {r : FreeGroup Generator}
    (hr : r ∈ retainedList) : r ∈ relators := by
  simp only [retainedList, List.mem_append, List.mem_map, List.mem_cons] at hr
  simp only [relators, Finset.mem_union]
  rcases hr with ⟨r₀, hr₀, rfl⟩ | ⟨i, hi, rfl⟩ | (rfl | ⟨i, -, rfl⟩) |
    ⟨g, -, rfl⟩
  · exact Or.inl (Or.inl (Or.inl
      (Finset.mem_image_of_mem _ (retainedBase_subset hr₀))))
  · exact Or.inl (Or.inl (Or.inr
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  · exact Or.inl (Or.inr (Finset.mem_union_left _
      (Finset.mem_singleton_self _)))
  · exact Or.inl (Or.inr (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))))
  · exact Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ g))

/-! ## The two homomorphisms -/

/-- The eliminated presentation maps onto the original group. -/
def toMarked : TietzeGroup →* MarkedGroup := by
  apply PresentedGroup.toGroup (f := sixGenerator)
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
  change sixGeneratorHom (substHom r₀) = 1
  rw [sixGeneratorHom_substHom]
  exact PresentedGroup.one_of_mem
    (Finset.mem_coe.mpr (retained_subset_relators hr₀))

/-- The original group maps onto the eliminated presentation. -/
def toTietze : MarkedGroup →* TietzeGroup := by
  apply PresentedGroup.toGroup (f := fun g : Generator ↦ tietzeWord (subst g))
  intro r hr
  have hlift : FreeGroup.lift (fun g : Generator ↦ tietzeWord (subst g)) r =
      tietzeWord (substHom r) := by
    refine freeGroup_hom_eq_on_generators
      (f := FreeGroup.lift fun g : Generator ↦ tietzeWord (subst g))
      (g := tietzeWord.comp substHom) ?_ r
    intro g
    simp
  rw [hlift]
  exact tietzeWord_substHom_relator (Finset.mem_coe.mp hr)

theorem toMarked_tietzeWord (w : FreeGroup SixGenerator) :
    toMarked (tietzeWord w) = sixGeneratorHom w :=
  presentedToGroup_mk _ w

theorem toTietze_wordInMarkedGroup (w : FreeGroup Generator) :
    toTietze (wordInMarkedGroup w) = tietzeWord (substHom w) := by
  rw [toTietze, presentedToGroup_mk]
  refine freeGroup_hom_eq_on_generators
    (f := FreeGroup.lift fun g : Generator ↦ tietzeWord (subst g))
    (g := tietzeWord.comp substHom) ?_ w
  intro g
  simp

/-! ## The elimination is an isomorphism -/

theorem toMarked_comp_toTietze :
    toMarked.comp toTietze = MonoidHom.id MarkedGroup := by
  refine PresentedGroup.ext ?_
  intro g
  rw [MonoidHom.comp_apply, MonoidHom.id_apply]
  show toMarked (toTietze (wordInMarkedGroup (FreeGroup.of g))) = _
  rw [toTietze_wordInMarkedGroup, toMarked_tietzeWord,
    sixGeneratorHom_substHom]
  rfl

theorem toTietze_comp_toMarked :
    toTietze.comp toMarked = MonoidHom.id TietzeGroup := by
  refine PresentedGroup.ext ?_
  intro i
  rw [MonoidHom.comp_apply, MonoidHom.id_apply]
  show toTietze (toMarked (tietzeWord (FreeGroup.of i))) = _
  rw [toMarked_tietzeWord, sixGeneratorHom_of]
  fin_cases i <;>
    · show toTietze (wordInMarkedGroup _) = _
      rw [toTietze_wordInMarkedGroup]
      rfl

/-- **The Tietze elimination.**  The literal eight-generator,
forty-one-relator group is isomorphic to the six-generator group on the
thirty-two retained relators. -/
def markedEquivTietze : MarkedGroup ≃* TietzeGroup where
  toFun := toTietze
  invFun := toMarked
  left_inv g := by
    have := congrArg (fun f : MarkedGroup →* MarkedGroup ↦ f g)
      toMarked_comp_toTietze
    simpa using this
  right_inv q := by
    have := congrArg (fun f : TietzeGroup →* TietzeGroup ↦ f q)
      toTietze_comp_toMarked
    simpa using this
  map_mul' := map_mul toTietze

/-! ## The relator count -/

/-- The elimination isomorphism sends each of the six letters to the
generator it names. -/
theorem markedEquivTietze_symm_of (i : SixGenerator) :
    markedEquivTietze.symm (PresentedGroup.of i) = sixGenerator i := by
  show toMarked (tietzeWord (FreeGroup.of i)) = sixGenerator i
  rw [toMarked_tietzeWord, sixGeneratorHom_of]

/-- **Six generators, thirty-two relators.**  The literal group `E` of the
manuscript is presented by a list of exactly thirty-two relators on the
six letters `v₁,x,y,z,t,c` --- and the isomorphism carries each letter to
the generator it names, which is what makes them *these* six generators
rather than merely six of them.

Presenting over a list rather than a finite set is what makes the count
exact: a `Finset` would identify any two relators that happened to
coincide as words, and that is a question about free-group words this
development deliberately never decides. -/
theorem exists_sixGenerator_thirtyTwo_presentation :
    ∃ L : List (FreeGroup SixGenerator), L.length = 32 ∧
      ∃ e : PresentedGroup {r | r ∈ L} ≃* MarkedGroup,
        ∀ i : SixGenerator, e (PresentedGroup.of i) = sixGenerator i :=
  ⟨tietzeRelatorList, tietzeRelatorList_length,
    markedEquivTietze.symm, markedEquivTietze_symm_of⟩

end

end LiteralTietzePresentation
end GroupApproximation
