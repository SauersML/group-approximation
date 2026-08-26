import GroupApproximation.Sofic.LiteralAffineFreeProductAvatarBlueprint
import GroupApproximation.Sofic.AvatarRouterInstance

/-!
# Marked positive padding for the literal affine free-product avatar

This file isolates a presentation-theoretic padding experiment for
`LiteralAffineFreeProductAvatarBlueprint.blueprint`.

The useful padding operation is not `WordPresentation.pad`: its defining word
contains negative letters.  Instead, for a positive presentation `P`, adjoin a
fresh generator `z`, send it to `1`, and replace every (nonempty) relator `r`
by the consecutive positive Nielsen pair

    z r^d,   z r^(d+1).

The pair normally generates `z` and `r`, so the operation is a Tietze move.
Both new relators have length at least `d+1`, and `z` occurs literally once in
each.  The latter is the occurrence-level datum from which the avatar
`leadCode` mark is to be read; importantly, it is proved here before avatar
substitution, rather than postulated as a private-generator field.

The construction is a valid positive Tietze move and its floor and occurrence
statements are useful independently.  It is **not** a viable small-cancellation
router: the two consecutive Nielsen relators are nested.  The companion module
`LiteralAffineFreeProductAvatarChecks` proves that their shorter expanded word
is itself a piece, and hence that `ConcreteRemainingRouterChecks d` is empty
for every `d`.  The residual structure below is retained to state that no-go
against the exact downstream interface, not to suggest its fields can be
filled.
-/

namespace GroupApproximation
namespace LiteralAffineFreeProductPaddedAvatarBlueprint

open BespokeRouter.AvatarWordFamily

noncomputable section

namespace PositiveMarkedPadding

variable {G : Type} [Group G]

/-- The fresh positive marker in the alphabet obtained by adjoining one
generator. -/
def marker (P : WordPresentation G) : List (Fin (P.card + 1) × Bool) :=
  [((Fin.last P.card), true)]

/-- One member of the consecutive Nielsen pair `z r^d, z r^(d+1)`. -/
def codedRelator (P : WordPresentation G) (d : ℕ)
    (r : List (Fin P.card × Bool)) : List (Fin (P.card + 1) × Bool) :=
  rightRelatorCode (marker P) (padList r) d

/-- The two coded copies of every old relator. -/
def rel (P : WordPresentation G) (d : ℕ) :
    Set (List (Fin (P.card + 1) × Bool)) :=
  codedRelator P d '' P.rel ∪ codedRelator P (d + 1) '' P.rel

theorem rel_finite (P : WordPresentation G) (d : ℕ) : (rel P d).Finite :=
  (P.rel_finite.image _).union (P.rel_finite.image _)

/-- Exact coded length. -/
theorem length_codedRelator (P : WordPresentation G) (d : ℕ)
    (r : List (Fin P.card × Bool)) :
    (codedRelator P d r).length = 1 + d * r.length := by
  rw [codedRelator, length_rightRelatorCode]
  simp [marker, length_padList]

/-- Consecutive Nielsen relators are nested.  This identity is harmless for
Tietze equivalence but fatal for metric small cancellation; the companion
checks module records the resulting no-go. -/
theorem codedRelator_succ (P : WordPresentation G) (d : ℕ)
    (r : List (Fin P.card × Bool)) :
    codedRelator P (d + 1) r = codedRelator P d r ++ padList r := by
  unfold codedRelator rightRelatorCode
  rw [List.replicate_succ', List.flatten_append, List.flatten_cons,
    List.flatten_nil]
  simp

/-- Nonempty old relators give the advertised uniform floor. -/
theorem floor_le_length_codedRelator (P : WordPresentation G) (d : ℕ)
    {r : List (Fin P.card × Bool)} (hr : r ≠ []) :
    d + 1 ≤ (codedRelator P d r).length := by
  rw [length_codedRelator]
  have hlen : 1 ≤ r.length := List.length_pos_iff.mpr hr
  have := Nat.mul_le_mul_left d hlen
  omega

/-- Every letter is positive when the old relator is positive. -/
theorem codedRelator_positive (P : WordPresentation G) (d : ℕ)
    {r : List (Fin P.card × Bool)}
    (hr : ∀ c ∈ r, c.2 = true) :
    ∀ c ∈ codedRelator P d r, c.2 = true := by
  apply rightRelatorCode_positive
  · simp [marker]
  · intro c hc
    simp only [padList, List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact hr x hx

/-- The fresh marker is absent from every lifted old word. -/
theorem last_not_mem_padList (P : WordPresentation G)
    (r : List (Fin P.card × Bool)) :
    ∀ c ∈ padList r, c.1 ≠ Fin.last P.card := by
  intro c hc
  simp only [padList, List.mem_map] at hc
  obtain ⟨x, -, rfl⟩ := hc
  exact Fin.castSucc_ne_last x.1

/-- The padding marker occurs at the head and nowhere in the repeated tail.
This is the exact source-word fact needed by the later `leadCode` bridge. -/
theorem marker_unique (P : WordPresentation G) (d : ℕ)
    (r : List (Fin P.card × Bool)) :
    ∀ c ∈ (codedRelator P d r).tail,
      c.1 ≠ Fin.last P.card := by
  intro c hc
  have hc' : c ∈ (List.replicate d (padList r)).flatten := by
    simpa [codedRelator, rightRelatorCode, marker] using hc
  rw [List.mem_flatten] at hc'
  obtain ⟨w, hw, hcw⟩ := hc'
  have hw' : w = padList r := List.eq_of_mem_replicate hw
  exact last_not_mem_padList P r c (hw' ▸ hcw)

/-- The presentation-level assumptions used by marked positive padding.
They hold for the empty-relator-normalized positive presentations in the
literal affine blueprint. -/
structure Admissible (P : WordPresentation G) : Prop where
  positive : ∀ r ∈ P.rel, ∀ c ∈ r, c.2 = true
  nonempty : ∀ r ∈ P.rel, r ≠ []
  inhabited : P.rel.Nonempty

/-- The coded pair for one old relator is contained in the whole coded family. -/
theorem pair_wordSubgroup_le (P : WordPresentation G) (d : ℕ)
    {r : List (Fin P.card × Bool)} (hr : r ∈ P.rel) :
    wordSubgroup
        ({codedRelator P d r, codedRelator P (d + 1) r} :
          Set (List (Fin (P.card + 1) × Bool))) ≤
      wordSubgroup (rel P d) := by
  refine Subgroup.normalClosure_le_normal ?_
  rintro _ ⟨w, hw, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · exact mem_wordSubgroup (Set.mem_union_left _ ⟨r, hr, rfl⟩)
  · exact mem_wordSubgroup (Set.mem_union_right _ ⟨r, hr, rfl⟩)

/-- The new family recovers both the fresh marker and each lifted old relator. -/
theorem marker_mem_and_padList_mem (P : WordPresentation G) (d : ℕ)
    {r : List (Fin P.card × Bool)} (hr : r ∈ P.rel) :
    FreeGroup.mk (marker P) ∈ wordSubgroup (rel P d) ∧
      FreeGroup.mk (padList r) ∈ wordSubgroup (rel P d) := by
  have heq := wordSubgroup_pair_rightRelatorCode
    (marker P) (padList r) d
  have hle := pair_wordSubgroup_le P d hr
  constructor
  · apply hle
    change FreeGroup.mk (marker P) ∈ wordSubgroup
      ({rightRelatorCode (marker P) (padList r) d,
        rightRelatorCode (marker P) (padList r) (d + 1)} : Set _)
    rw [heq]
    exact mem_wordSubgroup (by simp)
  · apply hle
    change FreeGroup.mk (padList r) ∈ wordSubgroup
      ({rightRelatorCode (marker P) (padList r) d,
        rightRelatorCode (marker P) (padList r) (d + 1)} : Set _)
    rw [heq]
    exact mem_wordSubgroup (by simp)

/-- Kernel preservation, reduced to the already-proved one-generator Tietze
padding with empty defining word. -/
theorem ker_le (P : WordPresentation G) (d : ℕ) (hP : Admissible P) :
    ((P.pad []).hom).ker ≤ wordSubgroup (rel P d) := by
  obtain ⟨a, ha⟩ := hP.inhabited
  have hmarker : FreeGroup.mk (marker P) ∈ wordSubgroup (rel P d) :=
    (marker_mem_and_padList_mem P d ha).1
  have hold : ∀ r ∈ P.rel,
      FreeGroup.mk (padList r) ∈ wordSubgroup (rel P d) :=
    fun r hr ↦ (marker_mem_and_padList_mem P d hr).2
  letI : (wordSubgroup (rel P d)).Normal := wordSubgroup_normal (rel P d)
  have hpad : wordSubgroup (P.padRel []) ≤ wordSubgroup (rel P d) := by
    refine Subgroup.normalClosure_le_normal (N := wordSubgroup (rel P d)) ?_
    rintro _ ⟨w, hw, rfl⟩
    change w ∈ padRelator [] '' P.rel ∪ {padDefiner []} at hw
    rcases hw with ⟨r, hr, rfl⟩ | rfl
    · rw [mk_padRelator]
      exact mul_mem (hold r hr) hmarker
    · simpa [marker, padDefiner, padList] using hmarker
  intro x hx
  have hx' := (P.pad []).ker_le hx
  change x ∈ wordSubgroup (P.padRel []) at hx'
  exact hpad hx'

/-- Positive marked padding as a genuine word presentation. -/
def presentation (P : WordPresentation G) (d : ℕ) (hP : Admissible P) :
    WordPresentation G where
  card := P.card + 1
  hom := (P.pad []).hom
  hom_surjective := (P.pad []).hom_surjective
  rel := rel P d
  rel_finite := rel_finite P d
  ker_le := ker_le P d hP

theorem presentation_rel_positive (P : WordPresentation G) (d : ℕ)
    (hP : Admissible P) :
    ∀ r ∈ (presentation P d hP).rel, ∀ c ∈ r, c.2 = true := by
  intro r hr
  change r ∈ rel P d at hr
  change r ∈ codedRelator P d '' P.rel ∪
    codedRelator P (d + 1) '' P.rel at hr
  rcases hr with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · exact codedRelator_positive P d (hP.positive r hr)
  · exact codedRelator_positive P (d + 1) (hP.positive r hr)

theorem presentation_rel_floor (P : WordPresentation G) (d : ℕ)
    (hP : Admissible P) :
    ∀ r ∈ (presentation P d hP).rel, d + 1 ≤ r.length := by
  intro r hr
  change r ∈ rel P d at hr
  change r ∈ codedRelator P d '' P.rel ∪
    codedRelator P (d + 1) '' P.rel at hr
  rcases hr with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
  · exact floor_le_length_codedRelator P d (hP.nonempty r hr)
  · have h := floor_le_length_codedRelator P (d + 1) (hP.nonempty r hr)
    exact Nat.le_trans (by omega) h

/-- A long positive spelling of an old word.  The marker occurs once, while
the chosen old null relator supplies arbitrary length. -/
def markedName (P : WordPresentation G) (a : List (Fin P.card × Bool))
    (d : ℕ) (w : List (Fin P.card × Bool)) :
    List (Fin (P.card + 1) × Bool) :=
  marker P ++ (List.replicate d (padList a)).flatten ++ padList w

theorem length_markedName (P : WordPresentation G)
    (a : List (Fin P.card × Bool)) (d : ℕ)
    (w : List (Fin P.card × Bool)) :
    (markedName P a d w).length = 1 + d * a.length + w.length := by
  simp [markedName, marker, length_padList]
  omega

theorem depth_le_length_markedName (P : WordPresentation G)
    {a : List (Fin P.card × Bool)} (ha : a ≠ []) (d : ℕ)
    (w : List (Fin P.card × Bool)) :
    d + 1 ≤ (markedName P a d w).length := by
  rw [length_markedName]
  have hlen : 1 ≤ a.length := List.length_pos_iff.mpr ha
  have := Nat.mul_le_mul_left d hlen
  omega

theorem markedName_positive (P : WordPresentation G)
    {a w : List (Fin P.card × Bool)}
    (ha : ∀ c ∈ a, c.2 = true) (hw : ∀ c ∈ w, c.2 = true)
    (d : ℕ) : ∀ c ∈ markedName P a d w, c.2 = true := by
  have hpa : ∀ c ∈ padList a, c.2 = true := by
    intro c hc
    simp only [padList, List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact ha x hx
  have hpw : ∀ c ∈ padList w, c.2 = true := by
    intro c hc
    simp only [padList, List.mem_map] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact hw x hx
  have hflat : ∀ c ∈ (List.replicate d (padList a)).flatten,
      c.2 = true := by
    apply AvatarMetricCheck.forall_positive_flatten
    intro u hu
    have hu' : u = padList a := List.eq_of_mem_replicate hu
    simpa [hu'] using hpa
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · rcases List.mem_append.mp hc with hc | hc
    · have hc' : c = (Fin.last P.card, true) := by simpa [marker] using hc
      rw [hc']
    · exact hflat c hc
  · exact hpw c hc

/-- The fresh generator occurs only at the head of a padded name as well. -/
theorem markedName_marker_unique (P : WordPresentation G)
    (a : List (Fin P.card × Bool)) (d : ℕ)
    (w : List (Fin P.card × Bool)) :
    ∀ c ∈ (markedName P a d w).tail,
      c.1 ≠ Fin.last P.card := by
  intro c hc
  have hc' : c ∈ (List.replicate d (padList a)).flatten ∨ c ∈ padList w := by
    simpa [markedName, marker] using hc
  rcases hc' with hc' | hc'
  · rw [List.mem_flatten] at hc'
    obtain ⟨u, hu, hcu⟩ := hc'
    have hu' : u = padList a := List.eq_of_mem_replicate hu
    exact last_not_mem_padList P a c (hu' ▸ hcu)
  · exact last_not_mem_padList P w c hc'

/-- A marked name still spells the old element. -/
theorem presentation_hom_markedName (P : WordPresentation G) (d : ℕ)
    (hP : Admissible P) {a w : List (Fin P.card × Bool)}
    (ha : P.hom (FreeGroup.mk a) = 1) :
    (presentation P d hP).hom (FreeGroup.mk (markedName P a d w)) =
      P.hom (FreeGroup.mk w) := by
  have hm : (P.hom.comp (padRetract [])) (FreeGroup.mk (marker P)) = 1 := by
    change P.hom (padRetract [] (FreeGroup.of (Fin.last P.card))) = 1
    rw [padRetract_of_last, ← FreeGroup.one_eq_mk, map_one]
  have ha' : (P.hom.comp (padRetract [])) (FreeGroup.mk (padList a)) =
      P.hom (FreeGroup.mk a) := by
    exact P.pad_hom_padList ([] : List (Fin P.card × Bool)) a
  have hw' : (P.hom.comp (padRetract [])) (FreeGroup.mk (padList w)) =
      P.hom (FreeGroup.mk w) := by
    exact P.pad_hom_padList ([] : List (Fin P.card × Bool)) w
  unfold presentation
  change (P.hom.comp (padRetract []))
    (FreeGroup.mk (markedName P a d w)) = _
  unfold markedName
  rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul,
    PeriodicOverlap.mk_flatten_replicate, map_pow, hm, one_mul, ha', ha,
    one_pow, one_mul, hw']

/-- A nontrivial target forces every surjective word presentation to have at
least one generator. -/
private theorem freeGroup_subsingleton {A : Type} [IsEmpty A] :
    Subsingleton (FreeGroup A) := by
  constructor
  intro x y
  have hone : ∀ z : FreeGroup A, z = 1 := by
    intro z
    refine FreeGroup.induction_on z rfl
      (fun i ↦ (IsEmpty.false i).elim)
      (fun i _ ↦ (IsEmpty.false i).elim)
      (fun a b ha hb ↦ by rw [ha, hb, one_mul])
  rw [hone x, hone y]

theorem card_pos_of_ne_one (P : WordPresentation G) {g : G} (hg : g ≠ 1) :
    0 < P.card := by
  by_contra h
  have hc : P.card = 0 := Nat.eq_zero_of_not_pos h
  letI : IsEmpty (Fin P.card) :=
    ⟨fun i ↦ by have hi := i.isLt; omega⟩
  haveI : Subsingleton (FreeGroup (Fin P.card)) :=
    freeGroup_subsingleton
  obtain ⟨x, hx⟩ := P.hom_surjective g
  apply hg
  rw [← hx]
  have hxone : x = 1 := Subsingleton.elim _ _
  rw [hxone, map_one]

/-- Removing empty relators from the canonical positive presentation leaves a
nonempty positive family as soon as the original presentation has a generator.
The barred-pair word supplies an explicit nontrivial kernel element. -/
theorem normalizedPositive_admissible (P : WordPresentation G)
    [Group.IsFinitelyPresented G] (hcard : 0 < P.card) :
    Admissible
      (LiteralAffineFreeProductAvatarBlueprint.withoutEmptyRelators
        (PositivePresentation.presentation P)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact PositivePresentation.presentation_rel_positive P r hr.1
  · intro r hr
    exact hr.2
  · let i : Fin P.card := ⟨0, hcard⟩
    let x : FreeGroup (Fin (P.card + P.card)) :=
      FreeGroup.mk (PositivePresentation.pairWord P i)
    have hxker : x ∈
        (LiteralAffineFreeProductAvatarBlueprint.withoutEmptyRelators
          (PositivePresentation.presentation P)).hom.ker := by
      apply MonoidHom.mem_ker.mpr
      exact (PositivePresentation.pairWord_mem P i).2
    have hxne : x ≠ 1 := by
      intro hx
      have hpos := (PositivePresentation.pairWord_mem P i).1
      have hword := AvatarMetricCheck.toWord_mk_of_forall_positive hpos
      have hnorm : FreeGroup.norm x = 2 := by
        change x.toWord.length = 2
        rw [hword]
        simp [PositivePresentation.pairWord]
      rw [hx, FreeGroup.norm_one] at hnorm
      omega
    by_contra hrel
    have hrel' :
        (LiteralAffineFreeProductAvatarBlueprint.withoutEmptyRelators
          (PositivePresentation.presentation P)).rel = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hrel
    have hxmem :=
      (LiteralAffineFreeProductAvatarBlueprint.withoutEmptyRelators
        (PositivePresentation.presentation P)).ker_le hxker
    rw [hrel'] at hxmem
    change x ∈ wordSubgroup
      (∅ : Set (List (Fin (P.card + P.card) × Bool))) at hxmem
    have hxone : x = 1 := by
      simpa [wordSubgroup] using hxmem
    exact hxne hxone

/-- Exact unresolved router-level work after the padding construction.  Floor
fields are intentionally absent: they are supplied by
`presentation_rel_floor` and `depth_le_length_markedName`. -/
structure RemainingRouterChecks
    {E : Type} [Group E] {N : Subgroup E} {s : E}
    {B : Type} [Group B] (D : Blueprint E N s B) (wordFloor : ℕ) where
  sharedBound : ℕ
  runCeil : ℕ
  /-- Turn the literal once-occurring fresh presentation marker into the
  unique `leadCode` position on every expanded router relator. -/
  occurrenceMarks : D.OccurrenceMarks
  /-- The genuine small-cancellation content, not a padding theorem. -/
  piece_short : ∀ p : List (Fin 2 × Bool),
    SmallCancellationRouter.IsPiece
        (SmallCancellationRouter.symmetrization D.relators) p →
      p.length < sharedBound * D.avatarLength + 2 * runCeil + 2
  flank_small : 8 * (2 * runCeil + 2) ≤ D.avatarLength
  floor_ge : 8 * sharedBound + 1 ≤ wordFloor
  protectedLength : ℕ
  protected_norm :
    FreeGroup.norm (FreeGroup.lift D.srcAvatar D.protectedWord) ≤ protectedLength
  protected_margin :
    2 * protectedLength ≤ wordFloor * D.avatarLength

end PositiveMarkedPadding

open LiteralAffineFreeProductAvatarBlueprint
open PositiveMarkedPadding

/-- The source positive presentation satisfies the padding side conditions,
without an extra premise. -/
theorem sourcePositive_admissible :
    Admissible sourcePositiveWordPresentation := by
  letI : Group.IsFinitelyPresented LiteralAffineFreeProductSource.Ambient :=
    LiteralAffineFreeProductSource.ambient_isFinitelyPresented
  simpa [sourcePositiveWordPresentation] using
    normalizedPositive_admissible sourceWordPresentation
      (card_pos_of_ne_one sourceWordPresentation
        LiteralAffineFreeProductBassSerre.crossingDefect_ne_one)

/-- The concrete `Gamma(3)` partner is nontrivial. -/
theorem gamma3WitnessElement_ne_one : gamma3WitnessElement ≠ 1 := by
  intro h
  apply CongruenceTorsionFree.gamma3Witness_ne_one
  exact congrArg Subtype.val h

/-- The partner positive presentation satisfies the same conditions. -/
theorem gamma3Positive_admissible :
    Admissible
      (withoutEmptyRelators gamma3PositiveWordPresentation) := by
  simpa [gamma3PositiveWordPresentation] using
    normalizedPositive_admissible gamma3WordPresentation
      (card_pos_of_ne_one gamma3WordPresentation gamma3WitnessElement_ne_one)

/-- The arbitrarily deep, positive, once-marked source presentation. -/
noncomputable def sourcePaddedPresentation (d : ℕ) :
    WordPresentation LiteralAffineFreeProductSource.Ambient :=
  presentation sourcePositiveWordPresentation d sourcePositive_admissible

/-- Every source relator is positive after marked padding. -/
theorem sourcePaddedPresentation_rel_positive (d : ℕ) :
    ∀ r ∈ (sourcePaddedPresentation d).rel, ∀ c ∈ r, c.2 = true :=
  presentation_rel_positive _ d sourcePositive_admissible

/-- Every source relator has the literal floor `d+1`. -/
theorem sourcePaddedPresentation_rel_floor (d : ℕ) :
    ∀ r ∈ (sourcePaddedPresentation d).rel, d + 1 ≤ r.length :=
  presentation_rel_floor _ d sourcePositive_admissible

/-- The arbitrarily deep, positive, once-marked partner presentation. -/
noncomputable def partnerPaddedPresentation (d : ℕ) :
    WordPresentation CongruenceSubgroup.gamma3Partner.B :=
  presentation (withoutEmptyRelators gamma3PositiveWordPresentation) d
    gamma3Positive_admissible

/-- Every partner relator is positive after marked padding. -/
theorem partnerPaddedPresentation_rel_positive (d : ℕ) :
    ∀ r ∈ (partnerPaddedPresentation d).rel, ∀ c ∈ r, c.2 = true :=
  presentation_rel_positive _ d gamma3Positive_admissible

/-- Every partner relator has the same literal floor `d+1`. -/
theorem partnerPaddedPresentation_rel_floor (d : ℕ) :
    ∀ r ∈ (partnerPaddedPresentation d).rel, d + 1 ≤ r.length :=
  presentation_rel_floor _ d gamma3Positive_admissible

/-- A chosen nonempty positive null relator used only to lengthen designated
source names. -/
noncomputable def sourceAnchor :
    List (Fin sourcePositiveWordPresentation.card × Bool) :=
  sourcePositive_admissible.inhabited.choose

theorem sourceAnchor_mem : sourceAnchor ∈ sourcePositiveWordPresentation.rel :=
  sourcePositive_admissible.inhabited.choose_spec

theorem sourceAnchor_ne_nil : sourceAnchor ≠ [] :=
  sourcePositive_admissible.nonempty sourceAnchor sourceAnchor_mem

theorem sourceAnchor_positive : ∀ c ∈ sourceAnchor, c.2 = true :=
  sourcePositive_admissible.positive sourceAnchor sourceAnchor_mem

theorem sourceAnchor_killed :
    sourcePositiveWordPresentation.hom (FreeGroup.mk sourceAnchor) = 1 := by
  letI : Group.IsFinitelyPresented LiteralAffineFreeProductSource.Ambient :=
    LiteralAffineFreeProductSource.ambient_isFinitelyPresented
  exact (PositivePresentation.rel_subset_kernelWords sourceWordPresentation
    sourceAnchor_mem.1).2

/-- A long, once-marked positive source name. -/
noncomputable def sourceMarkedName (d : ℕ)
    (g : LiteralAffineFreeProductSource.Ambient) :
    List (Fin (sourcePaddedPresentation d).card × Bool) :=
  markedName sourcePositiveWordPresentation sourceAnchor d
    (sourcePositiveName g)

theorem sourceMarkedName_positive (d : ℕ)
    (g : LiteralAffineFreeProductSource.Ambient) :
    ∀ c ∈ sourceMarkedName d g, c.2 = true :=
  markedName_positive _ sourceAnchor_positive (sourcePositiveName_positive g) d

theorem sourceMarkedName_spec (d : ℕ)
    (g : LiteralAffineFreeProductSource.Ambient) :
    (sourcePaddedPresentation d).hom (FreeGroup.mk (sourceMarkedName d g)) = g := by
  unfold sourcePaddedPresentation sourceMarkedName
  exact (presentation_hom_markedName _ d sourcePositive_admissible
    sourceAnchor_killed).trans (sourcePositiveName_spec g)

theorem sourceMarkedName_floor (d : ℕ)
    (g : LiteralAffineFreeProductSource.Ambient) :
    d + 1 ≤ (sourceMarkedName d g).length :=
  depth_le_length_markedName _ sourceAnchor_ne_nil d _

theorem sourceMarkedName_marker_unique (d : ℕ)
    (g : LiteralAffineFreeProductSource.Ambient) :
    ∀ c ∈ (sourceMarkedName d g).tail,
      c.1 ≠ Fin.last sourcePositiveWordPresentation.card :=
  markedName_marker_unique _ sourceAnchor d _

/-- The partner-side null relator and its basic facts. -/
noncomputable def partnerAnchor :
    List (Fin (withoutEmptyRelators gamma3PositiveWordPresentation).card × Bool) :=
  gamma3Positive_admissible.inhabited.choose

theorem partnerAnchor_mem :
    partnerAnchor ∈ (withoutEmptyRelators gamma3PositiveWordPresentation).rel :=
  gamma3Positive_admissible.inhabited.choose_spec

theorem partnerAnchor_ne_nil : partnerAnchor ≠ [] :=
  gamma3Positive_admissible.nonempty partnerAnchor partnerAnchor_mem

theorem partnerAnchor_positive : ∀ c ∈ partnerAnchor, c.2 = true :=
  gamma3Positive_admissible.positive partnerAnchor partnerAnchor_mem

theorem partnerAnchor_killed :
    (withoutEmptyRelators gamma3PositiveWordPresentation).hom
      (FreeGroup.mk partnerAnchor) = 1 := by
  exact (PositivePresentation.rel_subset_kernelWords gamma3WordPresentation
    partnerAnchor_mem.1).2

noncomputable def partnerMarkedName (d : ℕ)
    (g : CongruenceSubgroup.gamma3Partner.B) :
    List (Fin (partnerPaddedPresentation d).card × Bool) :=
  markedName (withoutEmptyRelators gamma3PositiveWordPresentation)
    partnerAnchor d (PositivePresentation.name gamma3WordPresentation g)

theorem partnerMarkedName_positive (d : ℕ)
    (g : CongruenceSubgroup.gamma3Partner.B) :
    ∀ c ∈ partnerMarkedName d g, c.2 = true :=
  markedName_positive _ partnerAnchor_positive
    (PositivePresentation.name_positive gamma3WordPresentation g) d

theorem partnerMarkedName_spec (d : ℕ)
    (g : CongruenceSubgroup.gamma3Partner.B) :
    (partnerPaddedPresentation d).hom
      (FreeGroup.mk (partnerMarkedName d g)) = g := by
  unfold partnerPaddedPresentation partnerMarkedName
  exact (presentation_hom_markedName _ d gamma3Positive_admissible
    partnerAnchor_killed).trans
      (PositivePresentation.presentation_hom_name gamma3WordPresentation g)

theorem partnerMarkedName_floor (d : ℕ)
    (g : CongruenceSubgroup.gamma3Partner.B) :
    d + 1 ≤ (partnerMarkedName d g).length :=
  depth_le_length_markedName _ partnerAnchor_ne_nil d _

theorem partnerMarkedName_marker_unique (d : ℕ)
    (g : CongruenceSubgroup.gamma3Partner.B) :
    ∀ c ∈ (partnerMarkedName d g).tail,
      c.1 ≠ Fin.last
        (withoutEmptyRelators gamma3PositiveWordPresentation).card :=
  markedName_marker_unique _ partnerAnchor d _

/-- Concrete source data with long marked defect names and an unchanged
protected name. -/
noncomputable def sourceData (d : ℕ) :
    SourceData LiteralAffineFreeProductSource.Ambient
      LiteralAffineFreeProductSource.amplifiedDefectData.core.defectNormal
      LiteralAffineFreeProductSource.amplifiedDefectData.s where
  pres := sourcePaddedPresentation d
  rel_positive := sourcePaddedPresentation_rel_positive d
  basisOneWord := sourceMarkedName d
    LiteralAffineFreeProductBassSerre.crossingDefect
  basisTwoWord := sourceMarkedName d conjugateCrossing
  basisOneWord_positive := sourceMarkedName_positive _ _
  basisTwoWord_positive := sourceMarkedName_positive _ _
  basisOne_mem := by
    rw [sourceMarkedName_spec]
    exact LiteralAffineFreeProductBassSerre.crossingDefect_mem
  basisTwo_mem := by
    rw [sourceMarkedName_spec]
    exact conjugateCrossing_mem
  protectedSrcWord := padList (sourcePositiveName
    LiteralAffineFreeProductSource.amplifiedDefectData.s)
  protectedSrcWord_spec := by
    exact (sourcePositiveWordPresentation.pad_hom_padList [] _).trans
      (sourcePositiveName_spec _)
  tieDefectWord := LiteralAffineFreeProductAvatarBlueprint.tieDefectWord
  tieDefectWord_positive :=
    LiteralAffineFreeProductAvatarBlueprint.tieDefectWord_positive

/-- Concrete partner data with long once-marked tie names. -/
noncomputable def partnerData (d : ℕ) :
    PartnerData CongruenceSubgroup.gamma3Partner.B where
  pres := partnerPaddedPresentation d
  rel_positive := partnerPaddedPresentation_rel_positive d
  tiePartnerWord := fun i ↦ partnerMarkedName d (gamma3TieElements i)
  tiePartnerWord_positive := fun i ↦
    partnerMarkedName_positive d (gamma3TieElements i)

/-- The padded replacement for
`LiteralAffineFreeProductAvatarBlueprint.blueprint`. -/
noncomputable def blueprint (d : ℕ) :
    Blueprint LiteralAffineFreeProductSource.Ambient
      LiteralAffineFreeProductSource.amplifiedDefectData.core.defectNormal
      LiteralAffineFreeProductSource.amplifiedDefectData.s
      CongruenceSubgroup.gamma3Partner.B where
  src := sourceData d
  par := partnerData d

/-- Both designated defect spellings meet the padding floor. -/
theorem blueprint_basisWord_floor (d : ℕ) (k : Fin 2) :
    d + 1 ≤ ((blueprint d).basisWord k).length := by
  fin_cases k
  · exact sourceMarkedName_floor d _
  · exact sourceMarkedName_floor d _

/-- Expanded source relators meet `(d+1)` avatar lengths. -/
theorem blueprint_src_floor (d : ℕ)
    (r : List (Fin (blueprint d).srcPres.card × Bool))
    (hr : r ∈ (blueprint d).srcPres.rel) :
    (d + 1) * (blueprint d).avatarLength ≤
      (avatarSubst (blueprint d).srcAvatarWord r).length := by
  rw [length_avatarSubst_eq (blueprint d).srcAvatarWord
    (blueprint d).avatarLength (blueprint d).length_srcAvatarWord]
  exact Nat.mul_le_mul_right (blueprint d).avatarLength
    (sourcePaddedPresentation_rel_floor d r hr)

/-- Expanded partner relators meet the same floor. -/
theorem blueprint_par_floor (d : ℕ)
    (r : List (Fin (blueprint d).parPres.card × Bool))
    (hr : r ∈ (blueprint d).parPres.rel) :
    (d + 1) * (blueprint d).avatarLength ≤
      (avatarSubst (blueprint d).parAvatarWord r).length := by
  rw [length_avatarSubst_eq (blueprint d).parAvatarWord
    (blueprint d).avatarLength (blueprint d).length_parAvatarWord]
  exact Nat.mul_le_mul_right (blueprint d).avatarLength
    (partnerPaddedPresentation_rel_floor d r hr)

/-- The multiplicity-free defect ties retain their exact singleton shape. -/
theorem blueprint_defectTieWord (d : ℕ) (i : Fin 2) :
    (blueprint d).defectTieWord i =
      [((i : Fin 2), true)] ++ (blueprint d).defectAvatarWord i := by
  fin_cases i
  · change [((0 : Fin 2), true)] ++
      avatarSubst (blueprint d).defectAvatarWord [((0 : Fin 2), true)] = _
    rw [avatarSubst_cons, avatarSubst_nil]
    simp [avatarSubstLetter]
  · change [((1 : Fin 2), true)] ++
      avatarSubst (blueprint d).defectAvatarWord [((1 : Fin 2), true)] = _
    rw [avatarSubst_cons, avatarSubst_nil]
    simp [avatarSubstLetter]

/-- The expanded defect ties meet the common floor. -/
theorem blueprint_defectTie_floor (d : ℕ) (i : Fin 2) :
    (d + 1) * (blueprint d).avatarLength ≤
      ((blueprint d).defectTieWord i).length := by
  rw [blueprint_defectTieWord]
  simp only [List.length_append, List.length_cons, List.length_nil]
  have hsubst := le_length_avatarSubst (blueprint d).srcAvatarWord
    (blueprint d).avatarLength
    (fun k ↦ le_of_eq ((blueprint d).length_srcAvatarWord k).symm)
    ((blueprint d).basisWord i)
  have hb := blueprint_basisWord_floor d i
  have hmul := Nat.mul_le_mul_right (blueprint d).avatarLength hb
  exact le_trans hmul (le_trans hsubst (Nat.le_add_left _ 1))

/-- The expanded partner ties meet the common floor. -/
theorem blueprint_partnerTie_floor (d : ℕ) (i : Fin 2) :
    (d + 1) * (blueprint d).avatarLength ≤
      ((blueprint d).partnerTieWord i).length := by
  change (d + 1) * (blueprint d).avatarLength ≤
    ([((i : Fin 2), true)] ++ avatarSubst (blueprint d).parAvatarWord
      (partnerMarkedName d (gamma3TieElements i))).length
  rw [List.length_append,
    length_avatarSubst_eq (blueprint d).parAvatarWord
      (blueprint d).avatarLength (blueprint d).length_parAvatarWord]
  simp only [List.length_cons, List.length_nil]
  have hname := partnerMarkedName_floor d (gamma3TieElements i)
  have hmul := Nat.mul_le_mul_right (blueprint d).avatarLength hname
  exact le_trans hmul (Nat.le_add_left _ 1)

/-- The exact hypothetical checklist after the valid presentation-level facts.
The companion checks module proves this type is empty for this nested Nielsen
family. -/
abbrev ConcreteRemainingRouterChecks (d : ℕ) : Type :=
  RemainingRouterChecks (blueprint d) (d + 1)

/-- A diagnostic adapter into the exact downstream interface.  Its premise is
proved impossible for this family in the companion checks module. -/
noncomputable def inputsOfRemaining (d : ℕ)
    (H : ConcreteRemainingRouterChecks d) :
    AvatarRouterInstance.Inputs (blueprint d) where
  avatarLen := (blueprint d).avatarLength
  runCeil := H.runCeil
  sharedBound := H.sharedBound
  wordFloor := d + 1
  src_avatar_long := fun i ↦
    le_of_eq ((blueprint d).length_srcAvatarWord i).symm
  par_avatar_long := fun i ↦
    le_of_eq ((blueprint d).length_parAvatarWord i).symm
  src_floor := blueprint_src_floor d
  par_floor := blueprint_par_floor d
  defectTie_floor := blueprint_defectTie_floor d
  partnerTie_floor := blueprint_partnerTie_floor d
  basis_ne_nil := fun k ↦ by
    have h := blueprint_basisWord_floor d k
    omega
  piece_short := H.piece_short
  occurrenceMarks := H.occurrenceMarks
  flank_small := H.flank_small
  floor_ge := H.floor_ge
  protectedLength := H.protectedLength
  protected_norm := H.protected_norm
  protected_margin := H.protected_margin

end

end LiteralAffineFreeProductPaddedAvatarBlueprint
end GroupApproximation
