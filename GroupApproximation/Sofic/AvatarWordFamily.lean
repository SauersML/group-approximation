import GroupApproximation.Sofic.AvatarMetricCheck
import GroupApproximation.Sofic.BespokeRouterGateAssembly
import GroupApproximation.Kazhdan.TorsionFreeKazhdanPartner
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The avatar word family: the router's relator design, transcribed

`Sofic.BespokeRouterConstruction` freezes the *input* side of the bespoke
router as `RouterRelatorDesign E N s B`, and derives every structural field of
`RoutingLemmaData` from it.  Until now that structure had no inhabitant: it is
a typed target for a word design, and the design lived only on paper, in
`notes/W3_AVATAR_WORD_DESIGN_2026-08-21.md`.  This module is that note,
transcribed into Lean data over abstract finite presentation input, so that the
only thing left between a source group and a term of `RoutingLemmaData` is a
finite list of word-combinatorial checks.

## The four pieces

* **§2, Tietze padding.**  The ball-injectivity engine wants
  `2·|W_d| ≤ min relator length`, and both sides scale linearly in avatar
  length, so avatar inflation can never fix a short presentation relator.  The
  fix is presentational: adjoin a fresh generator `w` with defining relator
  `w·Λ⁻¹` for a long word `Λ`, and append `w·Λ⁻¹` to every old relator.
  `WordPresentation.pad` does this; `WordPresentation.pad_hom_padList` is that
  the presented group is unchanged on the old generators, and
  `WordPresentation.le_length_of_mem_padRel` is the length floor `|Λ| + 1`.

  This is a **toolkit for the general alphabet, and the family does not run
  through it**: `w·Λ⁻¹` is not a positive word, and positivity is what makes
  the family reduced (below).  Under the positivity convention the same floor
  is obtained by appending positive trivial words instead — see
  `SourceData`, whose docstring records that and the two traps that come with
  it.  The padding is kept here because it is the general construction, and
  because it is what a caller who abandons positivity would need.

* **§2, the exponent code.**  `avatarWord L K ν` is the explicit positive word
  `∏_{j=1}^{L} y₁·y₂^{K·ν+j}` as a `List (Fin 2 × Bool)`.  The whole design
  rests on one arithmetic fact, `codeExponent_inj`: when the stride exceeds the
  block length — and `K = 2L` gives that — the pair `(ν, j)` is recoverable
  from the exponent `K·ν + j + 1`, so the exponent ranges of distinct avatars
  are disjoint and every exponent in the system occurs exactly once.

* **§3, the family.**  `Blueprint.relators` is `R_E ∪ R_B ∪ R_tie`: the padded
  source relators rewritten through the source avatars, the padded partner
  relators rewritten through the partner avatars, and the four tying relators
  `y_j·T_j⁻¹`, `y_j·T'_j⁻¹` over designated long defect and partner words.

* **§4, well-definedness.**  Literal membership, exactly as the note predicts:
  `srcRel_rewrite` and `parRel_rewrite` are `mem_relSubgroup` applied to a
  member of the family, and the two tying fields are `mem_relSubgroup` applied
  to a tying relator.  No combinatorics.

## What is a hypothesis, and why

`Blueprint.Obligations` carries the four word-level checks the construction
does not decide: no proper powers, the metric condition, nontriviality of the
protected avatar, and the protected ball.  They are named hypotheses in the
library's data-not-axiom style.  Three of the four are already proved
elsewhere: `Sofic.AvatarMetricCheck` establishes the metric condition, the
no-proper-power clause and the protected ball against its `AvatarMetricData`
bundle, and `Blueprint.obligations_of_metricData` feeds this family's relators
into it.  Only nontriviality of the protected avatar is open on both sides.

Cyclic reducedness is deliberately *not* on that list.  It is proved outright,
as `Blueprint.relators_cyclicallyReduced`, because **the whole family is a
family of positive words**, and a positive word is cyclically reduced on the
nose: reducedness asks that adjacent letters sharing a generator share a sign,
the wrap seam asks the same of the first and last letters, and when every
letter is positive both hold without ever being tested
(`AvatarMetricCheck.isCyclicallyReduced_of_forall_positive`).

That is worth stating carefully, because the obvious construction does *not*
have it, and leaving the field as a hypothesis would have been worse than
useless — it would have been false rather than open, and `Blueprint.design`
vacuous rather than conditional.  Avatars are positive words, all beginning
with `y₁` and all ending with `y₂`, so a junction between a positive and a
negative source letter rewrites to `y₂` against `y₂⁻¹`, and one between a
negative and a positive letter to `y₁⁻¹` against `y₁`.  Both cancel for *any*
avatars whatsoever, so a relator carrying a sign change never rewrites to a
reduced word.  The fix is presentational, of exactly the same kind as §2's
padding: take the source and partner presentations with **all relators
positive**, which every finitely presented group admits — adjoin `x̄` for each
generator `x` with the positive relator `x·x̄`, then rewrite every `x⁻¹` as `x̄`.
`SourceData.rel_positive` records that convention.

The four tying relators are positive too, by a design choice rather than by
luck: the tie is written `y_j·T_j`, saying `y_j = T_j⁻¹`, instead of the note's
`y_j·T_j⁻¹`, saying `y_j = T_j`.  Both put `y_j` in the subgroup generated by
the avatars — a subgroup is closed under inverses — and only the first is a
positive word.  Nothing downstream can tell the difference, because
`BespokeRouter.RouterRelatorDesign.tieDefect` quantifies over the closure.

The metric condition is stated at **`C'(1/8)`**, not `C'(1/6)`.  That is the
design's own constant — at `λ ≤ 1/8`, read in the sharp form
`|u| > (1−3λ)|r|`, the torsion descent's residual case is arithmetically empty
— and `1/6` is *derived* from it by `metricSmallCancellation_mono`.
Monotonicity runs `C'(1/8) → C'(1/6)` and never the reverse, so a `C'(1/6)`
hypothesis would be strictly weaker and would not feed
`GreendlingerFreeGate.router_conclusions_of_sharpGate`.  One `C'(1/8)` proof
serves the landed `metric` field and the gate call both.
-/

namespace GroupApproximation
namespace BespokeRouter
namespace AvatarWordFamily

open SmallCancellationRouter

/-! ## 0.  Word families over an arbitrary alphabet -/

/-- The normal subgroup a family of *words* presents, over an arbitrary
alphabet.  At `α = Fin 2` this is `BespokeRouter.relSubgroup`; it is restated
here because the source and partner presentations live over their own
alphabets. -/
def wordSubgroup {α : Type} (R : Set (List (α × Bool))) : Subgroup (FreeGroup α) :=
  Subgroup.normalClosure (FreeGroup.mk '' R)

/-- Registered because instance search stops at the `def`. -/
instance wordSubgroup_normal {α : Type} (R : Set (List (α × Bool))) :
    (wordSubgroup R).Normal :=
  Subgroup.normalClosure_normal

/-- A member of the family lies in the subgroup it presents. -/
theorem mem_wordSubgroup {α : Type} {R : Set (List (α × Bool))}
    {r : List (α × Bool)} (hr : r ∈ R) : FreeGroup.mk r ∈ wordSubgroup R :=
  Subgroup.subset_normalClosure ⟨r, hr, rfl⟩

/-- A relator of the shape `g · w⁻¹` identifies `g` with `w` in the presented
quotient.  This is `BespokeRouter.mkR_eq_of_mem` at an arbitrary alphabet. -/
theorem quot_eq_of_mem {α : Type} {R : Set (List (α × Bool))} {g w : FreeGroup α}
    (h : g * w⁻¹ ∈ wordSubgroup R) :
    QuotientGroup.mk' (wordSubgroup R) g = QuotientGroup.mk' (wordSubgroup R) w := by
  have h1 : QuotientGroup.mk' (wordSubgroup R) (g * w⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

/-! ## 1.  Avatar substitution -/

section Substitution

variable {α : Type}

/-- One letter, rewritten through an avatar assignment: a positive letter goes
to its avatar, a negative letter to the formal inverse of its avatar. -/
def avatarSubstLetter (A : α → List (Fin 2 × Bool)) : α × Bool → List (Fin 2 × Bool)
  | (i, true) => A i
  | (i, false) => FreeGroup.invRev (A i)

/-- A whole word, rewritten through an avatar assignment. -/
def avatarSubst (A : α → List (Fin 2 × Bool)) (w : List (α × Bool)) :
    List (Fin 2 × Bool) :=
  (w.map (avatarSubstLetter A)).flatten

/-- Rewriting the empty word. -/
theorem avatarSubst_nil (A : α → List (Fin 2 × Bool)) : avatarSubst A [] = [] := by
  simp [avatarSubst]

/-- Rewriting is letterwise concatenation. -/
theorem avatarSubst_cons (A : α → List (Fin 2 × Bool)) (x : α × Bool)
    (w : List (α × Bool)) :
    avatarSubst A (x :: w) = avatarSubstLetter A x ++ avatarSubst A w := by
  simp only [avatarSubst, List.map_cons, List.flatten_cons]

/-- A rewritten letter has the length of its avatar, sign notwithstanding. -/
theorem length_avatarSubstLetter (A : α → List (Fin 2 × Bool)) (x : α × Bool) :
    (avatarSubstLetter A x).length = (A x.1).length := by
  obtain ⟨i, b⟩ := x
  cases b
  · show (FreeGroup.invRev (A i)).length = (A i).length
    exact FreeGroup.invRev_length
  · show (A i).length = (A i).length
    rfl

/-- One letter's rewrite spells the corresponding value of the assignment. -/
theorem mk_avatarSubstLetter (A : α → List (Fin 2 × Bool)) (x : α × Bool) :
    FreeGroup.mk (avatarSubstLetter A x)
      = FreeGroup.lift (fun k => FreeGroup.mk (A k)) (FreeGroup.mk [x]) := by
  obtain ⟨i, b⟩ := x
  cases b
  · show FreeGroup.mk (FreeGroup.invRev (A i))
        = FreeGroup.lift (fun k => FreeGroup.mk (A k)) (FreeGroup.mk [(i, false)])
    rw [FreeGroup.lift_mk, ← FreeGroup.inv_mk]
    simp
  · show FreeGroup.mk (A i)
        = FreeGroup.lift (fun k => FreeGroup.mk (A k)) (FreeGroup.mk [(i, true)])
    rw [FreeGroup.lift_mk]
    simp

/-- **Rewriting commutes with the presentation map.**  This is the bridge that
turns the whole design into list combinatorics: a rewritten word *spells* the
image of the original under the assignment. -/
theorem mk_avatarSubst (A : α → List (Fin 2 × Bool)) (w : List (α × Bool)) :
    FreeGroup.mk (avatarSubst A w)
      = FreeGroup.lift (fun k => FreeGroup.mk (A k)) (FreeGroup.mk w) := by
  induction w with
  | nil =>
      have h1 : FreeGroup.mk (avatarSubst A ([] : List (α × Bool)))
          = (1 : FreeGroup (Fin 2)) := FreeGroup.one_eq_mk.symm
      have h2 : FreeGroup.mk ([] : List (α × Bool)) = (1 : FreeGroup α) :=
        FreeGroup.one_eq_mk.symm
      rw [h1, h2, map_one]
  | cons x w ih =>
      have hsplit : FreeGroup.mk (x :: w) = FreeGroup.mk [x] * FreeGroup.mk w :=
        FreeGroup.mul_mk.symm
      rw [avatarSubst_cons, ← FreeGroup.mul_mk]
      rw [ih, mk_avatarSubstLetter]
      rw [hsplit, map_mul]

/-- The same, phrased against an assignment presented as free-group elements —
the shape `RouterRelatorDesign.W` and `RouterRelatorDesign.U` take. -/
theorem lift_mk_eq_mk_avatarSubst (A : α → List (Fin 2 × Bool)) (W : α → RouterFree)
    (hW : ∀ k, W k = FreeGroup.mk (A k)) (w : List (α × Bool)) :
    FreeGroup.lift W (FreeGroup.mk w) = FreeGroup.mk (avatarSubst A w) := by
  have hfun : W = fun k => FreeGroup.mk (A k) := funext hW
  rw [hfun]
  exact (mk_avatarSubst A w).symm

/-- A rewritten word is at most the source length times the longest avatar. -/
theorem length_avatarSubst_le (A : α → List (Fin 2 × Bool)) (M : ℕ)
    (hM : ∀ k, (A k).length ≤ M) (w : List (α × Bool)) :
    (avatarSubst A w).length ≤ w.length * M := by
  induction w with
  | nil => simp [avatarSubst_nil]
  | cons x w ih =>
      have hx : (avatarSubstLetter A x).length ≤ M := by
        rw [length_avatarSubstLetter]
        exact hM x.1
      rw [avatarSubst_cons, List.length_append, List.length_cons, add_mul, one_mul]
      omega

/-- A rewritten word is at least the source length times the shortest avatar.
With `WordPresentation.le_length_of_mem_padRel` this is what carries the
padding floor through to the family. -/
theorem le_length_avatarSubst (A : α → List (Fin 2 × Bool)) (m : ℕ)
    (hm : ∀ k, m ≤ (A k).length) (w : List (α × Bool)) :
    w.length * m ≤ (avatarSubst A w).length := by
  induction w with
  | nil => simp
  | cons x w ih =>
      have hx : m ≤ (avatarSubstLetter A x).length := by
        rw [length_avatarSubstLetter]
        exact hm x.1
      rw [avatarSubst_cons, List.length_append, List.length_cons, add_mul, one_mul]
      omega

/-- **A positive word rewrites to a positive word.**  A positive source letter
is sent to its avatar unmodified — there is no `FreeGroup.invRev` anywhere on
this branch, which is exactly what the positivity convention buys.  With
`AvatarMetricCheck.isCyclicallyReduced_of_forall_positive` this is the whole
proof of the design's cyclic-reducedness field. -/
theorem forall_positive_avatarSubst (A : α → List (Fin 2 × Bool))
    (hA : ∀ k, ∀ c ∈ A k, c.2 = true) {w : List (α × Bool)}
    (hw : ∀ x ∈ w, x.2 = true) :
    ∀ c ∈ avatarSubst A w, c.2 = true := by
  refine AvatarMetricCheck.forall_positive_flatten ?_
  intro u hu c hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
  obtain ⟨i, b⟩ := x
  cases b
  · exact absurd (hw _ hx) (by simp)
  · exact hA i c hc

end Substitution

/-! ## 2.  Tietze padding, at the word level -/

section Padding

variable {n : ℕ}

/-- An old letter list, in the padded alphabet. -/
def padList (w : List (Fin n × Bool)) : List (Fin (n + 1) × Bool) :=
  w.map fun x => (x.1.castSucc, x.2)

/-- Padding does not change a word's length. -/
theorem length_padList (w : List (Fin n × Bool)) : (padList w).length = w.length := by
  simp [padList]

/-- The defining relator of the fresh generator: `w · Λ⁻¹`. -/
def padDefiner (long : List (Fin n × Bool)) : List (Fin (n + 1) × Bool) :=
  [(Fin.last n, true)] ++ FreeGroup.invRev (padList long)

/-- A padded relator: `ρ · w · Λ⁻¹`. -/
def padRelator (long r : List (Fin n × Bool)) : List (Fin (n + 1) × Bool) :=
  padList r ++ padDefiner long

/-- The defining relator has length `|Λ| + 1`. -/
theorem length_padDefiner (long : List (Fin n × Bool)) :
    (padDefiner long).length = long.length + 1 := by
  simp only [padDefiner, List.length_append, List.length_cons, List.length_nil,
    FreeGroup.invRev_length, length_padList]
  omega

/-- A padded relator has length `|ρ| + |Λ| + 1`. -/
theorem length_padRelator (long r : List (Fin n × Bool)) :
    (padRelator long r).length = r.length + long.length + 1 := by
  simp only [padRelator, List.length_append, length_padList, length_padDefiner]
  omega

/-- The defining relator spells `w · Λ⁻¹`. -/
theorem mk_padDefiner (long : List (Fin n × Bool)) :
    FreeGroup.mk (padDefiner long)
      = FreeGroup.of (Fin.last n) * (FreeGroup.mk (padList long))⁻¹ :=
  calc FreeGroup.mk (padDefiner long)
      = FreeGroup.of (Fin.last n) *
          FreeGroup.mk (FreeGroup.invRev (padList long)) := FreeGroup.mul_mk.symm
    _ = FreeGroup.of (Fin.last n) * (FreeGroup.mk (padList long))⁻¹ := by
        rw [FreeGroup.inv_mk]

/-- A padded relator spells `ρ` times the defining relator. -/
theorem mk_padRelator (long r : List (Fin n × Bool)) :
    FreeGroup.mk (padRelator long r)
      = FreeGroup.mk (padList r) * FreeGroup.mk (padDefiner long) :=
  FreeGroup.mul_mk.symm

/-- The alphabet embedding of the padding step. -/
def padHomOf : FreeGroup (Fin n) →* FreeGroup (Fin (n + 1)) :=
  FreeGroup.map Fin.castSucc

/-- The embedding is `padList` on spelled words. -/
theorem padHomOf_mk (w : List (Fin n × Bool)) :
    (padHomOf : FreeGroup (Fin n) →* _) (FreeGroup.mk w) = FreeGroup.mk (padList w) :=
  rfl

/-- The embedding on generators. -/
theorem padHomOf_of (i : Fin n) :
    (padHomOf : FreeGroup (Fin n) →* _) (FreeGroup.of i) = FreeGroup.of i.castSucc :=
  rfl

/-- The retraction of the padding step: the fresh generator goes back to the
long word it was defined to equal.  This is the whole content of "padding
preserves the presented group". -/
def padRetract (long : List (Fin n × Bool)) :
    FreeGroup (Fin (n + 1)) →* FreeGroup (Fin n) :=
  FreeGroup.lift (Fin.snoc FreeGroup.of (FreeGroup.mk long))

/-- The retraction fixes the old generators. -/
theorem padRetract_of_castSucc (long : List (Fin n × Bool)) (i : Fin n) :
    padRetract long (FreeGroup.of i.castSucc) = FreeGroup.of i := by
  simp [padRetract]

/-- The retraction sends the fresh generator to the long word. -/
theorem padRetract_of_last (long : List (Fin n × Bool)) :
    padRetract long (FreeGroup.of (Fin.last n)) = FreeGroup.mk long := by
  simp [padRetract]

/-- The retraction is a genuine retraction. -/
theorem padRetract_comp_padHomOf (long : List (Fin n × Bool)) :
    (padRetract long).comp padHomOf = MonoidHom.id (FreeGroup (Fin n)) :=
  FreeGroup.ext_hom _ _ fun i => by
    show padRetract long (padHomOf (FreeGroup.of i)) = FreeGroup.of i
    rw [padHomOf_of, padRetract_of_castSucc]

end Padding

/-! ## 2'.  Word presentations -/

/-- A finite presentation with the relators recorded as explicit letter lists.
This is `Group.IsFinitelyPresented` unpacked into the shape the router's design
consumes, one step further down: relators as *words*, so that their lengths are
`List.length` and the padding floor is arithmetic. -/
structure WordPresentation (G : Type) [Group G] where
  /-- The number of generators. -/
  card : ℕ
  /-- The presentation map. -/
  hom : FreeGroup (Fin card) →* G
  /-- It is onto: the chosen generators generate. -/
  hom_surjective : Function.Surjective hom
  /-- The defining relators, as letter lists. -/
  rel : Set (List (Fin card × Bool))
  /-- Finitely many of them. -/
  rel_finite : rel.Finite
  /-- They are defining. -/
  ker_le : hom.ker ≤ wordSubgroup rel

/-- **Every finitely presented group has a word presentation.**  Mathlib's
predicate gives relators as free-group elements; `FreeGroup.toWord` spells
them, and `FreeGroup.mk_toWord` says nothing is lost. -/
theorem nonempty_wordPresentation (G : Type) [Group G]
    [h : Group.IsFinitelyPresented G] : Nonempty (WordPresentation G) := by
  obtain ⟨m, φ, hφ, S, hSfin, hS⟩ := h.out
  refine ⟨⟨m, φ, hφ, FreeGroup.toWord '' S,
    hSfin.image FreeGroup.toWord, ?_⟩⟩
  have himg : FreeGroup.mk '' (FreeGroup.toWord '' S) = S := by
    ext g
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      rwa [FreeGroup.mk_toWord]
    · intro hg
      exact ⟨FreeGroup.toWord g, ⟨g, hg, rfl⟩, FreeGroup.mk_toWord⟩
  intro x hx
  show x ∈ Subgroup.normalClosure (FreeGroup.mk '' (FreeGroup.toWord '' S))
  rw [himg, hS]
  exact hx

/-- A choice of word presentation for a finitely presented group. -/
noncomputable def wordPresentation (G : Type) [Group G]
    [Group.IsFinitelyPresented G] : WordPresentation G :=
  (nonempty_wordPresentation G).some

namespace WordPresentation

variable {G : Type} [Group G] (P : WordPresentation G)

/-- The padded relator family: every old relator with `w·Λ⁻¹` appended, plus
the defining relator of the fresh generator. -/
def padRel (long : List (Fin P.card × Bool)) : Set (List (Fin (P.card + 1) × Bool)) :=
  padRelator long '' P.rel ∪ {padDefiner long}

/-- The padded presentation map: the old one, precomposed with the retraction. -/
def padHom (long : List (Fin P.card × Bool)) :
    FreeGroup (Fin (P.card + 1)) →* G :=
  P.hom.comp (padRetract long)

/-- The padded presentation map is still onto. -/
theorem padHom_surjective (long : List (Fin P.card × Bool)) :
    Function.Surjective (P.padHom long) := by
  intro g
  obtain ⟨x, rfl⟩ := P.hom_surjective g
  refine ⟨padHomOf x, ?_⟩
  have h : padRetract long (padHomOf x) = x :=
    calc padRetract long (padHomOf x)
        = ((padRetract long).comp padHomOf) x := rfl
      _ = (MonoidHom.id (FreeGroup (Fin P.card))) x := by
          rw [padRetract_comp_padHomOf]
      _ = x := rfl
  show P.hom (padRetract long (padHomOf x)) = P.hom x
  rw [h]

/-- **The padding floor.**  Every relator of the padded family is at least
`|Λ| + 1` letters long.  Choosing `Λ` with `2·ℓ_d + margin - 1` letters is
therefore exactly the note's §1 instruction, and the floor is unconditional:
it does not depend on how short the old relators were. -/
theorem le_length_of_mem_padRel (long : List (Fin P.card × Bool))
    {r : List (Fin (P.card + 1) × Bool)} (hr : r ∈ P.padRel long) :
    long.length + 1 ≤ r.length := by
  simp only [padRel, Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hr
  rcases hr with ⟨ρ, _, rfl⟩ | rfl
  · have h := length_padRelator long ρ
    omega
  · have h := length_padDefiner long
    omega

/-- **Padding is a Tietze transformation.**  The padded relators still define
the padded presentation map's kernel.  The proof is the classical one: modulo
the padded family the fresh generator *is* the long word, so the retraction is
the identity on the padded quotient, and an old relation is carried into the
padded family by cancelling the appended definer. -/
theorem padHom_ker_le (long : List (Fin P.card × Bool)) :
    (P.padHom long).ker ≤ wordSubgroup (P.padRel long) := by
  have hdef : FreeGroup.mk (padDefiner long) ∈ wordSubgroup (P.padRel long) :=
    mem_wordSubgroup (Set.mem_union_right _ rfl)
  have hold : ∀ r ∈ P.rel,
      FreeGroup.mk (padList r) ∈ wordSubgroup (P.padRel long) := by
    intro r hr
    have h1 : FreeGroup.mk (padRelator long r) ∈ wordSubgroup (P.padRel long) :=
      mem_wordSubgroup (Set.mem_union_left _ ⟨r, hr, rfl⟩)
    have h2 := mul_mem h1 (inv_mem hdef)
    rwa [mk_padRelator, mul_inv_cancel_right] at h2
  have hfix : ∀ a : Fin (P.card + 1),
      QuotientGroup.mk' (wordSubgroup (P.padRel long))
          (padHomOf (padRetract long (FreeGroup.of a)))
        = QuotientGroup.mk' (wordSubgroup (P.padRel long)) (FreeGroup.of a) := by
    intro a
    obtain ⟨i, rfl⟩ | rfl := a.eq_castSucc_or_eq_last
    · rw [padRetract_of_castSucc, padHomOf_of]
    · rw [padRetract_of_last, padHomOf_mk]
      refine (quot_eq_of_mem ?_).symm
      rw [← mk_padDefiner]
      exact hdef
  have hcomp : (QuotientGroup.mk' (wordSubgroup (P.padRel long))).comp
        (padHomOf.comp (padRetract long))
      = QuotientGroup.mk' (wordSubgroup (P.padRel long)) :=
    FreeGroup.ext_hom _ _ hfix
  have hker : wordSubgroup P.rel ≤
      ((QuotientGroup.mk' (wordSubgroup (P.padRel long))).comp padHomOf).ker := by
    refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨r, hr, rfl⟩
    exact MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff _).mpr (hold r hr))
  intro x hx
  have h1 : P.hom (padRetract long x) = 1 := MonoidHom.mem_ker.mp hx
  have h3 : padRetract long x ∈ wordSubgroup P.rel :=
    P.ker_le (MonoidHom.mem_ker.mpr h1)
  have h4 : QuotientGroup.mk' (wordSubgroup (P.padRel long))
      (padHomOf (padRetract long x)) = 1 := MonoidHom.mem_ker.mp (hker h3)
  have h5 := DFunLike.congr_fun hcomp x
  have h6 : QuotientGroup.mk' (wordSubgroup (P.padRel long)) x = 1 := by
    rw [← h5]
    exact h4
  exact (QuotientGroup.eq_one_iff _).mp h6

/-- **The Tietze padding of a word presentation.**  Adjoin a fresh generator
`w` with defining relator `w·Λ⁻¹` and append `w·Λ⁻¹` to every old relator: the
presented group is unchanged and every relator is now at least `|Λ| + 1`
letters long.  The padded presentation is design data, not an afterthought —
it is what the avatar rewriter is fed. -/
def pad (long : List (Fin P.card × Bool)) : WordPresentation G where
  card := P.card + 1
  hom := P.padHom long
  hom_surjective := P.padHom_surjective long
  rel := P.padRel long
  rel_finite := (P.rel_finite.image _).union (Set.finite_singleton _)
  ker_le := P.padHom_ker_le long

/-- The padded alphabet has one more letter. -/
theorem pad_card (long : List (Fin P.card × Bool)) :
    (P.pad long).card = P.card + 1 := rfl

/-- The padded presentation map, unfolded. -/
theorem pad_hom (long : List (Fin P.card × Bool)) :
    (P.pad long).hom = P.padHom long := rfl

/-- The padded relator family, unfolded. -/
theorem pad_rel (long : List (Fin P.card × Bool)) :
    (P.pad long).rel = P.padRel long := rfl

/-- **Padding preserves the presented group.**  On words in the old
generators the padded presentation map is the old one, so every element of `G`
named by an old word is named by the same word after padding — which is what
`basisOne_mem`, `basisTwo_mem` and `protectedWord_spec` need. -/
theorem pad_hom_padList (long w : List (Fin P.card × Bool)) :
    (P.pad long).hom (FreeGroup.mk (padList w)) = P.hom (FreeGroup.mk w) := by
  have h : padRetract long (padHomOf (FreeGroup.mk w)) = FreeGroup.mk w :=
    calc padRetract long (padHomOf (FreeGroup.mk w))
        = ((padRetract long).comp padHomOf) (FreeGroup.mk w) := rfl
      _ = (MonoidHom.id (FreeGroup (Fin P.card))) (FreeGroup.mk w) := by
          rw [padRetract_comp_padHomOf]
      _ = FreeGroup.mk w := rfl
  show P.hom (padRetract long (padHomOf (FreeGroup.mk w))) = P.hom (FreeGroup.mk w)
  rw [h]

end WordPresentation

/-! ## 3.  The exponent code -/

/-- `L = 16·(V+1)`, the number of blocks in each avatar.  `V` is the number of
avatar-carrying generators; the constant is deliberately generous. -/
def codeLength (V : ℕ) : ℕ := 16 * (V + 1)

/-- `K = 2L`, the stride between consecutive avatars' exponent ranges. -/
def codeStride (V : ℕ) : ℕ := 2 * codeLength V

/-- The block count is positive. -/
theorem codeLength_pos (V : ℕ) : 0 < codeLength V := by
  unfold codeLength
  omega

/-- **The stride exceeds the block length.**  This single inequality is what
makes the code injective, and `K = 2L` is chosen for it. -/
theorem codeLength_lt_codeStride (V : ℕ) : codeLength V < codeStride V := by
  have h := codeLength_pos V
  unfold codeStride
  omega

/-- The exponent carried by the `j`-th block of the `ν`-th avatar: `K·ν + j+1`,
so that the `ν`-th avatar's exponents fill the block `(K·ν, K·ν + L]`. -/
def codeExponent (K ν j : ℕ) : ℕ := K * ν + (j + 1)

/-- The block `y₁ · y₂^e`. -/
def blockWord (e : ℕ) : List (Fin 2 × Bool) :=
  ((0 : Fin 2), true) :: List.replicate e ((1 : Fin 2), true)

/-- A block has one `y₁` and `e` copies of `y₂`. -/
theorem length_blockWord (e : ℕ) : (blockWord e).length = e + 1 := by
  simp [blockWord]

/-- **The `ν`-th avatar**, `W_ν = ∏_{j=1}^{L} y₁ · y₂^{K·ν+j}` — a positive
word in the two free generators, written out as a letter list. -/
def avatarWord (L K ν : ℕ) : List (Fin 2 × Bool) :=
  ((List.range L).map fun j => blockWord (codeExponent K ν j)).flatten

/-- **Avatars are positive words.**  Each block is one `y₁` followed by a run of
`y₂`, and the avatar is their concatenation, so no letter is ever inverted. -/
theorem forall_positive_avatarWord (L K ν : ℕ) :
    ∀ c ∈ avatarWord L K ν, c.2 = true := by
  refine AvatarMetricCheck.forall_positive_flatten ?_
  intro u hu c hc
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hu
  rcases List.mem_cons.mp hc with rfl | hc'
  · rfl
  · have hcv : c = ((1 : Fin 2), true) := List.eq_of_mem_replicate hc'
    subst hcv
    rfl

/-- **The exponent range of one avatar** is the block `(K·ν, K·ν + L]`. -/
theorem codeExponent_mem_block {L K ν j : ℕ} (hj : j < L) :
    K * ν < codeExponent K ν j ∧ codeExponent K ν j ≤ K * ν + L := by
  unfold codeExponent
  omega

/-- **Every exponent occurs exactly once in the whole system.**  When the
stride exceeds the block length the pair `(ν, j)` is recoverable from
`K·ν + j + 1`: this is simultaneously the pairwise disjointness of the ranges
`[K·ν, K·ν + L)` and the injectivity of the code inside one range.  It is the
only arithmetic the design rests on. -/
theorem codeExponent_inj {L K ν j ν' j' : ℕ} (hK : L < K) (hj : j < L)
    (hj' : j' < L) (h : codeExponent K ν j = codeExponent K ν' j') :
    ν = ν' ∧ j = j' := by
  have key : ∀ a b c d : ℕ, c < L → a < b →
      codeExponent K a c < codeExponent K b d := by
    intro a b c d hc hab
    have hab' : a + 1 ≤ b := hab
    have h1 : K * (a + 1) ≤ K * b := Nat.mul_le_mul (le_refl K) hab'
    have h2 : K * a + K ≤ K * b :=
      calc K * a + K = K * (a + 1) := by ring
        _ ≤ K * b := h1
    unfold codeExponent
    omega
  rcases lt_trichotomy ν ν' with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (key ν ν' j j' hj hlt))
  · subst heq
    refine ⟨rfl, ?_⟩
    unfold codeExponent at h
    omega
  · exact absurd h.symm (Nat.ne_of_lt (key ν' ν j' j hj' hgt))

/-- **Distinct avatars use disjoint exponent ranges.** -/
theorem codeExponent_ne_of_index_ne {L K ν j ν' j' : ℕ} (hK : L < K) (hj : j < L)
    (hj' : j' < L) (hν : ν ≠ ν') :
    codeExponent K ν j ≠ codeExponent K ν' j' := fun h =>
  hν (codeExponent_inj hK hj hj' h).1

/-- Every block of a flattened list is short, so the flattening is. -/
theorem length_flatten_le {β : Type} (b : ℕ) :
    ∀ ls : List (List β), (∀ l ∈ ls, l.length ≤ b) →
      ls.flatten.length ≤ ls.length * b := by
  intro ls
  induction ls with
  | nil => intro _; simp
  | cons l ls ih =>
      intro h
      rw [List.flatten_cons, List.length_append, List.length_cons, add_mul, one_mul]
      have h1 : l.length ≤ b := h l (by simp)
      have h2 : ls.flatten.length ≤ ls.length * b :=
        ih fun x hx => h x (by simp [hx])
      omega

/-- Every block of a flattened list is long, so the flattening is. -/
theorem le_length_flatten {β : Type} (a : ℕ) :
    ∀ ls : List (List β), (∀ l ∈ ls, a ≤ l.length) →
      ls.length * a ≤ ls.flatten.length := by
  intro ls
  induction ls with
  | nil => intro _; simp
  | cons l ls ih =>
      intro h
      rw [List.flatten_cons, List.length_append, List.length_cons, add_mul, one_mul]
      have h1 : a ≤ l.length := h l (by simp)
      have h2 : ls.length * a ≤ ls.flatten.length :=
        ih fun x hx => h x (by simp [hx])
      omega

/-- The length of a flattening, as the sum of the block lengths. -/
theorem length_flatten_eq {β : Type} :
    ∀ ls : List (List β), ls.flatten.length = (ls.map List.length).sum := by
  intro ls
  induction ls with
  | nil => simp
  | cons l ls ih =>
      rw [List.flatten_cons, List.length_append, ih, List.map_cons, List.sum_cons]

/-- **The exact length of an avatar.**  Block `j` is one `y₁` and `K·ν+j+1`
copies of `y₂`, so the avatar is `∑_{j<L} (K·ν + j + 2)` letters.

This is strictly sharper than the two bounds below, which discard the
triangular term `∑ j` — for the design's constants that term is about `L²/2`
and is the dominant part of a low-index avatar, so a margin computed from
`le_length_avatarWord` alone pays for it twice.  The sum is left unevaluated on
purpose: whoever is doing margin arithmetic can apply Gauss to it in the
setting where the rest of the arithmetic lives. -/
theorem length_avatarWord (L K ν : ℕ) :
    (avatarWord L K ν).length = ((List.range L).map fun j => K * ν + j + 2).sum := by
  have hfun : (List.length ∘ fun j => blockWord (codeExponent K ν j))
      = (fun j : ℕ => K * ν + j + 2) := by
    funext j
    show (blockWord (codeExponent K ν j)).length = K * ν + j + 2
    rw [length_blockWord]
    unfold codeExponent
    omega
  show ((List.range L).map fun j => blockWord (codeExponent K ν j)).flatten.length = _
  rw [length_flatten_eq, List.map_map, hfun]

/-- The `ν`-th avatar is at least `L·(K·ν+2)` letters long.  Sharper than this,
and usually worth using instead, is `length_avatarWord`. -/
theorem le_length_avatarWord (L K ν : ℕ) :
    L * (K * ν + 2) ≤ (avatarWord L K ν).length := by
  have h : ∀ l ∈ (List.range L).map (fun j => blockWord (codeExponent K ν j)),
      K * ν + 2 ≤ l.length := by
    intro l hl
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hl
    rw [length_blockWord]
    unfold codeExponent
    omega
  have h2 := le_length_flatten (K * ν + 2) _ h
  rw [List.length_map, List.length_range] at h2
  exact h2

/-- The `ν`-th avatar is at most `L·(K·ν+L+1)` letters long. -/
theorem length_avatarWord_le (L K ν : ℕ) :
    (avatarWord L K ν).length ≤ L * (K * ν + L + 1) := by
  have h : ∀ l ∈ (List.range L).map (fun j => blockWord (codeExponent K ν j)),
      l.length ≤ K * ν + L + 1 := by
    intro l hl
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hl
    have hjL : j < L := List.mem_range.mp hj
    rw [length_blockWord]
    unfold codeExponent
    omega
  have h2 := length_flatten_le (K * ν + L + 1) _ h
  rw [List.length_map, List.length_range] at h2
  exact h2

/-! ## 4.  The blueprint -/

/-- What the router construction needs from the source side, over an arbitrary
finitely presented source.

**The presentation is the caller's responsibility, and three conventions are
load-bearing.**  All three are presentational — Tietze moves on the source, of
the same kind as §2's padding — and none of them constrains the group.

1. *Positive relators* (`rel_positive`), without which the rewrite is not
   reduced and the design's cyclic-reducedness field is false.  Adjoin `x̄` for
   each generator `x` with the positive relator `x·x̄`, then rewrite every `x⁻¹`
   as `x̄`.  This doubles the generator count, which the code constants absorb.

2. *Long relators, padded **per relator**, and never by a power.*  The metric
   and ball margins want a relator-length floor, and under the positivity
   convention §2's `w·Λ⁻¹` padding is unavailable.  Pad instead by appending
   positive trivial words `x₁x̄₁·x₂x̄₂·…`.  Two traps, both fatal:

   * **Padding every relator with the same tail `Λ` makes `C'(1/8)` false.**
     `ρ₁·Λ` and `ρ₂·Λ` rewrite to words sharing the suffix `avatarSubst Λ`, and
     symmetrization contains all rotations, so some rotation makes that shared
     suffix a common *prefix* — a piece of length `|Λ|·(avatar length)`.  With
     `Λ` carrying most of a padded relator that piece is a constant fraction of
     `|r|`, and padding *harder* makes it worse.  The design note's §1, read
     literally, therefore defeats its own §2.  Give each relator its own tail,
     over a fresh generator pair no other relator uses.

   * Padding with `(x·x̄)^k` makes the rewritten relator a proper power — a
     rewrite of a power is a power — and destroys the no-proper-power field.
     Use **distinct** pairs.

3. *One avatar per relator occurring exactly once*, which is what
   `AvatarMetricCheck.AvatarMetricData.uniqueMark` reads.  An avatar occurring
   twice in a relator repeats all `L` of its exponents, leaving no exponent
   unique in that relator.  The per-relator padding of (2) already supplies
   this: one fresh generator pair per relator does both jobs, and `V` has slack
   by design. -/
structure SourceData (E : Type) [Group E] (N : Subgroup E) (s : E) where
  /-- A word presentation of the source. -/
  pres : WordPresentation E
  /-- **The positivity convention**: every relator is a positive word.

  What this buys outright is cyclic reducedness of the rewrite
  (`Blueprint.relators_cyclicallyReduced`).  It also buys something for the run
  ceiling, but *less than it looks*, and the difference is worth being exact
  about.  Because a positive word is in particular reduced, nothing cancels at
  a junction, so there are no junction residues and the ceiling does not have
  to be doubled to accommodate them.  It does **not** follow that the runs are
  bounded by `A_max` at all: a positive word may be `y₂` a thousand times over.
  That bound is a property of the avatar code's block structure — every `y₂`-run
  is separated by a `y₁` and carries a code exponent — and it needs the
  corresponding induction, which lives in `AvatarRunBound`.  Until that lands,
  `AvatarMetricCheck.AvatarMetricData.runs_short` stays an instantiation
  hypothesis and is not a consequence of this field. -/
  rel_positive : ∀ r ∈ pres.rel, ∀ c ∈ r, c.2 = true
  /-- **Per-relator padding, as data.**  Each relator carries a *private*
  generator: one occurring exactly once in it, and in no other relator.  This
  is convention (2)'s per-relator tail, stated so that it can be consumed
  rather than merely intended.

  **What it gives, and what it does not.**  It gives
  `AvatarMetricCheck.AvatarMetricData.uniqueMark`: the private generator's
  avatar occurs once in the relator, so each of its `L` exponents is read at
  exactly one cyclic position, which is the unique mark that field asks for.

  It does **not** give `pinned`, and the gap is worth stating rather than
  papering over.  A window carrying three separators spans two complete
  `y₂`-runs; an avatar has `L = 16·(V+1)` blocks, so such a window normally
  sits entirely *inside one avatar*.  It therefore pins `(ν, j)` — which
  generator, which block — but not which relator, because the same generator
  may occur in two different relators.  Rotating each of those to begin at the
  window makes it a common prefix of two distinct symmetrized relators.  So
  `pinned` at threshold three would need every avatar *occurrence* to be unique
  across the whole family, which is far stronger than one private generator per
  relator, and is not something a presentation of an arbitrary group can be
  massaged into.

  The way out is to weaken the conclusion rather than strengthen this
  hypothesis: a piece may legitimately be about one avatar long — two relators
  sharing a generator share that generator's whole avatar — and the metric
  condition survives provided relators are long *measured in avatars*.  That
  moves the margin off `piece ≤ 3·A_max + 3` and onto the ratio of a single
  avatar to a whole relator, where the spread between the shortest and longest
  avatar is what has to be paid for.  The arithmetic belongs with whoever owns
  the margin. -/
  privateGen : ∀ r ∈ pres.rel, ∃ i : Fin pres.card,
    r.count (i, true) = 1 ∧ ∀ r' ∈ pres.rel, r' ≠ r → (i, true) ∉ r'
  /-- The first designated defect element, as a word. -/
  basisOneWord : List (Fin pres.card × Bool)
  /-- The second designated defect element, as a word. -/
  basisTwoWord : List (Fin pres.card × Bool)
  /-- The first designated defect word is positive.  Free under the positivity
  convention: with `x̄` adjoined, every element has a positive representative. -/
  basisOneWord_positive : ∀ c ∈ basisOneWord, c.2 = true
  /-- The second designated defect word is positive. -/
  basisTwoWord_positive : ∀ c ∈ basisTwoWord, c.2 = true
  /-- The first designated element lies in the designated normal subgroup. -/
  basisOne_mem : pres.hom (FreeGroup.mk basisOneWord) ∈ N
  /-- The second designated element lies in the designated normal subgroup. -/
  basisTwo_mem : pres.hom (FreeGroup.mk basisTwoWord) ∈ N
  /-- The protected element, as a word. -/
  protectedSrcWord : List (Fin pres.card × Bool)
  /-- It is a word for the protected element. -/
  protectedSrcWord_spec : pres.hom (FreeGroup.mk protectedSrcWord) = s
  /-- The two designated long words `T₁`, `T₂` in the defect pair `(a, b)`,
  written in two abstract letters — letter `0` is `a`, letter `1` is `b`.  They
  must be positive for the tying relators to be positive. -/
  tieDefectWord : Fin 2 → List (Fin 2 × Bool)
  /-- The designated long words are positive. -/
  tieDefectWord_positive : ∀ i, ∀ c ∈ tieDefectWord i, c.2 = true

/-- What the router construction needs from the partner side.  The three
conventions of `SourceData` apply verbatim on this side. -/
structure PartnerData (B : Type) [Group B] where
  /-- A word presentation of the partner. -/
  pres : WordPresentation B
  /-- **The positivity convention**: every relator is a positive word. -/
  rel_positive : ∀ r ∈ pres.rel, ∀ c ∈ r, c.2 = true
  /-- **Per-relator padding, as data**; see `SourceData.privateGen`. -/
  privateGen : ∀ r ∈ pres.rel, ∃ i : Fin pres.card,
    r.count (i, true) = 1 ∧ ∀ r' ∈ pres.rel, r' ≠ r → (i, true) ∉ r'
  /-- The two designated long partner words `T'₁`, `T'₂`. -/
  tiePartnerWord : Fin 2 → List (Fin pres.card × Bool)
  /-- They are positive. -/
  tiePartnerWord_positive : ∀ i, ∀ c ∈ tiePartnerWord i, c.2 = true

/-- **The blueprint**: source data and partner data, from which the whole
relator family is a construction. -/
structure Blueprint (E : Type) [Group E] (N : Subgroup E) (s : E)
    (B : Type) [Group B] where
  /-- The source side. -/
  src : SourceData E N s
  /-- The partner side. -/
  par : PartnerData B

namespace Blueprint

variable {E : Type} [Group E] {N : Subgroup E} {s : E} {B : Type} [Group B]
    (D : Blueprint E N s B)

/-! ### The padded presentations -/

/-- The source presentation the family is built on.  Under the positivity
convention this is the caller's presentation directly: §2's `w·Λ⁻¹` padding
would break positivity, so the length floor is obtained instead by appending
positive trivial words, which happens before the presentation reaches here.
`WordPresentation.pad` remains available for the general alphabet. -/
def srcPres : WordPresentation E := D.src.pres

/-- The partner presentation the family is built on. -/
def parPres : WordPresentation B := D.par.pres

/-- The source alphabet. -/
theorem srcPres_card : D.srcPres.card = D.src.pres.card := rfl

/-- The partner alphabet. -/
theorem parPres_card : D.parPres.card = D.par.pres.card := rfl

/-- Source relators are positive, by the convention. -/
theorem srcPres_rel_positive :
    ∀ r ∈ D.srcPres.rel, ∀ c ∈ r, c.2 = true := D.src.rel_positive

/-- Partner relators are positive, by the convention. -/
theorem parPres_rel_positive :
    ∀ r ∈ D.parPres.rel, ∀ c ∈ r, c.2 = true := D.par.rel_positive

/-! ### The code constants and the avatars -/

/-- The number of avatar-carrying generators. -/
def avatarCount : ℕ := D.srcPres.card + D.parPres.card

/-- The blueprint's `L`. -/
def codeL : ℕ := codeLength D.avatarCount

/-- The blueprint's `K = 2L`. -/
def codeK : ℕ := codeStride D.avatarCount

/-- The blueprint's stride exceeds its block length. -/
theorem codeL_lt_codeK : D.codeL < D.codeK := codeLength_lt_codeStride _

/-- The avatar of the `i`-th padded source generator. -/
def srcAvatarWord (i : Fin D.srcPres.card) : List (Fin 2 × Bool) :=
  avatarWord D.codeL D.codeK (i : ℕ)

/-- The avatar of the `k`-th padded partner generator: the partner indices sit
above the source indices, so the two families never share an exponent. -/
def parAvatarWord (k : Fin D.parPres.card) : List (Fin 2 × Bool) :=
  avatarWord D.codeL D.codeK (D.srcPres.card + (k : ℕ))

/-- **Source and partner avatar indices are distinct.**  With
`codeExponent_inj` this is the system-wide half of "each exponent appears
exactly once". -/
theorem srcIndex_ne_parIndex (i : Fin D.srcPres.card) (k : Fin D.parPres.card) :
    (i : ℕ) ≠ D.srcPres.card + (k : ℕ) := by
  have h := i.isLt
  omega

/-- **System-wide exponent uniqueness**, at the blueprint's own constants. -/
theorem codeExponent_system_inj {ν j ν' j' : ℕ} (hj : j < D.codeL)
    (hj' : j' < D.codeL)
    (h : codeExponent D.codeK ν j = codeExponent D.codeK ν' j') :
    ν = ν' ∧ j = j' :=
  codeExponent_inj D.codeL_lt_codeK hj hj' h

/-- The source's target-word assignment. -/
def srcAvatar (i : Fin D.srcPres.card) : RouterFree :=
  FreeGroup.mk (D.srcAvatarWord i)

/-- The partner's target-word assignment. -/
def parAvatar (k : Fin D.parPres.card) : RouterFree :=
  FreeGroup.mk (D.parAvatarWord k)

/-! ### The designated words, after padding -/

/-- The `k`-th designated defect word. -/
def basisWord (k : Fin 2) : List (Fin D.src.pres.card × Bool) :=
  if k = 0 then D.src.basisOneWord else D.src.basisTwoWord

/-- The zeroth designated defect word. -/
theorem basisWord_zero : D.basisWord 0 = D.src.basisOneWord := by
  simp [basisWord]

/-- The first designated defect word. -/
theorem basisWord_one : D.basisWord 1 = D.src.basisTwoWord := by
  simp [basisWord]

/-- The first designated defect element. -/
def basisOne : FreeGroup (Fin D.srcPres.card) :=
  FreeGroup.mk D.src.basisOneWord

/-- The second designated defect element. -/
def basisTwo : FreeGroup (Fin D.srcPres.card) :=
  FreeGroup.mk D.src.basisTwoWord

/-- The protected word. -/
def protectedWord : FreeGroup (Fin D.srcPres.card) :=
  FreeGroup.mk D.src.protectedSrcWord

/-- The first designated element lies in the defect. -/
theorem basisOne_mem : D.srcPres.hom D.basisOne ∈ N := D.src.basisOne_mem

/-- The second designated element lies in the defect. -/
theorem basisTwo_mem : D.srcPres.hom D.basisTwo ∈ N := D.src.basisTwo_mem

/-- The protected word names the protected element. -/
theorem protectedWord_spec : D.srcPres.hom D.protectedWord = s :=
  D.src.protectedSrcWord_spec

/-- The avatar of the `k`-th designated defect element. -/
def defectAvatarWord (k : Fin 2) : List (Fin 2 × Bool) :=
  avatarSubst D.srcAvatarWord (D.basisWord k)

/-- The defect avatars, as free-group elements. -/
def defectAvatar (k : Fin 2) : RouterFree :=
  FreeGroup.mk (D.defectAvatarWord k)

/-- The defect avatars spell the source avatars of the designated elements. -/
theorem mk_defectAvatarWord (k : Fin 2) :
    FreeGroup.mk (D.defectAvatarWord k)
      = FreeGroup.lift D.srcAvatar (FreeGroup.mk (D.basisWord k)) :=
  (lift_mk_eq_mk_avatarSubst D.srcAvatarWord D.srcAvatar (fun _ => rfl) _).symm

/-- The zeroth defect avatar is the source avatar of the first designated
defect element. -/
theorem defectAvatar_zero :
    D.defectAvatar 0 = FreeGroup.lift D.srcAvatar D.basisOne := by
  show FreeGroup.mk (D.defectAvatarWord 0) = FreeGroup.lift D.srcAvatar D.basisOne
  rw [D.mk_defectAvatarWord, D.basisWord_zero]
  rfl

/-- The first defect avatar is the source avatar of the second designated
defect element. -/
theorem defectAvatar_one :
    D.defectAvatar 1 = FreeGroup.lift D.srcAvatar D.basisTwo := by
  show FreeGroup.mk (D.defectAvatarWord 1) = FreeGroup.lift D.srcAvatar D.basisTwo
  rw [D.mk_defectAvatarWord, D.basisWord_one]
  rfl

/-! ### The relator family -/

/-- `R_E`: the source relators, rewritten through the source avatars.  Positive,
because the relators are and the avatars are. -/
def srcRelators : Set (List (Fin 2 × Bool)) :=
  avatarSubst D.srcAvatarWord '' D.srcPres.rel

/-- `R_B`: the partner relators, rewritten through the partner avatars. -/
def parRelators : Set (List (Fin 2 × Bool)) :=
  avatarSubst D.parAvatarWord '' D.parPres.rel

/-- The defect tying relator, `y_j · T_j`.

**Why `y_j·T_j` and not the note's `y_j·T_j⁻¹`.**  Both tie `y_j` to the avatar
subgroup — the first says `y_j = T_j⁻¹`, the second `y_j = T_j`, and a subgroup
contains the inverse of each of its elements, so either serves `tieDefect`,
which quantifies over `Subgroup.closure`.  Only the first is a *positive* word,
and positivity is what makes the whole family cyclically reduced with no
normalization pass and no length loss.

The `⁻¹` form would need one letter cancelled at exactly one of its two seams —
the straight seam collides when `j = 2` and the wrap seam when `j = 1` — and
that hand-cancellation, along with the reduction theory to justify it, is what
this form avoids entirely. -/
def defectTieWord (i : Fin 2) : List (Fin 2 × Bool) :=
  [(i, true)] ++ avatarSubst D.defectAvatarWord (D.src.tieDefectWord i)

/-- The partner tying relator, `y_j · T'_j`; see `defectTieWord` for why the
inverse is on the other side of the equation. -/
def partnerTieWord (i : Fin 2) : List (Fin 2 × Bool) :=
  [(i, true)] ++ avatarSubst D.parAvatarWord (D.par.tiePartnerWord i)

/-- **The relator family** `R = R_E ∪ R_B ∪ R_tie`. -/
def relators : Set (List (Fin 2 × Bool)) :=
  D.srcRelators ∪ D.parRelators ∪
    (Set.range D.defectTieWord ∪ Set.range D.partnerTieWord)

/-- **The family is finite**, by construction: two images of finite relator
sets and two ranges over `Fin 2`. -/
theorem relators_finite : D.relators.Finite := by
  refine Set.Finite.union (Set.Finite.union ?_ ?_) (Set.Finite.union ?_ ?_)
  · exact D.srcPres.rel_finite.image (avatarSubst D.srcAvatarWord)
  · exact D.parPres.rel_finite.image (avatarSubst D.parAvatarWord)
  · exact Set.finite_range D.defectTieWord
  · exact Set.finite_range D.partnerTieWord

/-- A rewritten source relator is in the family. -/
theorem mem_relators_src {r : List (Fin D.srcPres.card × Bool)}
    (hr : r ∈ D.srcPres.rel) : avatarSubst D.srcAvatarWord r ∈ D.relators :=
  Set.mem_union_left _ (Set.mem_union_left _ ⟨r, hr, rfl⟩)

/-- A rewritten partner relator is in the family. -/
theorem mem_relators_par {r : List (Fin D.parPres.card × Bool)}
    (hr : r ∈ D.parPres.rel) : avatarSubst D.parAvatarWord r ∈ D.relators :=
  Set.mem_union_left _ (Set.mem_union_right _ ⟨r, hr, rfl⟩)

/-- A defect tying relator is in the family. -/
theorem mem_relators_defectTie (i : Fin 2) : D.defectTieWord i ∈ D.relators :=
  Set.mem_union_right _ (Set.mem_union_left _ ⟨i, rfl⟩)

/-- A partner tying relator is in the family. -/
theorem mem_relators_partnerTie (i : Fin 2) : D.partnerTieWord i ∈ D.relators :=
  Set.mem_union_right _ (Set.mem_union_right _ ⟨i, rfl⟩)

/-- The designated defect words are positive, by the convention. -/
theorem basisWord_positive : ∀ k : Fin 2, ∀ c ∈ D.basisWord k, c.2 = true :=
  Fin.forall_fin_two.mpr
    ⟨by rw [D.basisWord_zero]; exact D.src.basisOneWord_positive,
      by rw [D.basisWord_one]; exact D.src.basisTwoWord_positive⟩

/-- **The whole family is positive.**  The four pieces are: the rewrite of a
positive source relator, the rewrite of a positive partner relator, and the two
tying relators, each a positive generator letter followed by the rewrite of a
positive designated word. -/
theorem forall_positive_relators :
    ∀ r ∈ D.relators, ∀ c ∈ r, c.2 = true := by
  have hsrc : ∀ k, ∀ c ∈ D.srcAvatarWord k, c.2 = true :=
    fun k => forall_positive_avatarWord D.codeL D.codeK (k : ℕ)
  have hpar : ∀ k, ∀ c ∈ D.parAvatarWord k, c.2 = true :=
    fun k => forall_positive_avatarWord D.codeL D.codeK (D.srcPres.card + (k : ℕ))
  have hdef : ∀ k, ∀ c ∈ D.defectAvatarWord k, c.2 = true := fun k =>
    forall_positive_avatarSubst D.srcAvatarWord hsrc (D.basisWord_positive k)
  intro r hr
  simp only [relators, srcRelators, parRelators, Set.mem_union, Set.mem_image,
    Set.mem_range] at hr
  rcases hr with (⟨ρ, hρ, rfl⟩ | ⟨ρ, hρ, rfl⟩) | (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact forall_positive_avatarSubst D.srcAvatarWord hsrc (D.src.rel_positive ρ hρ)
  · exact forall_positive_avatarSubst D.parAvatarWord hpar (D.par.rel_positive ρ hρ)
  · intro c hc
    rcases List.mem_append.mp hc with hc' | hc'
    · rcases List.mem_singleton.mp hc' with rfl
      rfl
    · exact forall_positive_avatarSubst D.defectAvatarWord hdef
        (D.src.tieDefectWord_positive i) c hc'
  · intro c hc
    rcases List.mem_append.mp hc with hc' | hc'
    · rcases List.mem_singleton.mp hc' with rfl
      rfl
    · exact forall_positive_avatarSubst D.parAvatarWord hpar
        (D.par.tiePartnerWord_positive i) c hc'

/-- **Every relator is cyclically reduced** — a construction lemma, not a
hypothesis.  A positive word is cyclically reduced outright, and the family is
positive. -/
theorem relators_cyclicallyReduced :
    ∀ r ∈ D.relators, FreeGroup.IsCyclicallyReduced r :=
  AvatarMetricCheck.relators_cyclicallyReduced_of_positive D.forall_positive_relators

/-! ### Well-definedness, and the two tying fields -/

/-- **Source well-definedness.**  Literal membership: the `W`-rewrite of a
source relator *is* one of the relators, so it dies in the routed quotient.
This is the note's §4, with no combinatorics anywhere. -/
theorem srcRel_rewrite :
    ∀ r ∈ FreeGroup.mk '' D.srcPres.rel,
      FreeGroup.lift D.srcAvatar r ∈ relSubgroup D.relators := by
  rintro _ ⟨ρ, hρ, rfl⟩
  rw [lift_mk_eq_mk_avatarSubst D.srcAvatarWord D.srcAvatar (fun _ => rfl) ρ]
  exact mem_relSubgroup (D.mem_relators_src hρ)

/-- **Partner well-definedness.** -/
theorem parRel_rewrite :
    ∀ r ∈ FreeGroup.mk '' D.parPres.rel,
      FreeGroup.lift D.parAvatar r ∈ relSubgroup D.relators := by
  rintro _ ⟨ρ, hρ, rfl⟩
  rw [lift_mk_eq_mk_avatarSubst D.parAvatarWord D.parAvatar (fun _ => rfl) ρ]
  exact mem_relSubgroup (D.mem_relators_par hρ)

/-- A defect tying relator spells `y_j · T_j`. -/
theorem mk_defectTieWord (i : Fin 2) :
    FreeGroup.mk (D.defectTieWord i)
      = FreeGroup.of i *
        FreeGroup.mk (avatarSubst D.defectAvatarWord (D.src.tieDefectWord i)) :=
  FreeGroup.mul_mk.symm

/-- A partner tying relator spells `y_j · T'_j`. -/
theorem mk_partnerTieWord (i : Fin 2) :
    FreeGroup.mk (D.partnerTieWord i)
      = FreeGroup.of i *
        FreeGroup.mk (avatarSubst D.parAvatarWord (D.par.tiePartnerWord i)) :=
  FreeGroup.mul_mk.symm

/-- **The defect tying field.**  Each free generator is, modulo the family, the
avatar of a designated long word in the defect pair — because that relator is
in the family. -/
theorem tieDefect (i : Fin 2) :
    ∃ v ∈ Subgroup.closure
        ({FreeGroup.lift D.srcAvatar D.basisOne,
          FreeGroup.lift D.srcAvatar D.basisTwo} : Set RouterFree),
      FreeGroup.of i * v⁻¹ ∈ relSubgroup D.relators := by
  refine ⟨(FreeGroup.mk (avatarSubst D.defectAvatarWord (D.src.tieDefectWord i)))⁻¹,
    ?_, ?_⟩
  · refine inv_mem ?_
    rw [← lift_mk_eq_mk_avatarSubst D.defectAvatarWord D.defectAvatar (fun _ => rfl)]
    refine FreeGroup.range_lift_le (f := D.defectAvatar) ?_
      (MonoidHom.mem_range.mpr ⟨FreeGroup.mk (D.src.tieDefectWord i), rfl⟩)
    refine Set.range_subset_iff.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · rw [D.defectAvatar_zero]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [D.defectAvatar_one]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rw [inv_inv, ← D.mk_defectTieWord]
    exact mem_relSubgroup (D.mem_relators_defectTie i)

/-- **The partner tying field.** -/
theorem tiePartner (i : Fin 2) :
    ∃ v ∈ Subgroup.closure (Set.range D.parAvatar),
      FreeGroup.of i * v⁻¹ ∈ relSubgroup D.relators := by
  refine ⟨(FreeGroup.mk (avatarSubst D.parAvatarWord (D.par.tiePartnerWord i)))⁻¹,
    ?_, ?_⟩
  · refine inv_mem ?_
    rw [← lift_mk_eq_mk_avatarSubst D.parAvatarWord D.parAvatar (fun _ => rfl),
      ← FreeGroup.range_lift_eq_closure]
    exact MonoidHom.mem_range.mpr ⟨FreeGroup.mk (D.par.tiePartnerWord i), rfl⟩
  · rw [inv_inv, ← D.mk_partnerTieWord]
    exact mem_relSubgroup (D.mem_relators_partnerTie i)

/-! ### The obligations, and the design -/

/-- **The word-level verification obligations.**  Everything the family's
construction does not decide, and nothing else.  A sibling module proves these
against the explicit family; here they are named hypotheses in the library's
data-not-axiom style.

The metric field is at the design's own constant `C'(1/8)`, not at the `1/6`
the landed structure stores: monotonicity runs `C'(1/8) → C'(1/6)` and never
the reverse, so one `C'(1/8)` proof serves both the landed field and the sharp
gate call. -/
structure Obligations : Prop where
  /-- No relator is a proper power: a period would translate the strictly
  increasing exponent sequence onto itself (§2(c)). -/
  relators_noProperPower : NoProperPower D.relators
  /-- The metric condition at the design's constant `C'(1/8)` (§2(b)). -/
  metric_eighth : MetricSmallCancellation D.relators (1 / 8)
  /-- The protected avatar is nontrivial in the free group. -/
  protectedWord_ne_one : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1
  /-- The protected ball condition (§2(d)): twice the protected avatar fits
  inside every symmetrized relator. -/
  protectedBall : ∀ r ∈ symmetrization D.relators,
    2 * FreeGroup.norm (FreeGroup.lift D.srcAvatar D.protectedWord) ≤ r.length

/-- **Three of the four obligations, from the sibling check bundle.**
`Sofic.AvatarMetricCheck` proves the metric condition at `C'(1/8)`, the
no-proper-power clause and the protected ball against its own
`AvatarMetricData`; feeding it this family's relators discharges those three,
leaving only nontriviality of the protected avatar.  The protected avatar's
length bound is the numeric input its ball argument asks for. -/
theorem obligations_of_metricData (C : AvatarMetricCheck.AvatarMetricData)
    (hrel : D.relators = C.relators)
    (hne : FreeGroup.lift D.srcAvatar D.protectedWord ≠ 1)
    (hlen : FreeGroup.norm (FreeGroup.lift D.srcAvatar D.protectedWord)
      ≤ C.protectedLength) :
    D.Obligations where
  relators_noProperPower := by
    rw [hrel]
    exact C.noProperPower
  metric_eighth := by
    rw [hrel]
    exact C.metric_eighth
  protectedWord_ne_one := hne
  protectedBall := by
    rw [hrel]
    exact C.protectedBall_field hlen

/-- **The design, assembled.**  Every field derivable from the family's
construction is filled here — finiteness, cyclic reducedness, both
presentations, both well-definedness clauses, both tying clauses, the
designated elements and the protected word — and the four remaining word-level
checks are the single hypothesis.

The `metric` field is `C'(1/6)`, obtained from the obligations' `C'(1/8)` by
`metricSmallCancellation_mono`. -/
noncomputable def design (H : D.Obligations) : RouterRelatorDesign E N s B where
  relators := D.relators
  relators_finite := D.relators_finite
  relators_cyclicallyReduced := D.relators_cyclicallyReduced
  relators_noProperPower := H.relators_noProperPower
  metric := metricSmallCancellation_mono (lam := 1 / 8) (lam' := 1 / 6)
    (by norm_num) H.metric_eighth
  srcCard := D.srcPres.card
  srcHom := D.srcPres.hom
  srcHom_surjective := D.srcPres.hom_surjective
  srcRel := FreeGroup.mk '' D.srcPres.rel
  srcHom_ker_le := D.srcPres.ker_le
  W := D.srcAvatar
  srcRel_rewrite := D.srcRel_rewrite
  parCard := D.parPres.card
  parHom := D.parPres.hom
  parHom_surjective := D.parPres.hom_surjective
  parRel := FreeGroup.mk '' D.parPres.rel
  parHom_ker_le := D.parPres.ker_le
  U := D.parAvatar
  parRel_rewrite := D.parRel_rewrite
  basisOne := D.basisOne
  basisTwo := D.basisTwo
  basisOne_mem := D.basisOne_mem
  basisTwo_mem := D.basisTwo_mem
  tieDefect := D.tieDefect
  tiePartner := D.tiePartner
  protectedWord := D.protectedWord
  protectedWord_spec := D.protectedWord_spec
  protectedWord_ne_one := H.protectedWord_ne_one
  protectedBall := H.protectedBall

/-- **The routed data**, from the blueprint's obligations and the sharp gate.
The same `C'(1/8)` proof that fills the design's `metric` field at `1/6` is
what `router_conclusions_of_sharpGate` consumes. -/
noncomputable def routingData [N.Normal] (H : D.Obligations)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    RoutingLemmaData E N s B :=
  (D.design H).routerData_of_sharpGate hgate (le_refl ((1 : ℚ) / 8)) H.metric_eighth

/-- Whoever exhibits a blueprint whose obligations hold has discharged the
frozen endpoint's single hypothesis at that source, defect, protected element
and partner — modulo the gate, and nothing else. -/
theorem nonempty_routingLemmaData [N.Normal] (H : D.Obligations)
    (hgate : GreendlingerFreeGate.SharpGreendlingerGate (Fin 2)) :
    Nonempty (RoutingLemmaData E N s B) :=
  ⟨D.routingData H hgate⟩

end Blueprint

/-! ## 5.  The certified partner -/

/-- A word presentation of the certified torsion-free Kazhdan partner `Γ(3)`,
extracted by choice from `gamma3Partner`'s `finitelyPresented` field.  Nothing
here is assumed: `gamma3_finitelyPresented` is the P13 descent together with
the in-repo Reidemeister--Schreier theorem. -/
noncomputable def gamma3WordPresentation :
    WordPresentation CongruenceSubgroup.gamma3Partner.B :=
  wordPresentation _

/-- The partner side of a blueprint, over the certified partner.  The caller
supplies the two designated long partner words and the two positivity facts:
`gamma3WordPresentation` is an arbitrary choice of presentation, so its
relators are not positive on the nose and the positivity convention has to be
established for it — by the same `x̄` Tietze move `SourceData` documents. -/
noncomputable def gamma3PartnerData
    (hpos : ∀ r ∈ gamma3WordPresentation.rel, ∀ c ∈ r, c.2 = true)
    (tie : Fin 2 → List (Fin gamma3WordPresentation.card × Bool))
    (htie : ∀ i, ∀ c ∈ tie i, c.2 = true) :
    PartnerData CongruenceSubgroup.gamma3Partner.B where
  pres := gamma3WordPresentation
  rel_positive := hpos
  tiePartnerWord := tie
  tiePartnerWord_positive := htie

end AvatarWordFamily
end BespokeRouter
end GroupApproximation
