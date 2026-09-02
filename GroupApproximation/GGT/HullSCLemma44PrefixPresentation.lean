import GroupApproximation.GGT.HullSCLemma44PrefixRelGenSet

/-!
# A strongly bounded prefix presentation for Hull's Lemma 4.4

Hull's definition of a strongly bounded relative presentation has two parts:
the relator lengths have a uniform bound, and only finitely many peripheral
letters occur.  The repository's `IsLemma44Input.stronglyBounded` field
expresses the second part for the original family `W`; the lengths of words in
`W` need not have a common upper bound.

The prefix quotient base repairs the first part.  Each step along a word in
`W` gives a triangular relation between two prefix generators and the original
relative letter.  These relations all have length three.  Their only
peripheral letter is the image of the original step, so finite peripheral
support follows from `IsLemma44Input.stronglyBounded`.

This file packages those facts independently of a combinatorial-map model.
The later relative-isoperimetric bridge can use
`StronglyBoundedIdentityRelations` as the bounded presentation input while the
van Kampen lane remains responsible only for diagram realization and the
Greendlinger certificate.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

/-! ## Prefix triangles as a relation family -/

/-- All consecutive-prefix triangles coming from the relator family `W`. -/
def RelWord.prefixTriangles
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) (q : G →* Q) :
    Set (List (GGT.RelLetter Q Lambda)) :=
  {triangle | ∃ word ∈ W,
    ∃ pre a suffix, word = pre ++ a :: suffix ∧
      triangle =
        GGT.RelGenSet.prefixTriangle q pre a}

/-- Membership in the prefix-triangle family, with every part displayed. -/
theorem RelWord.mem_prefixTriangles
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    {triangle : List (GGT.RelLetter Q Lambda)} :
    triangle ∈ RelWord.prefixTriangles W q ↔
      ∃ word ∈ W, ∃ pre a suffix, word = pre ++ a :: suffix ∧
        triangle =
          GGT.RelGenSet.prefixTriangle q pre a :=
  Iff.rfl

/-- The empty relator family has no prefix triangles. -/
@[simp] theorem RelWord.prefixTriangles_empty
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) :
    RelWord.prefixTriangles
      (∅ : Set (List (GGT.RelLetter G Lambda))) q = ∅ := by
  ext triangle
  constructor
  · rintro ⟨word, hword, pre, a, suffix, hsplit, htriangle⟩
    exact hword.elim
  · intro htriangle
    exact htriangle.elim

/-- Every relation in the prefix-triangle family has length exactly three. -/
theorem RelWord.length_eq_three_of_mem_prefixTriangles
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    {triangle : List (GGT.RelLetter Q Lambda)}
    (htriangle : triangle ∈ RelWord.prefixTriangles W q) :
    triangle.length = 3 := by
  obtain ⟨word, hword, pre, a, suffix, hsplit, rfl⟩ := htriangle
  exact GGT.RelGenSet.prefixTriangle_length q pre a

/-- Every prefix-triangle relation spells the identity. -/
theorem RelWord.listVal_eq_one_of_mem_prefixTriangles
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    {triangle : List (GGT.RelLetter Q Lambda)}
    (htriangle : triangle ∈ RelWord.prefixTriangles W q) :
    GGT.RelLetter.listVal triangle = 1 := by
  obtain ⟨word, hword, pre, a, suffix, hsplit, rfl⟩ := htriangle
  exact GGT.RelGenSet.listVal_prefixTriangle q pre a

/-- Prefix triangles are admissible over the quotient prefix relative
generating set. -/
theorem RelWord.admissible_of_mem_prefixTriangles
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    {triangle : List (GGT.RelLetter Q Lambda)}
    (htriangle : triangle ∈ RelWord.prefixTriangles W q) :
    RelWord.IsAdmissible (D.prefixQuotient W hsc q hq) triangle := by
  obtain ⟨word, hword, pre, a, suffix, hsplit, rfl⟩ := htriangle
  exact GGT.RelGenSet.prefixTriangle_admissible hsc q hq hword hsplit

/-! ## Peripheral support -/

/-- Peripheral letters occurring in a relative relation family. -/
def RelWord.componentSupport
    {G : Type u} {Lambda : Type w}
    (V : Set (List (GGT.RelLetter G Lambda))) :
    Set (GGT.RelLetter G Lambda) :=
  {a | (∃ lam h, a = GGT.RelLetter.comp lam h) ∧
    ∃ word ∈ V, a ∈ word}

/-- The `stronglyBounded` field of the Lemma 4.4 input is exactly finiteness
of the component-support set. -/
theorem RelWord.componentSupport_finite_of_lemma44Input
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho) :
    (RelWord.componentSupport W).Finite :=
  hsc.stronglyBounded

/-- A component letter in a prefix triangle is the mapped middle letter; the
two prefix endpoint letters are base letters. -/
theorem RelWord.componentSupport_prefixTriangles_subset
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) (q : G →* Q) :
    RelWord.componentSupport (RelWord.prefixTriangles W q) ⊆
      GGT.RelLetter.mapHom q '' RelWord.componentSupport W := by
  rintro b ⟨⟨lam, h, hb⟩, triangle, htriangle, hbtriangle⟩
  subst b
  obtain ⟨word, hword, pre, a, suffix, hsplit, rfl⟩ := htriangle
  simp only [GGT.RelGenSet.prefixTriangle, List.mem_cons,
    List.not_mem_nil, or_false] at hbtriangle
  rcases hbtriangle with hfirst | hmiddle | hlast
  · cases hfirst
  · cases a with
    | base x => cases hmiddle
    | comp lam' x =>
        have haWord : GGT.RelLetter.comp lam' x ∈ word := by
          rw [hsplit]
          simp
        refine ⟨GGT.RelLetter.comp lam' x, ?_, ?_⟩
        · exact ⟨⟨lam', x, rfl⟩, word, hword, haWord⟩
        · exact hmiddle.symm
  · cases hlast

/-- Finite source component support gives finite component support for all
prefix triangles. -/
theorem RelWord.componentSupport_prefixTriangles_finite
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) :
    (RelWord.componentSupport (RelWord.prefixTriangles W q)).Finite := by
  exact (hsc.stronglyBounded.image (GGT.RelLetter.mapHom q)).subset
    (RelWord.componentSupport_prefixTriangles_subset W q)

/-! ## Packaged bounded relations -/

/-- A relative relation family with a uniform length bound, finite peripheral
support, legal letters, and identity values. -/
structure StronglyBoundedIdentityRelations
    {Q : Type v} [Group Q] {Lambda : Type w}
    (E : GGT.RelGenSet Q Lambda) where
  relators : Set (List (GGT.RelLetter Q Lambda))
  lengthBound : ℕ
  admissible : ∀ word ∈ relators, RelWord.IsAdmissible E word
  value_one : ∀ word ∈ relators, GGT.RelLetter.listVal word = 1
  length_le : ∀ word ∈ relators, word.length ≤ lengthBound
  componentSupport_finite : (RelWord.componentSupport relators).Finite

/-- Prefix triangles form a strongly bounded identity-relation family at
uniform bound three. -/
def prefixTriangleRelations
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q) :
    StronglyBoundedIdentityRelations
      (D.prefixQuotient W hsc.toIsSmallCancellation q hq) where
  relators := RelWord.prefixTriangles W q
  lengthBound := 3
  admissible := fun word hword =>
    RelWord.admissible_of_mem_prefixTriangles hsc.toIsSmallCancellation
      q hq hword
  value_one := fun word hword =>
    RelWord.listVal_eq_one_of_mem_prefixTriangles hword
  length_le := fun word hword => by
    rw [RelWord.length_eq_three_of_mem_prefixTriangles hword]
  componentSupport_finite :=
    RelWord.componentSupport_prefixTriangles_finite hsc q

namespace StronglyBoundedIdentityRelations

/-- The packaged prefix family exposes its sharp uniform bound. -/
@[simp] theorem prefixTriangleRelations_lengthBound
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q) :
    (prefixTriangleRelations D W hsc q hq).lengthBound = 3 := rfl

/-- In the empty-family case the packaged relation set is empty. -/
@[simp] theorem prefixTriangleRelations_empty_relators
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D
      (∅ : Set (List (GGT.RelLetter G Lambda))) eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q) :
    (prefixTriangleRelations D ∅ hsc q hq).relators = ∅ := by
  exact RelWord.prefixTriangles_empty q

end StronglyBoundedIdentityRelations

end HullSC
end GroupApproximation
