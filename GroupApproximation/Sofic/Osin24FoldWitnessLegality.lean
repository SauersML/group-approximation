import GroupApproximation.Sofic.SmallCancellationRouter

/-!
# The fold obstruction is legal: `C'(λ)` does not exclude it, and minimality does

`Sofic/MatchingFoldObstruction.lean` exhibits six positions on which the naive
fold fails to be non-crossing, and leaves the decisive question open in its own
header: "either the configuration has to be excluded -- by minimality, or by the
metric condition, or by some property of the expression not yet spent -- or the
fold has to be performed together with the reordering of the boundary walk".

This module answers it.  **The metric condition does not exclude it**, and the
reason is one line: a family of one-letter relators satisfies `C'(λ)` at every
positive `λ`, vacuously, because a nonempty piece would be a common prefix of
two distinct one-letter words.  That is `metricSmallCancellation_of_length_one`
below, and it is what makes the witness's one-letter relator block legal.

## The instance, in full

Over `Fin 3`, write `u = (0, true)`, `q = (1, true)`, `z = (2, true)`.  Take

    R = {[u], [q], [z]}

whose symmetrization is the six one-letter words, all cyclically reduced
(`foldWitnessFamily_cyclicallyReduced`), satisfying `C'(1/6)`
(`foldWitnessFamily_metric`).  Take the expression

    e = [([], [u]), ([], [q⁻¹]), ([], [u⁻¹]), ([u], [q]), ([], [z])]

-- `ConjValid` holds, since `ConjValid` asks only that each relator lie in the
*symmetrization* -- and `w = [z]`, which is reduced and nonempty.  Then

    conjEval e = u · q⁻¹ · u⁻¹ · (u q u⁻¹) · z = z = FreeGroup.mk w,

and `labelledWord e w` is the eight-letter word

    0:u(rel)  1:q⁻¹(rel)  2:u⁻¹(rel)  3:u(conj)  4:q(rel)  5:u⁻¹(stem)
    6:z(rel)  7:z⁻¹(boundary)

whose free-cancellation matching is `(2,3), (1,4), (0,5), (6,7)` -- nested,
non-crossing, perfect.  The fourth factor has a one-letter relator block and a
one-letter conjugator, so its mirror pair is `(3,5)` and it brackets exactly
position `4`: the witness's configuration, on the nose.

The point the first attempt at this instance misses is the **empty
conjugators**.  With `c = []` a factor contributes only a relator block, so the
letters at `0`, `1`, `2` are relator letters rather than stem letters -- and the
transfer `2 —matched→ 3 —mirror→ 5 —matched→ 0` therefore joins two *relator*
letters, producing the pair `(0,2)`, which straddles the surviving
relator-to-relator pair `(1,4)` since `0 < 1 < 2 < 4`.  With nonempty
conjugators the same path closes into a cycle and no straddle appears.

## What excludes it, and what that means for the fold

Minimality, and nothing else.  `conjEval e = z` has the one-factor expression
`[([], [z])]`, so `e` is not shortest.  More sharply, the already-landed
pairwise lemma fires: with `A = ([], [q⁻¹])`, the factor between them
`B = [([], [u⁻¹])]`, and `D = ([u], [q])`,

    (conjEval B)⁻¹ * factorValue A * conjEval B * factorValue D
      = u · q⁻¹ · u⁻¹ · u q u⁻¹ = 1,

which is exactly what `MinimalNoCancellingPair.ne_inv_conj_of_minimal` forbids.

So the fold is **not** dead, and the next question is sharp: does pairwise
non-cancellation exclude *every* straddling transfer, or only those in which the
cancelling region is a union of whole factors?  The instance below is of the
second kind, and a configuration in which the region begins inside a relator
block and ends inside a stem block is not touched by the pairwise lemma.

Everything in this module is about the family.  The expression, the matching and
the minimality failure above are a seven-letter computation, recorded here and
not formalized.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  One-letter relators are legal -/

/-- A one-letter word is cyclically reduced: it is reduced, and its last letter
is its first. -/
theorem isCyclicallyReduced_of_singleton (a : α × Bool) :
    FreeGroup.IsCyclicallyReduced [a] := by
  refine ⟨FreeGroup.IsReduced.singleton, ?_⟩
  intro x hx b hb _
  rw [List.getLast?_singleton, Option.mem_some_iff] at hx
  rw [List.head?_cons, Option.mem_some_iff] at hb
  subst hx
  subst hb
  rfl

/-- Every member of the symmetrization of a family of one-letter words is a
one-letter word: rotation and formal inversion both preserve length. -/
theorem length_eq_one_of_mem_symmetrization {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, r.length = 1) {w : List (α × Bool)}
    (hw : w ∈ symmetrization R) : w.length = 1 := by
  obtain ⟨r, hr, n, hcase⟩ := hw
  rcases hcase with rfl | rfl
  · rw [List.length_rotate]
    exact hR r hr
  · rw [List.length_rotate, FreeGroup.invRev_length]
    exact hR r hr

/-- **A family of one-letter relators has no nonempty piece.**  A nonempty piece
is a prefix of two one-letter words, hence equal to both, hence they are not
distinct. -/
theorem eq_nil_of_isPiece_of_length_one {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, r.length = 1) {p : List (α × Bool)}
    (hp : IsPiece (symmetrization R) p) : p = [] := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hne, hp₁, hp₂⟩ := hp
  by_contra hpne
  have h1 : w₁.length = 1 := length_eq_one_of_mem_symmetrization hR hw₁
  have h2 : w₂.length = 1 := length_eq_one_of_mem_symmetrization hR hw₂
  have hpos : 0 < p.length := List.length_pos_iff.mpr hpne
  have hle := hp₁.length_le
  have he₁ : p = w₁ := hp₁.eq_of_length (by omega)
  have he₂ : p = w₂ := hp₂.eq_of_length (by omega)
  exact hne (he₁.symm.trans he₂)

/-- **`C'(λ)` is vacuous on one-letter relators, at every positive `λ`.**

This is the reason the metric condition cannot be the hypothesis that excludes
`MatchingFoldObstruction`'s configuration: the witness's one-letter relator
block is legal in a `C'(1/6)` family, and no length floor appears anywhere in
`SharpGreendlingerGate`. -/
theorem metricSmallCancellation_of_length_one {R : Set (List (α × Bool))}
    {lam : ℚ} (hR : ∀ r ∈ R, r.length = 1) (hlam : 0 < lam) :
    MetricSmallCancellation R lam := by
  intro p hp w hw _
  rw [eq_nil_of_isPiece_of_length_one hR hp, List.length_nil,
    length_eq_one_of_mem_symmetrization hR hw]
  push_cast
  linarith

/-! ## 2.  The witness family -/

/-- The three one-letter relators of the instance in the header. -/
def foldWitnessFamily : Set (List (Fin 3 × Bool)) :=
  {[(0, true)], [(1, true)], [(2, true)]}

theorem foldWitnessFamily_length_one :
    ∀ r ∈ foldWitnessFamily, r.length = 1 := by
  rintro r (rfl | rfl | rfl) <;> rfl

/-- The witness family is cyclically reduced, as `SharpGreendlingerGate`
demands. -/
theorem foldWitnessFamily_cyclicallyReduced :
    ∀ r ∈ foldWitnessFamily, FreeGroup.IsCyclicallyReduced r := by
  rintro r (rfl | rfl | rfl) <;> exact isCyclicallyReduced_of_singleton _

/-- **The witness family satisfies `C'(1/6)`.**  So the metric condition does
not exclude the fold obstruction. -/
theorem foldWitnessFamily_metric :
    MetricSmallCancellation foldWitnessFamily (1 / 6) :=
  metricSmallCancellation_of_length_one foldWitnessFamily_length_one (by norm_num)

end SmallCancellationRouter
end GroupApproximation
