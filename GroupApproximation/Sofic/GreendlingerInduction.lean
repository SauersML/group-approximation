import GroupApproximation.Sofic.GreendlingerRegime

/-!
# What is left: expressions with three or more factors

`GreendlingerRegime` closes the gate for every element whose expressions can be
taken with at most two conjugate factors, with no hypotheses left over.  This
file states exactly what remains, and proves the structural facts the remaining
induction runs on.

## The two structural facts

Minimality is *hereditary* in the two ways the induction needs.

* `IsMinimalConjExpr.tail` --- the tail of a minimal expression is a minimal
  expression for what it spells.  Otherwise, replacing it and putting the head
  back would shorten the whole.
* `IsMinimalConjExpr.leadingPair` --- the two leading factors form a minimal
  expression for *their* product.  Otherwise, replacing them and keeping the
  tail would shorten the whole.

The second is what makes everything proved about two factors apply to the front
of an expression of any length: the leading pair of a minimal expression is
itself minimal, so `GreendlingerRegime`'s analysis --- the swallowing bounds, the
piece identification, the coincidence --- applies to it verbatim.

## The strengthening the induction needs

Multiplying by another factor eats a prefix of the word, and can eat a
relator's worth of it.  So the conclusion "some subword is more than half of a
relator" does not survive the induction: the surviving relator can be exactly
the one the next factor destroys.  What does survive is the *two-piece*
conclusion --- **two disjoint** such subwords --- because a prefix cancellation
can only reach the first of them.  That is what Greendlinger's lemma actually
proves, and classically it is proved from a reduced diagram: a simply-connected
reduced diagram with at least two regions has at least two regions meeting the
boundary in more than half their own boundary.

`TwoPieceConclusion` states it, `greendlinger_of_twoPieceConclusion` shows it is
stronger than what the gate asks, and
`greendlingerConclusion_of_greendlingerTwoPiece` runs the base cases: the gate
follows from the two-piece statement for expressions with at least two factors.
`greendlingerConclusion_of_three_factor` records the sharper reduction this
development reaches: only expressions with **three or more** factors are still
open.

Depends on `C'(1/6)` exactly where `GreendlingerRegime` does.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Minimality is hereditary -/

theorem conjValid_append {R : Set (List (α × Bool))}
    {e₁ e₂ : List (FreeGroup α × List (α × Bool))}
    (h₁ : ConjValid R e₁) (h₂ : ConjValid R e₂) : ConjValid R (e₁ ++ e₂) := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact h₁ x h
  · exact h₂ x h

/-- **The tail of a minimal expression is minimal.**  A shorter or lighter
expression for what the tail spells would, with the head put back, shorten or
lighten the whole. -/
theorem IsMinimalConjExpr.tail [DecidableEq α] {R : Set (List (α × Bool))}
    {x : FreeGroup α × List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (h : IsMinimalConjExpr R (x :: e) g) :
    IsMinimalConjExpr R e (conjEval e) := by
  obtain ⟨hv, heq, hlen, hw⟩ := h
  obtain ⟨hx, hvt⟩ := conjValid_cons_iff.mp hv
  refine ⟨hvt, rfl, ?_, ?_⟩
  · intro e' hv' he'
    have hb := hlen (x :: e') (conjValid_cons_iff.mpr ⟨hx, hv'⟩) (by
      rw [conjEval_cons' x, he', ← conjEval_cons' x]
      exact heq)
    rw [List.length_cons, List.length_cons] at hb
    omega
  · intro e' hv' he' hlen'
    have hb := hw (x :: e') (conjValid_cons_iff.mpr ⟨hx, hv'⟩) (by
      rw [conjEval_cons' x, he', ← conjEval_cons' x]
      exact heq) (by rw [List.length_cons, List.length_cons, hlen'])
    obtain ⟨c, s⟩ := x
    rw [conjWeight_cons, conjWeight_cons] at hb
    omega

/-- **The leading pair of a minimal expression is minimal** for its own product.
This is what carries every two-factor result to the front of an expression of
any length. -/
theorem IsMinimalConjExpr.leadingPair [DecidableEq α]
    {R : Set (List (α × Bool))} {A B : FreeGroup α} {a b : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (h : IsMinimalConjExpr R ((A, a) :: (B, b) :: e) g) :
    IsMinimalConjExpr R [(A, a), (B, b)]
      (A * FreeGroup.mk a * A⁻¹ * (B * FreeGroup.mk b * B⁻¹)) := by
  obtain ⟨hv, heq, hlen, hw⟩ := h
  obtain ⟨ha, hv1⟩ := conjValid_cons_iff.mp hv
  obtain ⟨hb, hv2⟩ := conjValid_cons_iff.mp hv1
  have hpair : conjEval [(A, a), (B, b)]
      = A * FreeGroup.mk a * A⁻¹ * (B * FreeGroup.mk b * B⁻¹) := by
    rw [conjEval_cons, conjEval_cons, conjEval_nil, mul_one]
  refine ⟨conjValid_cons_iff.mpr ⟨ha, conjValid_cons_iff.mpr ⟨hb,
    conjValid_nil R⟩⟩, hpair, ?_, ?_⟩
  · intro e' hv' he'
    by_contra hcon
    push_neg at hcon
    have hval : ConjValid R (e' ++ e) := conjValid_append hv' hv2
    have heval : conjEval (e' ++ e) = g := by
      rw [conjEval_append, he', ← hpair, ← conjEval_append]
      have hb2 : conjEval ([(A, a), (B, b)] ++ e)
          = conjEval ((A, a) :: (B, b) :: e) := by
        rfl
      rw [hb2]
      exact heq
    have hb3 := hlen (e' ++ e) hval heval
    rw [List.length_append] at hb3
    simp only [List.length_cons, List.length_nil] at hb3 hcon
    omega
  · intro e' hv' he' hlen'
    by_contra hcon
    push_neg at hcon
    have hval : ConjValid R (e' ++ e) := conjValid_append hv' hv2
    have heval : conjEval (e' ++ e) = g := by
      rw [conjEval_append, he', ← hpair, ← conjEval_append]
      have hb2 : conjEval ([(A, a), (B, b)] ++ e)
          = conjEval ((A, a) :: (B, b) :: e) := by
        rfl
      rw [hb2]
      exact heq
    have hb3 := hw (e' ++ e) hval heval (by
      rw [List.length_append, hlen']
      simp)
    rw [conjWeight_append] at hb3
    have hb4 : conjWeight ((A, a) :: (B, b) :: e)
        = conjWeight [(A, a), (B, b)] + conjWeight e := by
      simp only [conjWeight_cons, conjWeight_nil]
      omega
    rw [hb4] at hb3
    omega

/-! ## The strengthening the induction needs -/

/-- **Two disjoint pieces.**  The word splits so that two of its blocks are each
more than half of a symmetrized relator.  This is what Greendlinger's lemma
proves for a reduced diagram with at least two regions, and --- unlike the
one-piece conclusion --- it survives multiplication by another factor, because a
prefix cancellation can only reach the first of the two. -/
def TwoPieceConclusion (R : Set (List (α × Bool))) (w : List (α × Bool)) : Prop :=
  ∃ A u₁ B u₂ C : List (α × Bool),
    w = A ++ u₁ ++ B ++ u₂ ++ C ∧
      (∃ r₁ ∈ symmetrization R, u₁ <+: r₁ ∧ r₁.length < 2 * u₁.length) ∧
      (∃ r₂ ∈ symmetrization R, u₂ <+: r₂ ∧ r₂.length < 2 * u₂.length)

/-- The two-piece conclusion is stronger than what the gate asks. -/
theorem greendlinger_of_twoPieceConclusion {R : Set (List (α × Bool))}
    {w : List (α × Bool)} (h : TwoPieceConclusion R w) :
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: r ∧ r.length < 2 * u.length := by
  obtain ⟨A, u₁, B, u₂, C, hw, ⟨r₁, hr₁, hpre, hlt⟩, -⟩ := h
  refine ⟨r₁, hr₁, u₁, ?_, hpre, hlt⟩
  refine ⟨A, B ++ u₂ ++ C, ?_⟩
  rw [hw]
  simp only [List.append_assoc]

/-- **The strengthened gate**: every reduced word whose shortest expression has
at least two factors has two disjoint pieces. -/
def GreendlingerTwoPiece (R : Set (List (α × Bool))) : Prop :=
  ∀ w : List (α × Bool), FreeGroup.IsReduced w → ∀ n : ℕ, 2 ≤ n →
    IsMinimalConjProduct R n (FreeGroup.mk w) → TwoPieceConclusion R w

/-- **The strengthened gate implies the gate.**  The base cases are already
closed: none is impossible for a nonempty reduced word, and one is the
one-relator case. -/
theorem greendlingerConclusion_of_greendlingerTwoPiece [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (h : GreendlingerTwoPiece R) : GreendlingerConclusion R := by
  intro w hw hwne hmem
  obtain ⟨n, hmin⟩ :=
    exists_isMinimalConjProduct_of_mem_normalClosure R (FreeGroup.mk w) hmem
  rcases n with _ | _ | n
  · exact absurd hmin.1 (not_isConjProduct_zero hw hwne)
  · exact greendlinger_of_isConjProduct_one hR hRne hw hmin.1
  · exact greendlinger_of_twoPieceConclusion (h w hw (n + 1 + 1) (by omega) hmin)

/-- **What is still open, sharply.**  The gate follows from the case of three or
more factors alone: everything below it is proved.

This is the reduction `GreendlingerRegime` buys.  The remaining input is the
induction classical treatments run on a reduced van Kampen diagram, and the
structural facts it needs --- that the tail and the leading pair of a minimal
expression are themselves minimal --- are proved above. -/
theorem greendlingerConclusion_of_three_factor [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (h : ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
      ∀ n : ℕ, 3 ≤ n → IsMinimalConjProduct R n (FreeGroup.mk w) →
        ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
          u <:+: w ∧ u <+: r ∧ r.length < 2 * u.length) :
    GreendlingerConclusion R := by
  intro w hw hwne hmem
  obtain ⟨n, hmin⟩ :=
    exists_isMinimalConjProduct_of_mem_normalClosure R (FreeGroup.mk w) hmem
  rcases le_or_gt n 2 with hle | hgt
  · exact greendlinger_of_le_two_factors hR hRne hmetric hw hwne hle hmin.1
  · exact h w hw hwne n (by omega) hmin

end SmallCancellationRouter
end GroupApproximation
