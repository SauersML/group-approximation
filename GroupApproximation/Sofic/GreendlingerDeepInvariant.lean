import GroupApproximation.Sofic.GreendlingerDeepTailWindow

/-!
# The deep branch on the weakened invariant: a window, and no offset at all

Two things had to go before the deep regime could be discharged, and they were
found separately.

`GreendlingerDeepInduction` §§7-10 removed the first: the descent no longer
demands an arc at a position measured against the **head** rotation.  Its
invariant is "for every `N ≤ |c| + i` with `6i < |t|`, the word with `N` letters
dropped carries an arc", so the deep obligation `DeepArcDrop` asks only for an
arc in `B'.drop (N − |P'|)` — position `0`, no offset.

`GreendlingerDeepTailWindow` removed the second: over a tail longer than one
factor the landing rotation is eaten from **both** ends, the head's block taking
`i` letters off the front and the landing factor's own block taking `k` off the
back, so the arc is a window `(t₃.drop i).take m` rather than a suffix, and
`greendlingerAt_of_rotation_window` produces it from `|t₃| < 2m` alone.

This file is the join.  `DeepOverrunWindow` still carries the head-denominated
offset field — `|M| + j − (|c| + |t|) ≤ |A|` — which is exactly the demand that
is unavailable once `|t| > 2|t₃|`; `DeepWindowDrop` below is the same window
statement with that field **deleted**, because on the weakened invariant the
arc is read at position `0` and the offset has nothing left to do.  What remains
is a statement about where two cancellations leave one rotation, and nothing
else:

    what survives carries a window of some symmetrized relator, longer than
    half of it.

## What is proved here

* `window_of_palindrome_take` and `window_of_palindrome_survivor` — the list
  surgery that turns "the landing factor's survivor, with `D` letters dropped"
  into the window shape the producer consumes.  This is the step
  `GreendlingerDeepTailWindow` left open; `take_drop_swap` is its pivot and
  `take_append_of_le` is proved here rather than cited, on the same principle.
* `exists_postJunction_drop` — in the deep regime the adjacent junction is empty
  (`GreendlingerDeepVacuity.not_deep_confined`), so what survives is always a
  drop of the word of the expression **after** that junction, at any tail
  length.  This is `exists_overrun_landing_drop` with the junction case
  discharged rather than assumed, and it is what lets the window be looked for
  in a factor the block is not adjacent to.
* `DeepWindowDrop`, `DeepArcDropSharp`, `DeepWindowDropSharp` and their
  discharges, and the gate over the window residual and the landing production,
  in both forms.

The relator the window comes from is existentially quantified rather than named:
the weakened invariant's context does not mention the landing factor, and the
predicate is weaker for letting its prover choose which factor pays.

## The deep branch is a landing, not an arc

Sections 6 and 7 go one step further and remove the arc obligation altogether.
The descent is already an induction, and what the deep regime leaves behind is
another expression with another block eating its front — the situation the
descent handles at every stage.  So the deep branch need not *produce* an arc:
it need only say **where the composite block stops**, and the recursion produces
the arc.

`DeepCompositeLands` is that statement, and it is a `LandsIn` — the same
predicate the landing branch already uses, at the composite block and one
junction down.  Its offset field `6i₃ < |t₃|` is exactly what
`GreendlingerDeepOverrunCount.six_mul_intrusion_lt_of_forward` proves from the
piece bound at any depth, which is why stating the residual this way is what
lets that lemma be spent.  `greendlingerAt_drop_of_lands` is the descent with
both branches landing, and its two non-trivial cases are the same computation.

Two coverage edges, since they are easy to lose.  The block that stops inside
the landing conjugator is the case `i₃ = 0`, which `LandsIn` carries in its
`N ≤ |c'| + i` field and which `drop_suffix_append` handles by truncated
subtraction.  The coincidence — the head rotation inverted being a rotation of
the landing one — is never reached here: it is spent inside the piece bound,
through `ne_rotate_invRev_of_minimal_forward`, which holds at every depth.

Depends on `C'(1/6)` only through `not_deep_confined`, where the junction kill
reads a piece bound.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  Taking past an append -/

/-- Taking fewer letters than the first block has ignores the second.  The
mirror of `GreendlingerChunks.drop_append_of_le`, proved here for the same
reason `GreendlingerDeepTailWindow.take_drop_swap` is: the window arithmetic
should not depend on a library name. -/
theorem take_append_of_le {β : Type*} :
    ∀ (n : ℕ) (l₁ l₂ : List β), n ≤ l₁.length →
      (l₁ ++ l₂).take n = l₁.take n := by
  intro n
  induction n with
  | zero =>
      intro l₁ l₂ _
      simp
  | succ n ih =>
      intro l₁ l₂ h
      cases l₁ with
      | nil =>
          rw [List.length_nil] at h
          exact absurd h (by omega)
      | cons x xs =>
          rw [List.length_cons] at h
          simp only [List.cons_append, List.take_succ_cons]
          rw [ih xs l₂ (by omega)]

/-! ## 2.  The window a two-sided cancellation leaves -/

/-- **The window, read off the palindrome.**  A palindrome truncated at `L` and
then advanced by `D` is a window of its rotation, provided the truncation has
not passed the rotation and the advance has passed the conjugator.

The two hypotheses are the two cancellations: `D` is what the head's block ate
off the front, `|c₃| + |t₃| − L` is what the landing factor's own block ate off
the back, and the window between them is what
`GreendlingerDeepTailWindow.greendlingerAt_of_rotation_window` turns into an
arc. -/
theorem window_of_palindrome_take {c₃ t₃ : List (α × Bool)} {D L : ℕ}
    (hc : c₃.length ≤ D) (hD : D ≤ L) (hL : L ≤ c₃.length + t₃.length) :
    ((palindrome c₃ t₃).take L).drop D
      = (t₃.drop (D - c₃.length)).take (L - D) := by
  have hpal : palindrome c₃ t₃ = c₃ ++ (t₃ ++ FreeGroup.invRev c₃) := by
    unfold palindrome
    rw [List.append_assoc]
  rw [take_drop_swap, hpal, drop_append_of_ge c₃ D (t₃ ++ FreeGroup.invRev c₃) hc,
    drop_append_of_le (D - c₃.length) t₃ (FreeGroup.invRev c₃) (by omega),
    take_append_of_le (L - D) (t₃.drop (D - c₃.length)) (FreeGroup.invRev c₃)
      (by rw [List.length_drop]; omega)]

/-- **The window, read off the landing factor's survivor.**  `P₃` is what the
factor keeps of its palindrome after its own cancellation, `B₃` is the rest of
the word, and `D` is where the block from above stops.  What survives is the
window, followed by everything the landing factor did not produce.

This is the shape `DeepWindowDrop` asks for, with `A = []`. -/
theorem window_of_palindrome_survivor {c₃ t₃ P₃ M₃ B₃ : List (α × Bool)} {D : ℕ}
    (heq : palindrome c₃ t₃ = P₃ ++ M₃)
    (hc : c₃.length ≤ D) (hD : D ≤ P₃.length)
    (hP : P₃.length ≤ c₃.length + t₃.length) :
    (P₃ ++ B₃).drop D
      = (t₃.drop (D - c₃.length)).take (P₃.length - D) ++ B₃ := by
  have hP₃ : (palindrome c₃ t₃).take P₃.length = P₃ := by
    rw [heq, List.take_left]
  have hstep : P₃.drop D = ((palindrome c₃ t₃).take P₃.length).drop D := by
    rw [hP₃]
  rw [drop_append_of_le D P₃ B₃ hD, hstep, window_of_palindrome_take hc hD hP]

/-! ## 3.  Past the adjacent junction, at any tail length -/

/-- **In the deep regime the survivor is a drop of the word past the junction.**

The block runs deep, so `GreendlingerDeepVacuity.not_deep_confined` says it
cannot stop inside the adjacent palindrome — the junction admits no deep
configuration at all.  Hence the overrun hypothesis of
`exists_overrun_landing_drop` is not an assumption but a theorem here, and what
survives the head's cancellation is a drop of the word of the expression after
the junction, whatever the length of that expression.

Compose with `drop_add` to move the incoming block across: the survivor
`B'.drop (N − |P'|)` is `(conjEval f).toWord.drop (D + (N − |P'|))`, and the
window is then looked for in a factor of `f`. -/
theorem exists_postJunction_drop [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c t P' M B' : List (α × Bool)} {e : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α} {i : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (ht : t ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hi : 6 * i < t.length)
    (hgt : c.length + t.length < M.length + i) :
    ∃ (c₂ t₂ : List (α × Bool)) (f : List (FreeGroup α × List (α × Bool)))
      (D : ℕ),
      t₂ ∈ symmetrization R ∧
        FreeGroup.IsReduced (palindrome c₂ t₂) ∧
        IsMinimalConjExpr R
          ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g ∧
        f.length < e.length ∧ B' = (conjEval f).toWord.drop D := by
  obtain ⟨c₂, t₂, f, ht₂, hredp₂, hmin₂, hev, hf⟩ :=
    exists_deep_tail_setup hR hRne hmin htail hlow
  rw [← hev] at htail
  by_cases hconf : FreeGroup.invRev M <+: palindrome c₂ t₂
  · exfalso
    obtain ⟨B'', hB''⟩ := hconf
    exact not_deep_confined hRne hmetric hmin₂ ht ht₂ hredp hredp₂ heq hB''.symm
      hlow hi hgt
  · obtain ⟨D, hD⟩ := exists_overrun_landing_drop hredp₂ htail hconf
    exact ⟨c₂, t₂, f, D, ht₂, hredp₂, hmin₂, hf, hD⟩

/-! ## 4.  The deep obligation as a window, with the offset deleted -/

/-- **The deep obligation, as a window.**  On the weakened invariant the arc is
read at position `0`, so all that is left to produce is a window of some
symmetrized relator, longer than half of it, inside what survives.

Compare `GreendlingerDeepTailWindow.DeepOverrunWindow`, which is this statement
plus the field `|M| + j − (|c| + |t|) ≤ |A|`: an offset denominated in the head
rotation, which is unavailable exactly when the landing rotation is the shorter
of the two (`GreendlingerDeepOverrunCount.two_mul_lt_of_relator_ratio`).  Here
that field is gone, and with it the ratio between the two rotations.

The relator is existentially quantified because the context does not name the
landing factor; a prover picks it, and `window_of_palindrome_survivor` above is
what exhibits the window once it has. -/
def DeepWindowDrop [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (N i : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → 6 * i < t.length → N ≤ c.length + i →
    c.length + t.length < M.length + i →
    ∃ (s A C : List (α × Bool)) (k m : ℕ),
      s ∈ symmetrization R ∧
        B'.drop (N - P'.length) = A ++ (s.drop k).take m ++ C ∧
        k + m ≤ s.length ∧ s.length < 2 * m

/-- **The deep branch, from the window.** -/
theorem deepArcDrop_of_deepWindowDrop [DecidableEq α]
    {R : Set (List (α × Bool))} (h : DeepWindowDrop R) : DeepArcDrop R := by
  intro c t e g P' M B' N i hmin ht hredp heq htail hlow hi hN hgt
  obtain ⟨s, A, C, k, m, hs, hsplit, hfit, hbound⟩ :=
    h c t e g P' M B' N i hmin ht hredp heq htail hlow hi hN hgt
  exact greendlingerAt_of_rotation_window hs hsplit (Nat.zero_le _) hfit hbound

/-- **The deep obligation on the weakened invariant, at the sharp constant.**
The `λ`-twin of `GreendlingerDeepInduction.DeepArcDrop`. -/
def DeepArcDropSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (N i : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (i : ℚ) < lam * (t.length : ℚ) →
    N ≤ c.length + i →
    c.length + t.length < M.length + i →
    GreendlingerAtSharp R lam 0 (B'.drop (N - P'.length))

/-- **The window obligation at the sharp constant.**  Only the window's length
bound moves; the shape is `λ`-free. -/
def DeepWindowDropSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (N i : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (i : ℚ) < lam * (t.length : ℚ) →
    N ≤ c.length + i →
    c.length + t.length < M.length + i →
    ∃ (s A C : List (α × Bool)) (k m : ℕ),
      s ∈ symmetrization R ∧
        B'.drop (N - P'.length) = A ++ (s.drop k).take m ++ C ∧
        k + m ≤ s.length ∧
        (1 - 3 * lam) * (s.length : ℚ) < (m : ℚ)

/-- **The sharp deep branch, from the sharp window.** -/
theorem deepArcDropSharp_of_deepWindowDropSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (h : DeepWindowDropSharp R lam) :
    DeepArcDropSharp R lam := by
  intro c t e g P' M B' N i hmin ht hredp heq htail hlow hi hN hgt
  obtain ⟨s, A, C, k, m, hs, hsplit, hfit, hbound⟩ :=
    h c t e g P' M B' N i hmin ht hredp heq htail hlow hi hN hgt
  exact greendlingerAtSharp_of_rotation_window hs hsplit (Nat.zero_le _) hfit
    hbound

/-- **The sharp weakened invariant, from the two branches.**  The `λ`-twin of
`GreendlingerDeepInduction.cascadeLandingDrop_of_deepArcDrop_of_landing`, with
`GreendlingerSharpTwins.LandingProductionSharp` unchanged. -/
theorem cascadeLandingDropSharp_of_deepArcDropSharp_of_landingSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hdeep : DeepArcDropSharp R lam) (hland : LandingProductionSharp R lam) :
    CascadeLandingDropSharp R lam := by
  intro c t e g P' M B' N i hmin ht hredp heq htail hlow hi hN
  rcases le_or_gt (M.length + i) (c.length + t.length) with hle | hgt
  · exact Or.inr ⟨hle,
      hland c t e g P' M B' i hmin ht hredp heq htail hlow hi hle⟩
  · exact Or.inl ((hdeep c t e g P' M B' N i hmin ht hredp heq htail hlow hi hN
      hgt).of_suffix (drop_suffix_append P' B' N))

/-! ## 5.  The gate, over the window and the landing production -/

/-- **The weakened invariant, from the window and the landing production.** -/
theorem cascadeLandingDrop_of_deepWindowDrop_of_landing [DecidableEq α]
    {R : Set (List (α × Bool))} (hwin : DeepWindowDrop R)
    (hland : LandingProduction R) : CascadeLandingDrop R :=
  cascadeLandingDrop_of_deepArcDrop_of_landing
    (deepArcDrop_of_deepWindowDrop hwin) hland

/-- **The free-group half-form gate over the window and the landing
production.**  The deep half now costs exactly one statement, and it names
neither the head rotation, nor the eaten stretch, nor any ratio between two
relators. -/
theorem greendlingerConclusion_of_deepWindowDrop_of_landing [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hwin : DeepWindowDrop R) (hland : LandingProduction R) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_cascadeLandingDrop hR hRne
    (cascadeLandingDrop_of_deepWindowDrop_of_landing hwin hland)

/-- **The same, over the (β)-regime landing residual.**  Composing with the
conjugator-absorbed plumbing of `Sofic.GreendlingerAlphaPlumb`: the gate costs
the deep window and the (β) landing production, and nothing else. -/
theorem greendlingerConclusion_of_deepWindowDrop_of_beta [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hwin : DeepWindowDrop R) (hbeta : LandingProductionBeta R) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_deepWindowDrop_of_landing hR hRne hwin
    (landingProduction_of_beta hmetric hbeta)

/-- **The sharp gate over the sharp window and the sharp landing
production.** -/
theorem greendlingerConclusionSharp_of_deepWindowDropSharp_of_landingSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hwin : DeepWindowDropSharp R lam)
    (hland : LandingProductionSharp R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_cascadeLandingDropSharp hR hRne hlam0 hlam
    (cascadeLandingDropSharp_of_deepArcDropSharp_of_landingSharp
      (deepArcDropSharp_of_deepWindowDropSharp hwin) hland)

/-- **The sharp gate over the sharp window and the sharp (β) landing.**  The end
state of both lanes: `GreendlingerConclusionSharp` — and through
`GreendlingerSharpTwins`, the sharp gate and the router's two obligations — over
the deep window and the conjugator-absorbed residual alone. -/
theorem greendlingerConclusionSharp_of_deepWindowDropSharp_of_betaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hwin : DeepWindowDropSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_deepWindowDropSharp_of_landingSharp hR hRne
    hlam0 hlam hwin (landingProductionSharp_of_betaSharp hmetric hbeta)

/-! ## 6.  The deep branch as a landing, and the descent that closes it

The window form above still asks the deep branch to produce an *arc*.  It need
not: the descent is already an induction, and what the deep regime leaves is
another expression with another block eating its front — the same situation the
descent handles at every stage.  So the deep obligation can be stated the way
the landing obligation is, as a claim about **where the block stops**, and the
arc comes out of the recursion for free.

`exists_postJunction_drop` is what makes this available at every tail length:
the junction is empty in the deep regime, so what survives is a drop of the word
past it, and the only question left is whether that composite drop lands.  Asked
that way the residual is a `LandsIn` — the very predicate the landing branch
already uses — and its offset field `6i < |t₃|` is exactly what
`GreendlingerDeepOverrunCount.six_mul_intrusion_lt_of_forward` proves from the
piece bound at any depth.

Nothing here reaches a coincidence: the coincidence is spent inside that piece
bound, through `ne_rotate_invRev_of_minimal_forward`, and the block that stops
inside the landing conjugator is the case `i = 0`, which `LandsIn` carries. -/

/-- **The deep obligation, as a landing.**  In the deep regime, with the
junction already discharged and the post-junction expression `f` and drop `D`
supplied, the composite block — what the head's own cancellation ate, plus what
the block from above ran past the head survivor — stops in some factor of `f`,
within a sixth of that factor's rotation past its conjugator.

This is `GreendlingerBetaBranch.LandingProduction`'s conclusion, at the
composite block and one junction down.  It asks for no arc, no window, no
offset against the head rotation and no ratio between two relators: only a
position, which is what the piece bound speaks to. -/
def DeepCompositeLands [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t c₂ t₂ : List (α × Bool))
    (e f : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (N i D : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → 6 * i < t.length → N ≤ c.length + i →
    c.length + t.length < M.length + i →
    f.length < e.length →
    B' = (conjEval f).toWord.drop D →
    LandsIn R (D + (N - P'.length)) (conjEval f).toWord f.length

/-- **The descent, with both branches landing.**

The induction of `GreendlingerDeepInduction.greendlingerAt_drop_of_cascadeLanding
Drop` with the deep case no longer handed out as an arc.  Three cases: the block
stays inside the trailing conjugator and the head's own rotation carries the
conclusion; it stops early enough for `LandingProduction` to name its landing
site; or it runs deep, the junction is empty, and `DeepCompositeLands` names the
landing site of the composite block one junction down.  The last two are the
same computation — a landing site, a recursion, two suffix inclusions — which is
the point of stating the deep residual as a landing.

So the gate now rests on two positional statements and nothing else. -/
theorem greendlingerAt_drop_of_lands [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hdeep : DeepCompositeLands R) (hland : LandingProduction R) :
    ∀ (n : ℕ) (e : List (FreeGroup α × List (α × Bool)))
      (c t w : List (α × Bool)) (N i : ℕ),
      e.length ≤ n →
      FreeGroup.IsReduced w → t ∈ symmetrization R →
      FreeGroup.IsReduced (palindrome c t) →
      IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) (FreeGroup.mk w) →
      6 * i < t.length → N ≤ c.length + i →
      GreendlingerAt R 0 (w.drop N) := by
  intro n
  induction n with
  | zero =>
      intro e c t w N i hlen hw ht hredp hmin hi hN
      cases e with
      | cons x e' =>
          simp only [List.length_cons] at hlen
          exact absurd hlen (by omega)
      | nil =>
          obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
            exists_leading_cancellation hw hredp hmin.2.1
          have hnil : FreeGroup.invRev M ++ B' = [] := by
            rw [← hgw, conjEval_nil]
            exact FreeGroup.toWord_eq_nil_iff.mpr rfl
          have hz := congrArg List.length hnil
          rw [List.length_append, FreeGroup.invRev_length,
            List.length_nil] at hz
          rw [hwe]
          exact (greendlingerAt_of_short_cancellation ht heq (by omega)
            hi).drop_of_le hN
  | succ n ih =>
      intro e c t w N i hlen hw ht hredp hmin hi hN
      obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
        exists_leading_cancellation hw hredp hmin.2.1
      have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
      have hlenP : P'.length + M.length = c.length + t.length + c.length := by
        have hb := congrArg List.length heq
        rw [List.length_append, length_palindrome] at hb
        exact hb.symm
      rw [hwe]
      rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
      · exact (greendlingerAt_of_short_cancellation ht heq hshort
          hi).drop_of_le hN
      · rcases le_or_gt (M.length + i) (c.length + t.length) with hle | hgt
        · obtain ⟨c', t', f, A, N', i', hf, hV, ht', hredp', hminf, hi', hN',
            hMb⟩ := hland c t e (FreeGroup.mk w) P' M B' i hmin ht hredp heq hgw
              (by omega) hi hle
          have hIH := ih f c' t'
            (conjEval ((FreeGroup.mk c', t') :: f)).toWord
            (N' + (M.length - A.length)) i'
            (by omega) FreeGroup.isReduced_toWord ht' hredp'
            (by rw [FreeGroup.mk_toWord]; exact hminf) hi' (by omega)
          have hB' : B' = (conjEval e).toWord.drop M.length := by
            rw [hgw, drop_append_of_ge (FreeGroup.invRev M) M.length B'
              (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
              Nat.sub_self, List.drop_zero]
          have hsuf₁ : (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop
              (N' + (M.length - A.length)) <:+ B' := by
            rw [hB', hV, drop_add N' (M.length - A.length)
              (conjEval ((FreeGroup.mk c', t') :: f)).toWord]
            exact drop_suffix_append A _ M.length
          have hsuf₂ : B' <:+ (P' ++ B').drop N := by
            have hb := drop_suffix_append P' B' N
            rwa [show N - P'.length = 0 from by omega, List.drop_zero] at hb
          exact hIH.of_suffix (hsuf₁.trans hsuf₂)
        · obtain ⟨c₂, t₂, f, D, ht₂, hredp₂, hmin₂, hf, hD⟩ :=
            exists_postJunction_drop hR hRne hmetric hmin ht hredp heq hgw
              (by omega) hi hgt
          obtain ⟨c₃, t₃, f₃, A₃, N₃, i₃, hf₃, hV₃, ht₃, hredp₃, hmin₃, hi₃,
            hN₃, hfit₃⟩ :=
            hdeep c t c₂ t₂ e f (FreeGroup.mk w) P' M B' N i D hmin hmin₂ ht ht₂
              hredp hredp₂ heq hgw (by omega) hi hN hgt hf hD
          have hIH := ih f₃ c₃ t₃
            (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord
            (N₃ + (D + (N - P'.length) - A₃.length)) i₃
            (by omega) FreeGroup.isReduced_toWord ht₃ hredp₃
            (by rw [FreeGroup.mk_toWord]; exact hmin₃) hi₃ (by omega)
          have hcomp : B'.drop (N - P'.length)
              = (conjEval f).toWord.drop (D + (N - P'.length)) := by
            rw [hD, ← drop_add]
          have hsuf₁ : (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord.drop
              (N₃ + (D + (N - P'.length) - A₃.length))
              <:+ (conjEval f).toWord.drop (D + (N - P'.length)) := by
            rw [hV₃, drop_add N₃ (D + (N - P'.length) - A₃.length)
              (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord]
            exact drop_suffix_append A₃ _ (D + (N - P'.length))
          have hsuf₂ : B'.drop (N - P'.length) <:+ (P' ++ B').drop N :=
            drop_suffix_append P' B' N
          rw [hcomp] at hsuf₂
          exact hIH.of_suffix (hsuf₁.trans hsuf₂)

/-- **The Greendlinger conclusion over the two landings.** -/
theorem greendlinger_of_lands [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hdeep : DeepCompositeLands R) (hland : LandingProduction R)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {e : List (FreeGroup α × List (α × Bool))}
    (hmin : IsMinimalConjExpr R e (FreeGroup.mk w)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ s.length < 2 * u.length := by
  cases e with
  | nil =>
      exfalso
      have hb := hmin.2.1
      rw [conjEval_nil] at hb
      have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
        rw [← FreeGroup.one_eq_mk]
        exact hb.symm
      have h2 := FreeGroup.reduce.sound h1
      rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
      exact hwne h2
  | cons x e'' =>
      obtain ⟨x₁, s₁⟩ := x
      obtain ⟨c, t, ht, hredp, hmin'⟩ := exists_palindromic_head hR hRne hmin
      have htpos : 0 < t.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
      have harc := greendlingerAt_drop_of_lands hR hRne hmetric hdeep hland
        e''.length e'' c t w 0 0 le_rfl hw ht hredp hmin' (by omega) (by omega)
      rw [List.drop_zero] at harc
      exact greendlinger_of_greendlingerAt harc

/-- **The free-group half-form gate over the two landings.**  The deep branch is
no longer an arc obligation: what the gate now costs is
`GreendlingerBetaBranch.LandingProduction` and one statement of the same kind
about the composite block one junction down. -/
theorem greendlingerConclusion_of_lands [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hdeep : DeepCompositeLands R) (hland : LandingProduction R) :
    GreendlingerConclusion R := by
  intro w hw hwne hmem
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R (FreeGroup.mk w)).mp hmem
  obtain ⟨e₀, hv₀, -, he₀⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩
  exact greendlinger_of_lands hR hRne hmetric hdeep hland hw hwne hmin

/-- **The same, over the (β)-regime landing residual.**  Both residuals are now
`LandsIn` statements: the conjugator-absorbed one of
`Sofic.GreendlingerAlphaPlumb` and the composite one of the deep branch. -/
theorem greendlingerConclusion_of_lands_of_beta [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hdeep : DeepCompositeLands R) (hbeta : LandingProductionBeta R) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_lands hR hRne hmetric hdeep
    (landingProduction_of_beta hmetric hbeta)

/-! ## 7.  The two landings, at the sharp constant -/

/-- **The deep obligation as a landing, at the sharp constant.**  The `λ`-twin
of `DeepCompositeLands`; the junction analysis it stands on is the half-form one,
reached by `GreendlingerDeepVacuitySharp.metricSmallCancellation_of_le` and
`six_mul_lt_of_lam_lt`, so nothing about the deep regime is restated. -/
def DeepCompositeLandsSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c₂ t₂ : List (α × Bool))
    (e f : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (N i D : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (i : ℚ) < lam * (t.length : ℚ) →
    N ≤ c.length + i →
    c.length + t.length < M.length + i →
    f.length < e.length →
    B' = (conjEval f).toWord.drop D →
    LandsInSharp R lam (D + (N - P'.length)) (conjEval f).toWord f.length

/-- **The descent at the sharp constant, with both branches landing.** -/
theorem greendlingerAtSharp_drop_of_lands [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepCompositeLandsSharp R lam)
    (hland : LandingProductionSharp R lam) :
    ∀ (n : ℕ) (e : List (FreeGroup α × List (α × Bool)))
      (c t w : List (α × Bool)) (N i : ℕ),
      e.length ≤ n →
      FreeGroup.IsReduced w → t ∈ symmetrization R →
      FreeGroup.IsReduced (palindrome c t) →
      IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) (FreeGroup.mk w) →
      (i : ℚ) < lam * (t.length : ℚ) → N ≤ c.length + i →
      GreendlingerAtSharp R lam 0 (w.drop N) := by
  intro n
  induction n with
  | zero =>
      intro e c t w N i hlen hw ht hredp hmin hi hN
      cases e with
      | cons x e' =>
          simp only [List.length_cons] at hlen
          exact absurd hlen (by omega)
      | nil =>
          obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
            exists_leading_cancellation hw hredp hmin.2.1
          have hnil : FreeGroup.invRev M ++ B' = [] := by
            rw [← hgw, conjEval_nil]
            exact FreeGroup.toWord_eq_nil_iff.mpr rfl
          have hz := congrArg List.length hnil
          rw [List.length_append, FreeGroup.invRev_length,
            List.length_nil] at hz
          rw [hwe]
          exact (greendlingerAtSharp_of_short_cancellation hlam ht heq
            (by omega) hi).drop_of_le hN
  | succ n ih =>
      intro e c t w N i hlen hw ht hredp hmin hi hN
      obtain ⟨P', M, B', heq, hgw, hwe⟩ :=
        exists_leading_cancellation hw hredp hmin.2.1
      have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
      have hlenP : P'.length + M.length = c.length + t.length + c.length := by
        have hb := congrArg List.length heq
        rw [List.length_append, length_palindrome] at hb
        exact hb.symm
      rw [hwe]
      rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
      · exact (greendlingerAtSharp_of_short_cancellation hlam ht heq hshort
          hi).drop_of_le hN
      · rcases le_or_gt (M.length + i) (c.length + t.length) with hle | hgt
        · obtain ⟨c', t', f, A, N', i', hf, hV, ht', hredp', hminf, hi', hN',
            hMb⟩ := hland c t e (FreeGroup.mk w) P' M B' i hmin ht hredp heq hgw
              (by omega) hi hle
          have hIH := ih f c' t'
            (conjEval ((FreeGroup.mk c', t') :: f)).toWord
            (N' + (M.length - A.length)) i'
            (by omega) FreeGroup.isReduced_toWord ht' hredp'
            (by rw [FreeGroup.mk_toWord]; exact hminf) hi' (by omega)
          have hB' : B' = (conjEval e).toWord.drop M.length := by
            rw [hgw, drop_append_of_ge (FreeGroup.invRev M) M.length B'
              (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
              Nat.sub_self, List.drop_zero]
          have hsuf₁ : (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop
              (N' + (M.length - A.length)) <:+ B' := by
            rw [hB', hV, drop_add N' (M.length - A.length)
              (conjEval ((FreeGroup.mk c', t') :: f)).toWord]
            exact drop_suffix_append A _ M.length
          have hsuf₂ : B' <:+ (P' ++ B').drop N := by
            have hb := drop_suffix_append P' B' N
            rwa [show N - P'.length = 0 from by omega, List.drop_zero] at hb
          exact hIH.of_suffix (hsuf₁.trans hsuf₂)
        · obtain ⟨c₂, t₂, f, D, ht₂, hredp₂, hmin₂, hf, hD⟩ :=
            exists_postJunction_drop hR hRne
              (metricSmallCancellation_of_le hlam hmetric) hmin ht hredp heq hgw
              (by omega) (six_mul_lt_of_lam_lt hlam hi) hgt
          obtain ⟨c₃, t₃, f₃, A₃, N₃, i₃, hf₃, hV₃, ht₃, hredp₃, hmin₃, hi₃,
            hN₃, hfit₃⟩ :=
            hdeep c t c₂ t₂ e f (FreeGroup.mk w) P' M B' N i D hmin hmin₂ ht ht₂
              hredp hredp₂ heq hgw (by omega) hi hN hgt hf hD
          have hIH := ih f₃ c₃ t₃
            (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord
            (N₃ + (D + (N - P'.length) - A₃.length)) i₃
            (by omega) FreeGroup.isReduced_toWord ht₃ hredp₃
            (by rw [FreeGroup.mk_toWord]; exact hmin₃) hi₃ (by omega)
          have hcomp : B'.drop (N - P'.length)
              = (conjEval f).toWord.drop (D + (N - P'.length)) := by
            rw [hD, ← drop_add]
          have hsuf₁ : (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord.drop
              (N₃ + (D + (N - P'.length) - A₃.length))
              <:+ (conjEval f).toWord.drop (D + (N - P'.length)) := by
            rw [hV₃, drop_add N₃ (D + (N - P'.length) - A₃.length)
              (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord]
            exact drop_suffix_append A₃ _ (D + (N - P'.length))
          have hsuf₂ : B'.drop (N - P'.length) <:+ (P' ++ B').drop N :=
            drop_suffix_append P' B' N
          rw [hcomp] at hsuf₂
          exact hIH.of_suffix (hsuf₁.trans hsuf₂)

/-- **The sharp conclusion over the two landings.** -/
theorem greendlingerSharp_of_lands [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepCompositeLandsSharp R lam)
    (hland : LandingProductionSharp R lam)
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {e : List (FreeGroup α × List (α × Bool))}
    (hmin : IsMinimalConjExpr R e (FreeGroup.mk w)) :
    ∃ s ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: s ∧ (1 - 3 * lam) * (s.length : ℚ) < (u.length : ℚ) := by
  cases e with
  | nil =>
      exfalso
      have hb := hmin.2.1
      rw [conjEval_nil] at hb
      have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
        rw [← FreeGroup.one_eq_mk]
        exact hb.symm
      have h2 := FreeGroup.reduce.sound h1
      rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
      exact hwne h2
  | cons x e'' =>
      obtain ⟨x₁, s₁⟩ := x
      obtain ⟨c, t, ht, hredp, hmin'⟩ := exists_palindromic_head hR hRne hmin
      have htpos : 0 < t.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
      have hjq : ((0 : ℕ) : ℚ) < lam * (t.length : ℚ) := by
        have htq : (0 : ℚ) < (t.length : ℚ) := by exact_mod_cast htpos
        simpa using mul_pos hlam0 htq
      have harc := greendlingerAtSharp_drop_of_lands hR hRne hlam hmetric hdeep
        hland e''.length e'' c t w 0 0 le_rfl hw ht hredp hmin' hjq (by omega)
      rw [List.drop_zero] at harc
      exact greendlingerSharp_of_greendlingerAtSharp harc

/-- **The sharp gate over the two landings.**  Both residuals are `LandsInSharp`
statements about where a block stops, and the deep half no longer owes an arc at
any offset. -/
theorem greendlingerConclusionSharp_of_lands [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepCompositeLandsSharp R lam)
    (hland : LandingProductionSharp R lam) :
    GreendlingerConclusionSharp R lam := by
  intro w hw hwne hmem
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R (FreeGroup.mk w)).mp hmem
  obtain ⟨e₀, hv₀, -, he₀⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩
  exact greendlingerSharp_of_lands hR hRne hlam0 hlam hmetric hdeep hland hw
    hwne hmin

/-- **The sharp gate over the deep landing and the (β) landing.**  The end
state: `GreendlingerConclusionSharp` — and through `GreendlingerSharpTwins`, the
sharp gate and both router obligations — over two positional residuals. -/
theorem greendlingerConclusionSharp_of_lands_of_betaSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepCompositeLandsSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_lands hR hRne hlam0 hlam hmetric hdeep
    (landingProductionSharp_of_betaSharp hmetric hbeta)

end SmallCancellationRouter
end GroupApproximation
