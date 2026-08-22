import GroupApproximation.Sofic.GreendlingerDeepThreeFactor

/-!
# The frame the three-factor overrun sits in

`GreendlingerDeepVacuity` leaves the deep regime owing one statement,
`DeepOverrunArc`: the head's block overruns the adjacent palindrome and the
located conclusion has to come from further down.  `GreendlingerDeepThreeFactor`
attacks that at its shortest instance — an expression of exactly three factors,
where the landing factor is the last one and its word is its own palindrome.

This file is the frame that carries that instance to expressions of any length,
and it is a frame rather than an induction on purpose.

## Why there is no induction on the deep predicate

The obvious move — hand the configuration down to the next factor and recurse —
is not available, and the arithmetic says why.  If the head's block overruns the
second factor then `GreendlingerChunks.survivor_le_of_overrun` caps that factor's
rotation survivor at two thirds, so the second factor loses at least a *third* of
its own rotation.  The deep regime needs five sixths
(`GreendlingerDeepArc.five_mul_lt_six_mul_eaten`), and a third is not five
sixths: the constant degrades `5/6 → 2/3` in a single step.  A third is still
enough for rigidity, since `eq_of_sixth_common_prefix` asks only for a sixth, but
it is not enough for the arc producer `greendlingerAt_of_deep_arc`, which needs
more than a half.  So the induction hypothesis is unavailable one level down, and
`DeepOverrunArc` cannot be its own inductive statement.

What replaces the induction is a decomposition that holds at every length.

## The overrun always leaves a drop

`exists_overrun_landing_drop` is `GreendlingerDeepThreeFactor`'s
`exists_three_factor_landing_drop` with the three-factor hypothesis removed:
whenever the head's block covers the second factor's survivor entirely, what
survives is a **drop of the word of the expression from the third factor on**,

    B' = (conjEval T).toWord.drop N,      N = |M₂| + (|M| − |P₂|),

for an arbitrary tail `T`.  The second factor drops out of the picture — that is
what the overrun hypothesis buys — and the proof is the same two cancellation
decompositions and one composition of drops.  At `T = [(mk c₃, t₃)]` the word is
the third palindrome and the statement is the landed one.

## What the frame delivers

`DeepOverrunLanding` is `DeepOverrunArc` with the tail split at the landing
factor, that factor in palindromic normal form, and the drop above supplied.
`deepOverrunArc_of_landing` proves `DeepOverrunArc` from it, discharging on the
way the two things the split needs:

* the two-factor case is **vacuous** — with an empty tail the tail word is the
  adjacent palindrome itself (`toWord_conjEval_singleton`), so the block is
  confined and the overrun hypothesis is contradicted;
* the landing factor is put into palindromic normal form by
  `exists_palindromic_thd`, the third-position analogue of
  `GreendlingerThreeFactor.exists_palindromic_snd`.  `exists_palindromic_at`
  does it at *any* position, which is the general form the cascade has wanted
  since `Sofic.GreendlingerAlphaPlumb` recorded its absence.

`deepOverrunLanding_of_depth_of_tail` then splits `DeepOverrunLanding` at the
landing factor's own tail: when it is empty the landed three-factor count
discharges the case outright, and what is left — `DeepOverrunLandingTail` — is
exactly the configuration in which the block lands in a factor that is **not**
the last.  Both forms are carried, the half one and the `λ`-twin, since the
frame never reads the arc bound.

## The distance-two reroute, and what it costs

Section 5 derives the composite pin the lane asked for.  The swap

    conjEval ((B, b) :: (C, m) :: e)
      = conjEval ((C, m) :: ((C * mk m * C⁻¹)⁻¹ * B, b) :: e)

moves the landing factor up beside the head keeping its own conjugator, and
composing it with the eaten reroute gives, in a minimal expression,

    |E| + ‖B‖ ≤ |t₀| + ‖(C · m · C⁻¹)⁻¹ · B‖.

That is the adjacent pin `|E| ≤ |t₀|` plus the cost of the swap, and the cost is
real: it is bounded by `2‖C‖ + |m|` and by nothing better, so the composite pin
is **vacuous** unless the intermediate factor's conjugator already carries the
landing factor's palindrome — and is *sharper* than the adjacent pin exactly when
it does, since then the swapped conjugator is the shorter one.  This is the
quantitative form of `GreendlingerDeepVacuity`'s remark that a reroute moves one
factor past its neighbour and no further; there is no free distance-two pin.

Unconditional throughout: no piece bound is read anywhere in this file.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  A one-factor expression spells its own palindrome -/

/-- The word of a single factor in palindromic normal form is that palindrome.
The two-factor case of the deep overrun is refuted by this alone. -/
theorem toWord_conjEval_singleton [DecidableEq α] {c t : List (α × Bool)}
    (hredp : FreeGroup.IsReduced (palindrome c t)) :
    (conjEval [(FreeGroup.mk c, t)]).toWord = palindrome c t := by
  have hev : conjEval [(FreeGroup.mk c, t)] = FreeGroup.mk (palindrome c t) := by
    rw [conjEval_cons, conjEval_nil, mul_one, mk_palindrome]
  rw [hev, FreeGroup.toWord_mk, hredp.reduce_eq]

/-! ## 2.  The overrun leaves a drop, at any length -/

/-- **The overrun, decomposed, for a tail of any length.**  When the head's block
covers the second factor's survivor entirely, what is left of the tail word is a
suffix of the word of the expression from the *third* factor on — one drop, by
one number.

This is `GreendlingerDeepThreeFactor.exists_three_factor_landing_drop` with the
three-factor hypothesis removed: that version reads the last factor's word as its
own palindrome, and nothing else in the argument uses the length of the tail.
The number is `|M₂| + (|M| − |P₂|)`, the depth the second factor's own block
reached plus the extra the head's block ran past it, and the overrun hypothesis
enters only to put `|P₂| ≤ |M|`. -/
theorem exists_overrun_landing_drop [DecidableEq α]
    {c₂ t₂ M B' : List (α × Bool)}
    {T : List (FreeGroup α × List (α × Bool))}
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (htail : (conjEval ((FreeGroup.mk c₂, t₂) :: T)).toWord
      = FreeGroup.invRev M ++ B')
    (hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂)) :
    ∃ N : ℕ, B' = (conjEval T).toWord.drop N := by
  have heval : conjEval ((FreeGroup.mk c₂, t₂) :: T)
      = FreeGroup.mk ((conjEval ((FreeGroup.mk c₂, t₂) :: T)).toWord) :=
    (FreeGroup.mk_toWord).symm
  obtain ⟨P₂, M₂, B₂, heq₂, hgw₂, hwe₂⟩ :=
    exists_leading_cancellation FreeGroup.isReduced_toWord hredp₂ heval
  have hB₂ : B₂ = (conjEval T).toWord.drop M₂.length := by
    rw [hgw₂, drop_append_of_ge (FreeGroup.invRev M₂) M₂.length B₂
      (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
      Nat.sub_self, List.drop_zero]
  rcases le_or_gt P₂.length M.length with hlen | hgt
  · have hkey : B' = B₂.drop (M.length - P₂.length) := by
      have h1 : FreeGroup.invRev M ++ B' = P₂ ++ B₂ := by
        rw [← htail, hwe₂]
      have h2 : (FreeGroup.invRev M ++ B').drop M.length = B' := by
        rw [drop_append_of_ge (FreeGroup.invRev M) M.length B'
          (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
          Nat.sub_self, List.drop_zero]
      rw [← h2, h1, drop_append_of_ge P₂ M.length B₂ hlen]
    refine ⟨M₂.length + (M.length - P₂.length), ?_⟩
    rw [hkey, hB₂,
      drop_add M₂.length (M.length - P₂.length) (conjEval T).toWord]
  · exfalso
    refine hover ?_
    have hMpre : FreeGroup.invRev M
        <+: (conjEval ((FreeGroup.mk c₂, t₂) :: T)).toWord := ⟨B', htail.symm⟩
    have hP₂pre : P₂ <+: (conjEval ((FreeGroup.mk c₂, t₂) :: T)).toWord :=
      ⟨B₂, hwe₂.symm⟩
    refine (List.prefix_of_prefix_length_le hMpre hP₂pre ?_).trans ⟨M₂, heq₂.symm⟩
    rw [FreeGroup.invRev_length]
    omega

/-! ## 3.  Palindromic normal form at a position the descent has passed -/

/-- **A factor at any position, in palindromic normal form.**  Replacing the
factor after `e₁` by its normal form spells the same element with a conjugator no
longer, so minimality is untouched.

`GreendlingerThreeFactor.exists_palindromic_head` and `exists_palindromic_snd` do
this at the first and second positions and there was no general form;
`Sofic.GreendlingerAlphaPlumb` records the absence as the reason its
conjugator-absorbed site has to name a landing factor already in normal form.
The general form is this, and the proof is the same three checks read through
`conjEval_append` and `conjWeight_append`. -/
theorem exists_palindromic_at [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {x : FreeGroup α} {s : List (α × Bool)}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R (e₁ ++ ((x, s) :: f)) g) :
    ∃ c t : List (α × Bool), t ∈ symmetrization R ∧
      FreeGroup.IsReduced (palindrome c t) ∧
      IsMinimalConjExpr R (e₁ ++ ((FreeGroup.mk c, t) :: f)) g := by
  obtain ⟨hv, he, hlen, hweight⟩ := hmin
  have hs : s ∈ symmetrization R :=
    hv (x, s) (List.mem_append_right _ List.mem_cons_self)
  obtain ⟨c, t, ht, hredt, heqt, hnormt⟩ := exists_palindrome_factor hR hRne hs x
  refine ⟨c, t, ht, hredt, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rcases List.mem_append.mp hy with hy₁ | hy₂
    · exact hv y (List.mem_append_left _ hy₁)
    · rcases List.mem_cons.mp hy₂ with rfl | hy₃
      · exact ht
      · exact hv y (List.mem_append_right _ (List.mem_cons_of_mem _ hy₃))
  · rw [conjEval_append, conjEval_cons, heqt, ← conjEval_cons,
      ← conjEval_append]
    exact he
  · intro e₀ hv₀ he₀
    have hb := hlen e₀ hv₀ he₀
    simpa using hb
  · intro e₀ hv₀ he₀ hlen₀
    have hb : conjWeight (e₁ ++ ((FreeGroup.mk c, t) :: f))
        ≤ conjWeight (e₁ ++ ((x, s) :: f)) := by
      rw [conjWeight_append, conjWeight_append, conjWeight_cons, conjWeight_cons]
      omega
    refine le_trans hb (hweight e₀ hv₀ he₀ ?_)
    simpa using hlen₀

/-- **The third factor in palindromic normal form**, with the first two left
exactly as they are.  This is the instance the frame below spends: the landing
factor of a deep overrun is the third, and the junction analysis reads it as a
palindrome. -/
theorem exists_palindromic_thd [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {c t c' t' : List (α × Bool)} {x : FreeGroup α} {s : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t')
      :: (x, s) :: e) g) :
    ∃ c'' t'' : List (α × Bool), t'' ∈ symmetrization R ∧
      FreeGroup.IsReduced (palindrome c'' t'') ∧
      IsMinimalConjExpr R ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t')
        :: (FreeGroup.mk c'', t'') :: e) g := by
  obtain ⟨hv, he, hlen, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  obtain ⟨h5, h6⟩ := conjValid_cons_iff.mp h4
  obtain ⟨c'', t'', ht'', hredt'', heqt'', hnormt''⟩ :=
    exists_palindrome_factor hR hRne h5 x
  refine ⟨c'', t'', ht'', hredt'',
    conjValid_cons_iff.mpr ⟨h1, conjValid_cons_iff.mpr ⟨h3,
      conjValid_cons_iff.mpr ⟨ht'', h6⟩⟩⟩, ?_, ?_, ?_⟩
  · rw [conjEval_cons, conjEval_cons, conjEval_cons, heqt'']
    rw [conjEval_cons, conjEval_cons, conjEval_cons] at he
    exact he
  · intro e₀ hv₀ he₀
    have hb := hlen e₀ hv₀ he₀
    simpa using hb
  · intro e₀ hv₀ he₀ hlen₀
    have hb : conjWeight ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t')
        :: (FreeGroup.mk c'', t'') :: e)
        ≤ conjWeight ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t')
          :: (x, s) :: e) := by
      simp only [conjWeight_cons]
      omega
    refine le_trans hb (hweight e₀ hv₀ he₀ ?_)
    simpa using hlen₀

/-! ## 4.  The residual, with the landing factor named and the drop supplied -/

/-- **The overrun obligation, at the landing factor.**  `DeepOverrunArc` with the
tail split at the factor the block lands in, that factor in palindromic normal
form, and the drop of `exists_overrun_landing_drop` handed over.

Nothing here is a weakening: `deepOverrunArc_of_landing` proves `DeepOverrunArc`
from it outright.  What it adds is the three things a landing analysis has to
start from — the landing factor as a palindrome, the expression it heads, and the
position `N` the block reached inside its word. -/
def DeepOverrunLanding [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t c₂ t₂ c₃ t₃ M B' : List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) (j N : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R → t₃ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    FreeGroup.IsReduced (palindrome c₃ t₃) →
    M <:+ palindrome c t →
    (conjEval ((FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: f)).toWord = FreeGroup.invRev M ++ B' →
    ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂) →
    B' = (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord.drop N →
    c.length < M.length → 6 * j < t.length →
    c.length + t.length < M.length + j →
    GreendlingerAt R (M.length + j - (c.length + t.length)) B'

/-- **The overrun obligation, at the landing factor, at the sharp constant.**
The `λ`-twin of `DeepOverrunLanding`.  Only the offset hypothesis and the arc
bound move; every structural field is `λ`-free and is quoted verbatim, because
the frame below never reads the bound. -/
def DeepOverrunLandingSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c₂ t₂ c₃ t₃ M B' : List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) (j N : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R → t₃ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    FreeGroup.IsReduced (palindrome c₃ t₃) →
    M <:+ palindrome c t →
    (conjEval ((FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: f)).toWord = FreeGroup.invRev M ++ B' →
    ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂) →
    B' = (conjEval ((FreeGroup.mk c₃, t₃) :: f)).toWord.drop N →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    c.length + t.length < M.length + j →
    GreendlingerAtSharp R lam (M.length + j - (c.length + t.length)) B'

/-- **The frame.**  `DeepOverrunArc` from the landing obligation.

Two cases and no induction.  An empty tail is impossible: the tail word is then
the adjacent palindrome itself, so the block is confined and the overrun
hypothesis is contradicted.  Otherwise the tail's leading factor is put in
palindromic normal form — which leaves the element it spells, and so the tail
word, unchanged — and `exists_overrun_landing_drop` supplies the position. -/
theorem deepOverrunArc_of_landing [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hland : DeepOverrunLanding R) : DeepOverrunArc R := by
  intro c t c₂ t₂ M B' f g j hmin ht ht₂ hredp hredp₂ hMsuf htail hover hlow hj
    hgt
  cases f with
  | nil =>
      exact absurd
        (show FreeGroup.invRev M <+: palindrome c₂ t₂ from
          ⟨B', htail.symm.trans (toWord_conjEval_singleton hredp₂)⟩) hover
  | cons x f' =>
      obtain ⟨x₃, s₃⟩ := x
      obtain ⟨c₃, t₃, ht₃, hredp₃, hmin₃⟩ := exists_palindromic_thd hR hRne hmin
      have hev : conjEval ((FreeGroup.mk c₂, t₂)
            :: (FreeGroup.mk c₃, t₃) :: f')
          = conjEval ((FreeGroup.mk c₂, t₂) :: (x₃, s₃) :: f') := by
        have h1 := hmin₃.2.1
        have h2 := hmin.2.1
        rw [conjEval_cons] at h1 h2
        exact mul_left_cancel (h1.trans h2.symm)
      rw [← hev] at htail
      obtain ⟨N, hB'⟩ := exists_overrun_landing_drop hredp₂ htail hover
      exact hland c t c₂ t₂ c₃ t₃ M B' f' g j N hmin₃ ht ht₂ ht₃ hredp hredp₂
        hredp₃ hMsuf htail hover hB' hlow hj hgt

/-- **The frame, at the sharp constant.**  The same two cases: the frame reads
neither the offset hypothesis nor the arc bound, so the proof is the half-form
one with the two `λ`-carrying fields passed through untouched. -/
theorem deepOverrunArcSharp_of_landingSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hland : DeepOverrunLandingSharp R lam) : DeepOverrunArcSharp R lam := by
  intro c t c₂ t₂ M B' f g j hmin ht ht₂ hredp hredp₂ hMsuf htail hover hlow hj
    hgt
  cases f with
  | nil =>
      exact absurd
        (show FreeGroup.invRev M <+: palindrome c₂ t₂ from
          ⟨B', htail.symm.trans (toWord_conjEval_singleton hredp₂)⟩) hover
  | cons x f' =>
      obtain ⟨x₃, s₃⟩ := x
      obtain ⟨c₃, t₃, ht₃, hredp₃, hmin₃⟩ := exists_palindromic_thd hR hRne hmin
      have hev : conjEval ((FreeGroup.mk c₂, t₂)
            :: (FreeGroup.mk c₃, t₃) :: f')
          = conjEval ((FreeGroup.mk c₂, t₂) :: (x₃, s₃) :: f') := by
        have h1 := hmin₃.2.1
        have h2 := hmin.2.1
        rw [conjEval_cons] at h1 h2
        exact mul_left_cancel (h1.trans h2.symm)
      rw [← hev] at htail
      obtain ⟨N, hB'⟩ := exists_overrun_landing_drop hredp₂ htail hover
      exact hland c t c₂ t₂ c₃ t₃ M B' f' g j N hmin₃ ht ht₂ ht₃ hredp hredp₂
        hredp₃ hMsuf htail hover hB' hlow hj hgt

/-! ## 5.  What is left once the landed count is spent -/

/-- **The landing obligation where the landing factor is not the last.**
`DeepOverrunLanding` restricted to expressions with a fourth factor.

This is the whole of what the deep lane still owes beyond the three-factor
count: `deepOverrunLanding_of_depth_of_tail` discharges the complementary case
from `GreendlingerDeepThreeFactor.DeepOverrunDepth`, which is stated at exactly
three factors because it reads the last factor's word as its own palindrome.
The fourth factor is left as it stands rather than in normal form; a prover who
wants it normalized has `exists_palindromic_at` above. -/
def DeepOverrunLandingTail [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t c₂ t₂ c₃ t₃ M B' : List (α × Bool))
    (x : FreeGroup α × List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) (j N : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: x :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R → t₃ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    FreeGroup.IsReduced (palindrome c₃ t₃) →
    M <:+ palindrome c t →
    (conjEval ((FreeGroup.mk c₂, t₂)
      :: (FreeGroup.mk c₃, t₃) :: x :: f)).toWord = FreeGroup.invRev M ++ B' →
    ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂) →
    B' = (conjEval ((FreeGroup.mk c₃, t₃) :: x :: f)).toWord.drop N →
    c.length < M.length → 6 * j < t.length →
    c.length + t.length < M.length + j →
    GreendlingerAt R (M.length + j - (c.length + t.length)) B'

/-- **The landing obligation, from the landed three-factor count and the rest.**
When the landing factor is the last one, `DeepOverrunLanding` is exactly the
statement `GreendlingerDeepThreeFactor.greendlingerAt_of_deepOverrunDepth`
proves from the count; when it is not, the residual applies.  The supplied drop
is not needed in the first branch — that theorem derives its own. -/
theorem deepOverrunLanding_of_depth_of_tail [DecidableEq α]
    {R : Set (List (α × Bool))} (hdepth : DeepOverrunDepth R)
    (htail : DeepOverrunLandingTail R) : DeepOverrunLanding R := by
  intro c t c₂ t₂ c₃ t₃ M B' f g j N hmin ht ht₂ ht₃ hredp hredp₂ hredp₃ hMsuf
    hword hover hB' hlow hj hgt
  cases f with
  | nil =>
      exact greendlingerAt_of_deepOverrunDepth hdepth hmin ht ht₂ ht₃ hredp
        hredp₂ hredp₃ hMsuf hword hover hlow hj hgt
  | cons x f' =>
      exact htail c t c₂ t₂ c₃ t₃ M B' x f' g j N hmin ht ht₂ ht₃ hredp hredp₂
        hredp₃ hMsuf hword hover hB' hlow hj hgt

/-- **`DeepOverrunArc` over the landed count and the one residual.**  The deep
regime now costs exactly two statements: the three-factor count, and the
configuration in which the block lands in a factor that is not the last. -/
theorem deepOverrunArc_of_depth_of_tail [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hdepth : DeepOverrunDepth R) (htail : DeepOverrunLandingTail R) :
    DeepOverrunArc R :=
  deepOverrunArc_of_landing hR hRne
    (deepOverrunLanding_of_depth_of_tail hdepth htail)

/-- **The free-group half-form gate over the deep residuals and the (β)
landing.**  Composing the frame with `Sofic.GreendlingerAlphaPlumb`'s
conjugator-absorbed plumbing: the gate costs the three-factor count, the
not-last-factor landing, and the (β)-regime landing production. -/
theorem greendlingerConclusion_of_depth_of_tail_of_beta [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hdepth : DeepOverrunDepth R) (htail : DeepOverrunLandingTail R)
    (hbeta : LandingProductionBeta R) : GreendlingerConclusion R :=
  greendlingerConclusion_of_deepOverrunArc_of_landing hR hRne hmetric
    (deepOverrunArc_of_depth_of_tail hR hRne hdepth htail)
    (landingProduction_of_beta hmetric hbeta)

/-! ## 6.  The distance-two reroute, and its price -/

/-- Replacing a tail by one that spells the same element leaves the expression
spelling the same element.  Stated because the composite moves below rewrite
under a head factor, where rewriting with `conjEval_cons` twice would unfold the
tail's own leading factor instead of the second side of the equation. -/
theorem conjEval_cons_congr (x : FreeGroup α × List (α × Bool))
    {T₁ T₂ : List (FreeGroup α × List (α × Bool))}
    (h : conjEval T₁ = conjEval T₂) :
    conjEval (x :: T₁) = conjEval (x :: T₂) := by
  rw [conjEval_cons', conjEval_cons', h]

/-- **The swap that makes a factor adjacent to the head.**  The second factor is
conjugated past the third; the third keeps its own conjugator, which is what a
reroute against the head needs, and the second pays.

Unconditional, and available at every junction: no minimality, no reducedness. -/
theorem conjEval_swap_snd (B C : FreeGroup α) (b m : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) :
    conjEval ((B, b) :: (C, m) :: e)
      = conjEval ((C, m)
        :: ((C * FreeGroup.mk m * C⁻¹)⁻¹ * B, b) :: e) :=
  conjEval_replace_two (by group)

/-- **The eaten pin at distance two.**  The third factor's conjugator runs back
along the head's rotation — `c₃ = c ++ (invRev E ++ Z)`, the configuration
`GreendlingerDeepArc.not_deep_eaten_buried` reads — but the two factors are not
adjacent.  Swapping the second factor past the third makes them adjacent at the
cost of one conjugator, and the eaten reroute then applies to the pair.

The pin is the adjacent one plus that cost:

    |E| + ‖B‖ ≤ |t₀| + ‖(C · m · C⁻¹)⁻¹ · B‖.

The cost is not free — it is at most `2‖C‖ + |m|` and no better in general — so
this is informative only where the intermediate conjugator already carries the
landing palindrome, and where it does the swapped conjugator is the *shorter*
one and the pin beats `two_mul_eaten_le_of_minimal_reroute`.  Read the other way
it is the quantitative form of `GreendlingerDeepVacuity`'s remark that a reroute
moves one factor past its neighbour and no further: there is no free
distance-two pin. -/
theorem eaten_le_of_minimal_reroute_two [DecidableEq α]
    {R : Set (List (α × Bool))} {c t₀ E Z m b : List (α × Bool)}
    {B : FreeGroup α} {e : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t₀ ++ E) :: (B, b)
        :: (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)), m) :: e) g)
    (hred : FreeGroup.IsReduced (c ++ (FreeGroup.invRev E ++ Z))) :
    E.length + FreeGroup.norm B
      ≤ t₀.length + FreeGroup.norm
        ((FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)) * FreeGroup.mk m
          * (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)))⁻¹)⁻¹ * B) := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  obtain ⟨h5, h6⟩ := conjValid_cons_iff.mp h4
  -- the swap, then the reroute
  have hswap := conjEval_swap_snd B
    (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z))) b m e
  have hmid : conjEval ((FreeGroup.mk c, t₀ ++ E) :: (B, b)
        :: (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)), m) :: e)
      = conjEval ((FreeGroup.mk c, t₀ ++ E)
        :: (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)), m)
        :: ((FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)) * FreeGroup.mk m
          * (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)))⁻¹)⁻¹ * B, b)
        :: e) :=
    conjEval_cons_congr (FreeGroup.mk c, t₀ ++ E) hswap
  have hmove := mk_palindrome_mul_reroute c (t₀ ++ E) (FreeGroup.invRev E ++ Z) m
  simp only [mk_palindrome] at hmove
  have hv2 : ConjValid R
      ((FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z))), m)
        :: (FreeGroup.mk c, t₀ ++ E)
        :: ((FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)) * FreeGroup.mk m
          * (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)))⁻¹)⁻¹ * B, b)
        :: e) :=
    conjValid_cons_iff.mpr ⟨h5, conjValid_cons_iff.mpr ⟨h1,
      conjValid_cons_iff.mpr ⟨h3, h6⟩⟩⟩
  have he2 : conjEval
      ((FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z))), m)
        :: (FreeGroup.mk c, t₀ ++ E)
        :: ((FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)) * FreeGroup.mk m
          * (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)))⁻¹)⁻¹ * B, b)
        :: e) = g := by
    rw [← conjEval_replace_two hmove, ← hmid]
    exact he
  have hlen2 :
      ((FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z))), m)
        :: (FreeGroup.mk c, t₀ ++ E)
        :: ((FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)) * FreeGroup.mk m
          * (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)))⁻¹)⁻¹ * B, b)
        :: e).length
      = ((FreeGroup.mk c, t₀ ++ E) :: (B, b)
        :: (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)), m) :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  simp only [conjWeight_cons] at hle
  have hnorm1 : FreeGroup.norm (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)))
      = c.length + (E.length + Z.length) := by
    rw [norm_mk_of_isReduced hred]
    simp [FreeGroup.invRev_length]
  have hcollapse : FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z)))
      = FreeGroup.mk (c ++ (t₀ ++ Z)) := by
    simp only [mk_append_mul, mk_invRev_eq_inv]
    group
  have hnorm2 : FreeGroup.norm
      (FreeGroup.mk (c ++ ((t₀ ++ E) ++ (FreeGroup.invRev E ++ Z))))
      ≤ c.length + (t₀.length + Z.length) := by
    rw [hcollapse]
    have hb := norm_mk_le_length (c ++ (t₀ ++ Z))
    rw [List.length_append, List.length_append] at hb
    exact hb
  omega

/-- **The hug pin at distance two**, the mirror.  The head's conjugator overhangs
the third factor's by `q`, a prefix of that factor's rotation, and again the two
are not adjacent.  Same swap, same price:

    |q| + ‖B‖ ≤ |r| + ‖(C · (q ++ r) · C⁻¹)⁻¹ · B‖.

Note that the intermediate conjugator's own norm never enters: it appears on both
sides of the weight comparison and cancels, which is why neither pin needs the
second factor reduced. -/
theorem hug_le_of_minimal_reroute_two [DecidableEq α]
    {R : Set (List (α × Bool))} {c' q r t b : List (α × Bool)}
    {B : FreeGroup α} {e : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk (c' ++ q), t) :: (B, b)
        :: (FreeGroup.mk c', q ++ r) :: e) g)
    (hred : FreeGroup.IsReduced (c' ++ q)) :
    q.length + FreeGroup.norm B
      ≤ r.length + FreeGroup.norm
        ((FreeGroup.mk c' * FreeGroup.mk (q ++ r)
          * (FreeGroup.mk c')⁻¹)⁻¹ * B) := by
  obtain ⟨hv, he, -, hweight⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  obtain ⟨h3, h4⟩ := conjValid_cons_iff.mp h2
  obtain ⟨h5, h6⟩ := conjValid_cons_iff.mp h4
  have hswap := conjEval_swap_snd B (FreeGroup.mk c') b (q ++ r) e
  have hmid : conjEval ((FreeGroup.mk (c' ++ q), t) :: (B, b)
        :: (FreeGroup.mk c', q ++ r) :: e)
      = conjEval ((FreeGroup.mk (c' ++ q), t) :: (FreeGroup.mk c', q ++ r)
        :: ((FreeGroup.mk c' * FreeGroup.mk (q ++ r)
          * (FreeGroup.mk c')⁻¹)⁻¹ * B, b) :: e) :=
    conjEval_cons_congr (FreeGroup.mk (c' ++ q), t) hswap
  have hmove := mk_palindrome_mul_hug_reroute c' q r t
  simp only [mk_palindrome] at hmove
  have hv2 : ConjValid R
      ((FreeGroup.mk c', q ++ r)
        :: (FreeGroup.mk (c' ++ FreeGroup.invRev r), t)
        :: ((FreeGroup.mk c' * FreeGroup.mk (q ++ r)
          * (FreeGroup.mk c')⁻¹)⁻¹ * B, b) :: e) :=
    conjValid_cons_iff.mpr ⟨h5, conjValid_cons_iff.mpr ⟨h1,
      conjValid_cons_iff.mpr ⟨h3, h6⟩⟩⟩
  have he2 : conjEval ((FreeGroup.mk c', q ++ r)
      :: (FreeGroup.mk (c' ++ FreeGroup.invRev r), t)
      :: ((FreeGroup.mk c' * FreeGroup.mk (q ++ r)
        * (FreeGroup.mk c')⁻¹)⁻¹ * B, b) :: e) = g := by
    rw [← conjEval_replace_two hmove, ← hmid]
    exact he
  have hlen2 : ((FreeGroup.mk c', q ++ r)
      :: (FreeGroup.mk (c' ++ FreeGroup.invRev r), t)
      :: ((FreeGroup.mk c' * FreeGroup.mk (q ++ r)
        * (FreeGroup.mk c')⁻¹)⁻¹ * B, b) :: e).length
      = ((FreeGroup.mk (c' ++ q), t) :: (B, b)
        :: (FreeGroup.mk c', q ++ r) :: e).length := by
    simp
  have hle := hweight _ hv2 he2 hlen2
  simp only [conjWeight_cons] at hle
  have hnorm : FreeGroup.norm (FreeGroup.mk (c' ++ q)) = c'.length + q.length := by
    rw [norm_mk_of_isReduced hred, List.length_append]
  have hnorm2 : FreeGroup.norm (FreeGroup.mk (c' ++ FreeGroup.invRev r))
      ≤ c'.length + r.length := by
    have hb := norm_mk_le_length (c' ++ FreeGroup.invRev r)
    rw [List.length_append, FreeGroup.invRev_length] at hb
    exact hb
  omega

end SmallCancellationRouter
end GroupApproximation
