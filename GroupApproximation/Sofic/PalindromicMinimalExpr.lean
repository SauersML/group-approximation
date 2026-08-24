import GroupApproximation.Sofic.GreendlingerWeight

/-!
# Every expression can be respelled with reduced palindromic factors

`GreendlingerWeight.exists_palindrome_factor` puts **one** factor of a
conjugate-product expression into palindromic normal form: it replaces
`x · mk s · x⁻¹` by `mk c · mk t · (mk c)⁻¹` with `t` a rotation of `s`, with
`c` no longer than `x`, and — the point — with the word

    `palindrome c t = c ++ t ++ invRev c`

**reduced**.  `exists_palindromic_isMinimalConjExpr` applies it to the first two
factors of a minimal expression.  This file applies it to *all* of them at once,
and records that minimality survives.

## Why the whole expression

The curvature count runs on `ConjExprMatching.labelledWord e w`, the word

    `c₁ t₁ c₁⁻¹ ⋯ cₙ tₙ cₙ⁻¹ · w⁻¹`

with each letter tagged by its block.  `MatchingSameBlock` proves that no
matched pair has both ends in one **block**, from the fact that each block is
spelled by a reduced word.  What the stems need is the same statement for a
whole **factor** — `conj k`, `relator k` and `stem k` are three blocks of one
factor, and a pair joining two of them is exactly a conjugator letter cancelling
against its own relator, which is what makes a stem impossible to price.

That statement needs each factor's word `cₖ ++ tₖ ++ invRev cₖ` to be reduced,
for every `k` at once, which is what `IsPalindromicExpr` names and what
`exists_palindromic_conjExpr` supplies.

## What is proved

* `exists_palindromic_conjExpr` — every valid expression has a palindromic
  respelling of the same length, spelling the same element, of no greater
  weight.  A list induction over `exists_palindrome_factor`.
* `exists_palindromic_isMinimalConjExpr_all` — consequently a *minimal*
  expression has a palindromic respelling that is again minimal: the length is
  unchanged, so the length clause transfers verbatim, and the weight cannot rise,
  so the weight clause transfers through one `le_trans`.
* `isReduced_factorWord_of_isPalindromicExpr` — the property in the shape the
  labelled word consumes, `c ++ (t ++ invRev c)`, which is what
  `ConjExprMatching.map_fst_labelledFactor` produces.

So a curvature count may assume, for free, that every factor of the expression
it is handed is a reduced palindrome.  Nothing here is about small cancellation:
the only inputs are that the relators are cyclically reduced and nonempty.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  Palindromes, reassociated -/

/-- `palindrome` associated the way a labelled factor spells it:
`ConjExprMatching.map_fst_labelledFactor` produces `c ++ (s ++ invRev c)`. -/
theorem palindrome_eq_append_append (c m : List (α × Bool)) :
    palindrome c m = c ++ (m ++ FreeGroup.invRev c) := by
  rw [palindrome, List.append_assoc]

/-- The conjugator of a reduced palindrome is reduced. -/
theorem isReduced_of_isReduced_palindrome {c m : List (α × Bool)}
    (h : FreeGroup.IsReduced (palindrome c m)) : FreeGroup.IsReduced c :=
  isReduced_of_infix ⟨[], m ++ FreeGroup.invRev c, by simp [palindrome]⟩ h

/-- A reduced conjugator is its own normal form, so a palindrome built from it
can be read off the element it names. -/
theorem toWord_mk_of_isReduced [DecidableEq α] {c : List (α × Bool)}
    (h : FreeGroup.IsReduced c) : (FreeGroup.mk c).toWord = c := by
  rw [FreeGroup.toWord_mk, h.reduce_eq]

/-! ## 2.  The property -/

/-- **Every factor is a reduced palindrome.**  The factor `(c, s)` contributes
the word `c.toWord ++ s ++ invRev c.toWord` to the expression's word, and this
says that word is reduced — no letter of the conjugator cancels against the
relator it wraps, and the two copies of the conjugator do not meet. -/
def IsPalindromicExpr [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) : Prop :=
  ∀ q ∈ e, FreeGroup.IsReduced (palindrome q.1.toWord q.2)

theorem isPalindromicExpr_nil [DecidableEq α] :
    IsPalindromicExpr ([] : List (FreeGroup α × List (α × Bool))) := by
  intro q hq
  exact absurd hq (by simp)

theorem isPalindromicExpr_cons [DecidableEq α] {c : FreeGroup α}
    {s : List (α × Bool)} {e : List (FreeGroup α × List (α × Bool))}
    (h : FreeGroup.IsReduced (palindrome c.toWord s))
    (he : IsPalindromicExpr e) : IsPalindromicExpr ((c, s) :: e) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact h
  · exact he q hq'

theorem IsPalindromicExpr.tail [DecidableEq α] {x : FreeGroup α × List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))}
    (h : IsPalindromicExpr (x :: e)) : IsPalindromicExpr e :=
  fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- **The property in the shape the labelled word consumes.**  A factor of a
palindromic expression spells `c ++ (s ++ invRev c)`, reduced — which is exactly
`ConjExprMatching.map_fst_labelledFactor` of that factor. -/
theorem isReduced_factorWord_of_isPalindromicExpr [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} (h : IsPalindromicExpr e)
    {q : FreeGroup α × List (α × Bool)} (hq : q ∈ e) :
    FreeGroup.IsReduced
      (q.1.toWord ++ (q.2 ++ FreeGroup.invRev q.1.toWord)) := by
  have := h q hq
  rwa [palindrome_eq_append_append] at this

/-! ## 3.  The respelling -/

/-- **Every valid expression has a palindromic respelling.**  Each factor is
replaced by its palindromic normal form: the element is unchanged, the number of
factors is unchanged, and the total conjugator length cannot rise, because
`exists_palindrome_factor` returns a conjugator no longer than the one it
replaces. -/
theorem exists_palindromic_conjExpr [DecidableEq α] {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ []) :
    ∀ e : List (FreeGroup α × List (α × Bool)), ConjValid R e →
      ∃ e' : List (FreeGroup α × List (α × Bool)),
        ConjValid R e' ∧ conjEval e' = conjEval e ∧ e'.length = e.length ∧
          conjWeight e' ≤ conjWeight e ∧ IsPalindromicExpr e' := by
  intro e
  induction e with
  | nil =>
      intro _
      exact ⟨[], conjValid_nil R, rfl, rfl, le_rfl, isPalindromicExpr_nil⟩
  | cons x e ih =>
      obtain ⟨y, s⟩ := x
      intro hv
      obtain ⟨hs, he⟩ := conjValid_cons_iff.mp hv
      obtain ⟨e', hv', heq', hlen', hwt', hpal'⟩ := ih he
      obtain ⟨c, t, ht, hredt, heqt, hnormt⟩ := exists_palindrome_factor hR hRne hs y
      have hredc : FreeGroup.IsReduced c := isReduced_of_isReduced_palindrome hredt
      have hword : (FreeGroup.mk c).toWord = c := toWord_mk_of_isReduced hredc
      refine ⟨(FreeGroup.mk c, t) :: e', conjValid_cons_iff.mpr ⟨ht, hv'⟩, ?_, ?_,
        ?_, isPalindromicExpr_cons (by rw [hword]; exact hredt) hpal'⟩
      · rw [conjEval_cons, conjEval_cons, heqt, heq']
      · rw [List.length_cons, List.length_cons, hlen']
      · rw [conjWeight_cons, conjWeight_cons]
        exact Nat.add_le_add hnormt hwt'

/-- **Minimality survives the respelling.**  The respelling has the same length,
so the length clause of minimality is inherited verbatim; its weight is no
greater, so the weight clause is inherited through one `le_trans`.

Consequently the count may assume both minimality and palindromic factors. -/
theorem exists_palindromic_isMinimalConjExpr_all [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R e g) :
    ∃ e', IsMinimalConjExpr R e' g ∧ IsPalindromicExpr e' := by
  obtain ⟨hv, he, hlen, hwt⟩ := hmin
  obtain ⟨e', hv', heq', hlen', hwt', hpal'⟩ :=
    exists_palindromic_conjExpr hR hRne e hv
  refine ⟨e', ⟨hv', by rw [heq', he], ?_, ?_⟩, hpal'⟩
  · intro e₀ hv₀ he₀
    rw [hlen']
    exact hlen e₀ hv₀ he₀
  · intro e₀ hv₀ he₀ hl₀
    refine le_trans hwt' (hwt e₀ hv₀ he₀ ?_)
    rw [hl₀, hlen']

/-- The same, keyed to an element rather than to an expression: a minimal
expression exists for anything the normal closure contains, and it may be taken
palindromic. -/
theorem exists_palindromic_minimal_of_exists [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {g : FreeGroup α}
    (h : ∃ e : List (FreeGroup α × List (α × Bool)), ConjValid R e ∧ conjEval e = g) :
    ∃ e, IsMinimalConjExpr R e g ∧ IsPalindromicExpr e := by
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr h
  exact exists_palindromic_isMinimalConjExpr_all hR hRne hmin

end SmallCancellationRouter
end GroupApproximation
