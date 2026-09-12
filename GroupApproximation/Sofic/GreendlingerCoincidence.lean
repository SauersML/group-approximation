import GroupApproximation.Sofic.GreendlingerDeepestMatch

/-!
# The coincidence, discharged from minimality — adjacent or not

`GreendlingerDeepestMatch` closes the `i_c = 0` branch of `CascadeLanding`
against one hypothesis it does not prove: that the head rotation, inverted, is
not the rotation of the landing rotation that the overlap prefixes.  That
hypothesis is distinctness, and distinctness is not a statement about pieces —
it is a statement about the expression, and what refutes it is minimality.

This file discharges it, for a landing factor anywhere in the tail.

## Why the adjacent argument does not transport unchanged

For an adjacent landing factor the coincidence makes the two palindromes spell
mutually inverse elements (`mk_palindrome_mul_eq_one_of_coincidence`), and
minimality forbids exactly that.  Further down the cascade the same computation
gives a product of *unconjugated* palindromes, while minimality
(`GreendlingerThreeFactor.conj_ne_inv_of_minimal`) forbids a product in which
the landing factor is conjugated by everything between the two — and the two
statements do not meet: nothing makes `conjEval e₁` commute with the landing
factor.

The repair is to name the **effective conjugator**.  Write

    mk d = conjEval e₁ * mk c'

for a word `d`, which always exists — take `d = (conjEval e₁ * mk c').toWord`.
Then

    conjEval e₁ * (mk c' * mk t' * (mk c')⁻¹) * (conjEval e₁)⁻¹
      = mk d * mk t' * (mk d)⁻¹ = mk (palindrome d t'),

so the shape minimality forbids *is* a product of two palindromes after all,
and the coincidence lemma applies to `d` in place of `c'`.  The adjacent case
is the instance `e₁ = []`, where `conjEval [] = 1` and `d` may be taken to be
`c'` itself: one theorem covers both, and the distinction the assignment drew
between them disappears once the effective conjugator is written down.

What the overhang hypothesis then says is `c = d ++ q` — the head conjugator
overhangs the *effective* conjugator of the landing factor, not its bare one.
That is the form the word-level analysis produces anyway, since what the block
meets in the tail word is the landing palindrome as it appears there, already
conjugated by everything the cascade has passed.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The coincidence contradicts minimality -/

/-- **Distinctness, from minimality alone.**

If the head rotation inverted were the rotation of the landing rotation that
the overlap prefixes, the head factor and the landing factor — the latter
conjugated by everything between them — would spell mutually inverse elements,
and a minimal expression has no such pair: deleting both shortens it by two.

`e₁` is the block of factors between the two, so `e₁ = []` is the adjacent
case and needs no separate argument.  `hd` names the effective conjugator and
is satisfiable for every `e₁` and `c'` by `FreeGroup.mk_toWord`. -/
theorem invRev_ne_rotate_of_minimal [DecidableEq α] {R : Set (List (α × Bool))}
    {c t t' c' d q : List (α × Bool)}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c', t') :: f))) g)
    (hd : FreeGroup.mk d = conjEval e₁ * FreeGroup.mk c')
    (hcq : c = d ++ q) (hq : q <+: t') :
    FreeGroup.invRev t ≠ t'.rotate q.length := by
  intro hrot
  have hcoin := mk_palindrome_mul_eq_one_of_coincidence hcq hq hrot
  refine conj_ne_inv_of_minimal hmin ?_
  have hexp : conjEval e₁ * (FreeGroup.mk c' * FreeGroup.mk t'
        * (FreeGroup.mk c')⁻¹) * (conjEval e₁)⁻¹
      = FreeGroup.mk d * FreeGroup.mk t' * (FreeGroup.mk d)⁻¹ := by
    rw [hd]
    group
  rw [hexp, ← mk_palindrome, ← mk_palindrome]
  exact hcoin

/-- **The effective conjugator always exists.**  Recorded so that a caller
never has to invent `d`: it is the reduced word of the product. -/
theorem exists_effectiveConjugator [DecidableEq α]
    (e₁ : List (FreeGroup α × List (α × Bool))) (c' : List (α × Bool)) :
    ∃ d : List (α × Bool), FreeGroup.mk d = conjEval e₁ * FreeGroup.mk c' :=
  ⟨(conjEval e₁ * FreeGroup.mk c').toWord, FreeGroup.mk_toWord⟩

/-! ## Case (α), with nothing left assumed about distinctness -/

/-- **`CascadeLanding` on the `i_c = 0` branch, hypothesis-free in the
coincidence.**

This is `GreendlingerDeepestMatch.cascadeLanding_of_conjugatorAbsorbed` with
its distinctness hypothesis replaced by the data that produces it: the landing
factor's position in the tail, the minimality of the whole expression, and the
overhang of the head conjugator past the effective conjugator.  Case (α) is
now closed against the hypotheses the descent actually has.

What remains of `CascadeLanding` is the `i_c > 0` branch, and nothing here
touches it. -/
theorem cascadeLanding_of_conjugatorAbsorbed' [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {c t t' c' d q E A M P' B' : List (α × Bool)} {N j : ℕ}
    {e e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hlow : c.length < M.length)
    (hhigh : M.length ≤ c.length + t.length)
    (hj : 6 * j < t.length)
    (hM : M = E ++ FreeGroup.invRev c)
    (hintr : FreeGroup.invRev E <+: t'.rotate q.length)
    (he : e = e₁ ++ ((FreeGroup.mk c', t') :: f))
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hd : FreeGroup.mk d = conjEval e₁ * FreeGroup.mk c')
    (hcq : c = d ++ q) (hq : q <+: t')
    (hf : f.length < e.length)
    (hV : (conjEval e).toWord
      = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hmin' : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)))
    (hN : N ≤ c'.length + E.length)
    (hfit : M.length + N ≤ A.length + c'.length + E.length) :
    GreendlingerAt R (c.length + j) (P' ++ B') ∨
      (M.length + j ≤ c.length + t.length ∧
        LandsIn R M.length (conjEval e).toWord e.length) := by
  subst he
  exact cascadeLanding_of_conjugatorAbsorbed hmetric ht ht' heq hlow hhigh hj hM
    hintr (invRev_ne_rotate_of_minimal hmin hd hcq hq) hf hV hredp' hmin' hN hfit

end SmallCancellationRouter
end GroupApproximation
