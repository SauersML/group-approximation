import GroupApproximation.Sofic.GreendlingerCoincidence

/-!
# The (β) branch: eaten letters come back, and reducedness voids the coincidence

`GreendlingerDeepestMatch` and `GreendlingerCoincidence` close the `i_c = 0`
branch of `CascadeLanding` — the branch where every head-conjugator letter is
absorbed before the landing chunk's relator territory.  This file opens the
other one, `i_c > 0`, where conjugator letters eat into the landing factor's
relator letters and pieces bound nothing.

## L-reapp: eaten letters are conserved

At the junction of two adjacent tail factors, whatever the second conjugator
eats off the first palindrome comes back verbatim at the far end of the second
palindrome.  The reason is the mirror in `palindrome c' t' = c' ++ t' ++ invRev
c'`: if the eaten block is `invRev m`, so that `c' = invRev m ++ rest`, then

    invRev c' = invRev rest ++ m,

and the `m` sits at the very end.  Nothing is destroyed, only moved — the same
suffix-mirror computation as `GreendlingerOverlap.invRev_eaten_block`, applied
at an internal junction rather than at the head.

The statement is positional on purpose.  The `μ + j > |t₁|` case — where the
head relator is too far gone for the landing disjunct and the located
conclusion has to come from a later factor — consumes the *position* of the
reappeared copy, not merely its existence, because `GreendlingerAt` is located.
So the form to hand it is the explicit decomposition, whose prefix length is
the position and whose last block is the copy.

The hypothesis `c' = invRev m ++ rest` encodes the junction and carries the
side condition `|m| ≤ |c'|` for free.  A junction that ate *past* `c'` into the
relator would be a different statement: relator letters are then genuinely
destroyed and nothing reappears.

## L-red: the coincidence is void by reducedness, not by collapse

In the `i_c = 0` branch the coincidence had to be excluded by minimality — two
factors spelling mutually inverse elements can be deleted together.  Here it is
cheaper.  If the match past the head conjugator exceeds every piece then the
alignment is exact, `invRev t = t'.rotate i`, and the last letter of the head
conjugator is the letter of `t'` at position `i - 1`.  That is the same letter
as the last letter of `t'.rotate i`, which is the inverse of the first letter
of `t` — so `c ++ t` carries a letter beside its own inverse and the head
palindrome is not reduced.  Reducedness of that palindrome is a standing
hypothesis of `CascadeLanding`, so the coincidence never arises.

No minimality, no small cancellation: the whole argument is that a rotation by
`i` puts `t'[i-1]` at the end.  `ReducednessVoidsCoincidence` states it as a
predicate, since the proof is not written yet; its conclusion is deliberately
the shape `GreendlingerCoincidence.invRev_ne_rotate_of_minimal` produces, so
the two branches feed one downstream slot and the assembly never has to know
which of them discharged the coincidence.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## L-reapp: the junction reappearance, positionally -/

/-- **Eaten letters reappear at the far end.**  If the second conjugator opens
with the inverse of a block `m` — which is what it means for `m` to have been
eaten off the previous palindrome at the junction — then `m` itself is the last
block of the second palindrome.

The decomposition is the statement: the prefix names the position, the final
block names the copy. -/
theorem palindrome_eq_append_reappearance {c' t' m rest : List (α × Bool)}
    (hc' : c' = FreeGroup.invRev m ++ rest) :
    palindrome c' t'
      = (FreeGroup.invRev m ++ rest ++ t' ++ FreeGroup.invRev rest) ++ m := by
  unfold palindrome
  rw [hc', FreeGroup.invRev_append, FreeGroup.invRev_invRev]
  simp only [List.append_assoc]

/-- The reappeared copy is a suffix of the palindrome it comes back in. -/
theorem reappearance_suffix {c' t' m rest : List (α × Bool)}
    (hc' : c' = FreeGroup.invRev m ++ rest) :
    m <:+ palindrome c' t' :=
  ⟨_, (palindrome_eq_append_reappearance hc').symm⟩

/-- **The position of the reappeared copy**, which is what the located
conclusion consumes: the copy begins after `|m| + |rest| + |t'| + |rest|`
letters. -/
theorem length_reappearance_prefix {t' m rest : List (α × Bool)} :
    (FreeGroup.invRev m ++ rest ++ t' ++ FreeGroup.invRev rest).length
      = m.length + rest.length + t'.length + rest.length := by
  simp only [List.length_append, FreeGroup.invRev_length]

/-- The palindrome's length, split at the reappearance. -/
theorem length_palindrome_reappearance {c' t' m rest : List (α × Bool)}
    (hc' : c' = FreeGroup.invRev m ++ rest) :
    (palindrome c' t').length
      = (m.length + rest.length + t'.length + rest.length) + m.length := by
  rw [palindrome_eq_append_reappearance hc', List.length_append,
    length_reappearance_prefix]

/-! ## L-red: reducedness voids the (β) coincidence -/

/-- **OPEN — L-red, as a predicate on the alphabet.**  In the `i_c > 0` regime
the coincidence cannot happen, and reducedness alone refutes it.

`halign` is the (β) alignment: the last `i` letters of the head conjugator are
the opening `i` letters of the landing rotation.  Per the interface note of
`GreendlingerCoincidence`, the conjugator meant here is the effective one — the
head conjugator as it appears in the tail word — so a caller assembling this
must take the overhang against that, not against a bare factor conjugator.

The proof to write, entirely elementary:

* `halign` gives `c.getLast = t'[i - 1]`, the last letter of the aligned block;
* `t'.rotate i` ends with `t'[i - 1]`, since rotating by `i` moves the first
  `i` letters to the back;
* so the coincidence gives `c.getLast = (invRev t).getLast`, and the last
  letter of `invRev t` is the inverse of the first letter of `t`;
* hence `c ++ t` places a letter beside its inverse, contradicting
  `FreeGroup.IsReduced (palindrome c t)`.

The index origin is the landing CHUNK, not the relator word.  `i` counts
letters eaten into the chunk's relator territory, and that territory begins at
rotation offset `k` of `t'` whenever the previous junction consumed the
landing factor's conjugator entirely plus a prefix of its relator — so the
alignment is against `t'.rotate k` and the coincidence reads
`t'.rotate (k + i)`.  Stating it at general `k` is what lets the assembly
typecheck against whatever bookkeeping it has: the alternative, rotating the
factor's relator word to make `k = 0`, would perturb that factor's conjugator
and weight, which a minimality argument must not do.  The unrotated form is
the `k = 0` instance. -/
def ReducednessVoidsCoincidence (α : Type*) : Prop :=
  ∀ (c t t' : List (α × Bool)) (i k : ℕ),
    FreeGroup.IsReduced (palindrome c t) → 0 < i → i ≤ c.length →
    c.drop (c.length - i) <+: t'.rotate k →
    FreeGroup.invRev t ≠ t'.rotate (k + i)

/-- The (β) coincidence discharge, in the shape the landing analysis consumes:
the same conclusion `GreendlingerCoincidence.invRev_ne_rotate_of_minimal`
produces for the `i_c = 0` branch, so one slot serves both. -/
theorem invRev_ne_rotate_of_reduced (hred : ReducednessVoidsCoincidence α)
    {c t t' : List (α × Bool)} {i k : ℕ}
    (hpal : FreeGroup.IsReduced (palindrome c t))
    (hi : 0 < i) (hic : i ≤ c.length)
    (halign : c.drop (c.length - i) <+: t'.rotate k) :
    FreeGroup.invRev t ≠ t'.rotate (k + i) :=
  hred c t t' i k hpal hi hic halign

end SmallCancellationRouter
end GroupApproximation
