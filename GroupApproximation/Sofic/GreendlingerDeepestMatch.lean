import GroupApproximation.Sofic.GreendlingerCascade
import GroupApproximation.Sofic.GreendlingerOverlap

/-!
# The deepest eaten letters are relator letters, and the landing they force

`GreendlingerCascade` reduces the gate to `CascadeLanding`: at the head of a
minimal expression whose leading cancellation reaches past its own trailing
conjugator, either enough of the leading rotation survives for the located
conclusion, or the block stops in a later factor within a sixth of that
factor's rotation past its conjugator.

This file supplies the positional fact that splits that hypothesis in two, and
discharges the half it makes accessible.

## The orientation

The head palindrome is `c ++ t ++ invRev c`, and the block `M` it loses is a
suffix of it.  Once `M` is longer than the trailing conjugator it contains all
of it, so `M = E ++ invRev c` with `E` a suffix of the rotation, and taking
formal inverses

    invRev M = c ++ invRev E.

The eaten prefix of the tail word therefore reads *conjugator letters first,
relator letters last*: positions `[0, |c|)` are matched against `c`, positions
`[|c|, |c| + |E|)` against `t`, and `|E| = |M| - |c| ≥ 1` in the regime.  So
whichever chunk of the tail contains the last eaten position has its deepest
eaten letters matched relator-against-relator, never against the conjugator.

`eaten_prefix_orientation` is that statement and `invRev_eaten_drop` is its
positional form.  Neither is new mathematics: both are compositions of
`GreendlingerOverlap.eaten_split`, `eaten_suffix_of_le` and
`invRev_eaten_block`, which already prove the three halves separately, and
`GreendlingerOverlap.exists_overlap_of_cancellation` already performs the same
composition internally on its way to a stronger conclusion.  What is new is
only that the fact now has a name, so the case split below can cite it.

## The case split, and the half discharged here

The intrusion of the block past the landing factor's conjugator splits as
`i = i_c + i_t`, where `i_t` counts letters matched against `t` — the deep ones
— and `i_c` counts head-conjugator letters that overran every intermediate
chunk.  The orientation says `i_t ≥ 1` always.

* **`i_c = 0`** — every conjugator letter is absorbed before the landing
  chunk's relator territory, so the intrusion is exactly the relator segment
  `invRev E`.  That segment is a common prefix of two symmetrized relators read
  cyclically, so it is a piece unless the two coincide, and `C'(1/6)` turns the
  piece into the sixth-bound `LandsIn` demands.  This is
  `landsIn_of_conjugatorAbsorbed` and `cascadeLanding_of_conjugatorAbsorbed`
  below, and both are proved.
* **`i_c > 0`** — conjugator letters eat into the landing factor's relator
  letters, where pieces bound nothing.  Untouched here; that is the regime the
  design note isolates as the concentrated risk of the lane.

The coincidence branch is the one place minimality is spent.  For an *adjacent*
landing factor `GreendlingerOverlap.mk_palindrome_mul_eq_one_of_coincidence`
plus `IsMinimalConjExpr.mul_ne_one` already close it; for a landing factor
further down the cascade the corresponding statement is
`GreendlingerThreeFactor.conj_ne_inv_of_minimal`, which forbids cancellation
between any two factors and not only neighbours.  Both are taken as the
distinctness hypothesis `hne` here rather than re-derived, so that this file
owes nothing to the shape of the expression between the two factors.

Unconditional apart from the `C'(1/6)` hypothesis, which enters exactly where
the piece bound is read.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The orientation of the eaten prefix -/

/-- **The eaten prefix reads conjugator-first, relator-last.**

In the regime where the block outruns the trailing conjugator but not the
rotation, `M = E ++ invRev c` for a suffix `E` of the rotation of length
`|M| - |c| ≥ 1`, and the prefix it destroys in the tail word is `c` followed by
`invRev E`.

Every conjunct is one of `GreendlingerOverlap`'s three splitting lemmas; the
content of the statement is that they hold *together*, which is what pins the
order of the two segments. -/
theorem eaten_prefix_orientation {c t M P' : List (α × Bool)}
    (heq : palindrome c t = P' ++ M)
    (hlow : c.length < M.length)
    (hhigh : M.length ≤ c.length + t.length) :
    ∃ E : List (α × Bool),
      M = E ++ FreeGroup.invRev c ∧
        FreeGroup.invRev M = c ++ FreeGroup.invRev E ∧
        E <:+ t ∧ E.length = M.length - c.length ∧ 0 < E.length := by
  have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
  have hMsuf : M <:+ palindrome c t := ⟨P', heq.symm⟩
  obtain ⟨E, hM, hEsuf⟩ := eaten_split hMsuf (by omega)
  have hMlen : M.length = E.length + (FreeGroup.invRev c).length := by
    rw [hM, List.length_append]
  exact ⟨E, hM, invRev_eaten_block hM,
    eaten_suffix_of_le hM hEsuf (by omega), by omega, by omega⟩

/-- **The positional form.**  Dropping the conjugator's worth of letters from
the eaten prefix leaves exactly the relator segment: the deep eaten positions
are the ones matched against the rotation. -/
theorem invRev_eaten_drop {c E M : List (α × Bool)}
    (hM : M = E ++ FreeGroup.invRev c) :
    (FreeGroup.invRev M).drop c.length = FreeGroup.invRev E := by
  rw [invRev_eaten_block hM, List.drop_left]

/-! ## 2.  The intrusion is doubly piece-bounded -/

/-- **The relator segment is a piece, and both relators bound it.**

`invRev E` prefixes the inverted head rotation because inversion turns suffixes
into prefixes, and it prefixes the landing rotation by hypothesis; distinctness
makes it a piece, and `C'(1/6)` then bounds it against *each* of the two
relators.  The bound against the head rotation is the one the length
bookkeeping of `CascadeLanding` needs; the bound against the landing rotation
is the one `LandsIn` stores. -/
theorem six_mul_intrusion_lt {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {t t' E : List (α × Bool)} {k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t)
    (hintr : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k) :
    6 * E.length < t.length ∧ 6 * E.length < t'.length := by
  have hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E) :=
    isPiece_of_overlap ht ht' hEt hintr hne
  have hEl : (FreeGroup.invRev E).length = E.length := FreeGroup.invRev_length
  have hhead : 6 * (FreeGroup.invRev E).length < (FreeGroup.invRev t).length :=
    six_mul_length_lt_of_isPiece hmetric hpiece (invRev_mem_symmetrization ht)
      (invRev_prefix_of_suffix hEt)
  have hland : 6 * (FreeGroup.invRev E).length < (t'.rotate k).length :=
    six_mul_length_lt_of_isPiece hmetric hpiece
      (rotate_mem_symmetrization ht' k) hintr
  have htl : (FreeGroup.invRev t).length = t.length := FreeGroup.invRev_length
  have hrl : (t'.rotate k).length = t'.length := by simp
  omega

/-! ## 3.  The landing, when the conjugator is absorbed -/

/-- **The `i_c = 0` case produces the landing site.**

The intrusion is the relator segment alone, so the piece bound of the previous
theorem *is* the sixth-bound field of `LandsIn`, with `i = |E|`.  Everything
else in `LandsIn` is cascade bookkeeping about where the landing factor sits,
which this theorem takes as given and does not touch. -/
theorem landsIn_of_conjugatorAbsorbed [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {t t' c' E A M : List (α × Bool)} {k N : ℕ}
    {e f : List (FreeGroup α × List (α × Bool))}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t)
    (hintr : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k)
    (hf : f.length < e.length)
    (hV : (conjEval e).toWord
      = A ++ (conjEval ((FreeGroup.mk c', t') :: f)).toWord.drop N)
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (hmin' : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
      (conjEval ((FreeGroup.mk c', t') :: f)))
    (hN : N ≤ c'.length + E.length)
    (hfit : M.length + N ≤ A.length + c'.length + E.length) :
    LandsIn R M.length (conjEval e).toWord e.length :=
  ⟨c', t', f, A, N, E.length, hf, hV, ht', hredp', hmin',
    (six_mul_intrusion_lt hmetric ht ht' hEt hintr hne).2, hN, hfit⟩

/-- **`CascadeLanding` on the `i_c = 0` branch.**

The conclusion is `CascadeLanding`'s own disjunction, taken on the landing
side, for a head whose block outruns its trailing conjugator but not its
rotation and whose intrusion into the landing factor consists of relator
letters only.  The length conjunct is where the *head* half of the double piece
bound is spent: the intrusion and the surviving stretch `j` are each under a
sixth of the head rotation, so together they fit inside it.

Named so that the `i_c > 0` branch can be proved separately and the two
combined without either touching the other. -/
theorem cascadeLanding_of_conjugatorAbsorbed [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {c t t' c' E A M P' B' : List (α × Bool)} {k N j : ℕ}
    {e f : List (FreeGroup α × List (α × Bool))}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hlow : c.length < M.length)
    (hhigh : M.length ≤ c.length + t.length)
    (hj : 6 * j < t.length)
    (hM : M = E ++ FreeGroup.invRev c)
    (hintr : FreeGroup.invRev E <+: t'.rotate k)
    (hne : FreeGroup.invRev t ≠ t'.rotate k)
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
  -- the orientation lemma identifies the segment `E` the caller named, and
  -- places it inside the rotation
  have hEt : E <:+ t := by
    obtain ⟨E', hM', -, hE't, -, -⟩ := eaten_prefix_orientation heq hlow hhigh
    have hEE : E = E' := List.append_cancel_right (hM.symm.trans hM')
    rw [hEE]
    exact hE't
  have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
  have hMlen : M.length = E.length + (FreeGroup.invRev c).length := by
    rw [hM, List.length_append]
  have hbound := (six_mul_intrusion_lt hmetric ht ht' hEt hintr hne).1
  refine Or.inr ⟨by omega, ?_⟩
  exact landsIn_of_conjugatorAbsorbed hmetric ht ht' hEt hintr hne hf hV hredp'
    hmin' hN hfit

end SmallCancellationRouter
end GroupApproximation
