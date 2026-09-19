import GroupApproximation.Sofic.GreendlingerDeepInvariant
import GroupApproximation.Sofic.GreendlingerSharpWindow
import GroupApproximation.Sofic.GreendlingerSharpBackLoss

/-!
# The drop-route invariant at an arbitrary constant

`GreendlingerDeepInvariant` carries the weakened invariant — the one in which
the arc is read at position `0` and the head-denominated offset conjunct is
gone — and it is already twinned almost everywhere: `DeepWindowDrop`,
`DeepArcDrop`, `CascadeLandingDrop`, `DeepCompositeLands`, the descent and both
gates all have their `λ`-counterparts in that file.  Three statements do not,
and all three sit on the drop route:

* §3's `exists_postJunction_drop`, which reads `C'(1/6)` and `6i < |t|`.  The
  sharp descent `greendlingerAtSharp_drop_of_lands` already calls it through
  `GreendlingerDeepVacuitySharp.metricSmallCancellation_of_le` and
  `six_mul_lt_of_lam_lt`, inline; §1 below names that composition, so a prover
  working in the sharp hypothesis set does not have to rediscover it.
* §5's `cascadeLandingDrop_of_deepWindowDrop_of_landing`.  Its twin exists only
  as the two-step composition performed inside
  `GreendlingerSharpDropGate.sharpGreendlingerGate_of_windowDropSharp_of_landingSharp`;
  §2 below names it, so the drop route has the same one-line entry point at
  `λ` that it has at a sixth.
* §8's `greendlingerAt_of_landing_survivor`, the last mile of the window route.
  §3 below twins it, and also states its **payload** form, which is literally
  the conclusion body of `DeepWindowDropSharp`.

## What §3 is and is not

It is the partial producer, and the scope note of the `λ`-free version applies
verbatim.  The two hypotheses are the two ends of the landing rotation:

* the **front** bound `D − |c₃| < λ|t₃|` is the incoming block's intrusion,
  which `GreendlingerSharpRigidity.intrusion_lt_of_forward_sharp` supplies at
  any depth;
* the **back** bound `|c₃| + |t₃| − |P₃| < λ|t₃|` is the landing factor's own
  loss, which `GreendlingerSharpBackLoss.back_lt_of_backward_sharp` and
  `back_lt_of_forward_sharp` supply *only through their `hintr` field* — the
  landing factor's eaten stretch reaching the next factor's relator letters,
  which is exactly what fails when that factor is itself deep.

So this discharges the drop-form arc at a **shallow** landing factor and says
nothing about a deep one.  `DeepWindowDropSharp` quantifies over both, so
nothing here discharges it; what is missing between them is the induction that
hands a deep landing factor to its own stage of the descent, which is what §§6-7
of the `λ`-free file arrange for `DeepCompositeLands` and what no statement
arranges for `DeepWindowDrop`.

## Where `0 ≤ lam` is read

Only in §3, and only through the sharp two-piece survivor count
`GreendlingerSharpWindow.sharp_survivor_of_two_pieces`, which produces a
survivor longer than `(1 − 2λ)|t₃|`
and the arc asks for `(1 − 3λ)|t₃|`, and the whole `λ|t₃|` of slack between
them is nonnegative exactly when `λ` is.  At `λ = 1/6` that comparison was
invisible inside `omega`.  No sign or upper bound on `λ` is read anywhere else
here; §1 reads `λ ≤ 1/6` because the junction kill it calls is stated in the
half-form hypothesis set, and §2 reads nothing at all.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  Past the adjacent junction, at an arbitrary constant -/

/-- **The `λ`-twin of `GreendlingerDeepInvariant.exists_postJunction_drop`.**

In the deep regime the adjacent junction is empty, so what survives the head's
cancellation is a drop of the word of the expression past it — at any tail
length, and now at any `λ ≤ 1/6`.

Nothing about the junction is re-examined.  The junction kill is
`GreendlingerDeepVacuity.not_deep_confined`, which is stated in the half-form
hypothesis set; `metricSmallCancellation_of_le` weakens `C'(λ)` to `C'(1/6)`
and `six_mul_lt_of_lam_lt` weakens the sharp offset to the half-form one, and
those two substitutions are the whole of the twin.  This is the composition the
sharp descent already performs inline, given a name. -/
theorem exists_postJunction_drop_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    {c t P' M B' : List (α × Bool)} {e : List (FreeGroup α × List (α × Bool))}
    {g : FreeGroup α} {i : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (ht : t ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i) :
    ∃ (c₂ t₂ : List (α × Bool)) (f : List (FreeGroup α × List (α × Bool)))
      (D : ℕ),
      t₂ ∈ symmetrization R ∧
        FreeGroup.IsReduced (palindrome c₂ t₂) ∧
        IsMinimalConjExpr R
          ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g ∧
        f.length < e.length ∧ B' = (conjEval f).toWord.drop D :=
  exists_postJunction_drop hR hRne (metricSmallCancellation_of_le hlam hmetric)
    hmin ht hredp heq htail hlow (six_mul_lt_of_lam_lt hlam hi) hgt

/-! ## 2.  The weakened invariant, from the window and the landing -/

/-- **The `λ`-twin of
`GreendlingerDeepInvariant.cascadeLandingDrop_of_deepWindowDrop_of_landing`.**

The drop route's one-line entry point at an arbitrary constant: a sharp window
family and a sharp landing family give the sharp weakened invariant, and from
there `GreendlingerSharpDropGate` gives the gate.  Both arguments are
hypotheses; nothing here discharges either. -/
theorem cascadeLandingDropSharp_of_deepWindowDropSharp_of_landingSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hwin : DeepWindowDropSharp R lam) (hland : LandingProductionSharp R lam) :
    CascadeLandingDropSharp R lam :=
  cascadeLandingDropSharp_of_deepArcDropSharp_of_landingSharp
    (deepArcDropSharp_of_deepWindowDropSharp hwin) hland

/-! ## 3.  The window route's last mile, at an arbitrary constant

`GreendlingerDeepInvariant` §8 reads the arc off a landing factor's survivor
from two piece bounds, one per end of the landing rotation.  Both bounds are
already twinned — the front one in `GreendlingerSharpRigidity`, the back one in
`GreendlingerSharpBackLoss` — and the surgery that exhibits the window,
`window_of_palindrome_survivor`, names no constant, so the producer twins by
substituting `greendlingerAtSharp_of_two_piece_window` for its `λ`-free
counterpart.

The asymmetry between the two bounds is the whole content of the scope note: the
front one holds at any depth, the back one says the landing factor is not itself
deep. -/

/-- **The sharp arc from a landing factor's survivor, from the two piece
bounds.**  The `λ`-twin of
`GreendlingerDeepInvariant.greendlingerAt_of_landing_survivor`.

`P₃` is what the landing factor keeps of its palindrome after its own
cancellation, `B₃` is the rest of the word, and `D` is where the block from
above stops inside it.  The two bounds are the intrusions at the two ends,
`D − |c₃|` from the front and `|c₃| + |t₃| − |P₃|` from the back, each now
measured against `λ|t₃|` rather than against a sixth of `|t₃|`.

`0 ≤ lam` is read only by the two-piece survivor count, which needs the slack
between `(1 − 2λ)` and `(1 − 3λ)` to be nonnegative.

**Scope.**  The back bound is the landing factor's own loss, and it is available
only where that factor is shallow; this is therefore the drop-form arc at a
shallow landing factor, and not a discharge of the deep branch.  Where the
landing factor is deep, the arc has to come from its own stage of the descent. -/
theorem greendlingerAtSharp_of_landing_survivor {R : Set (List (α × Bool))}
    {lam : ℚ} {c₃ t₃ P₃ M₃ B₃ : List (α × Bool)} {D : ℕ}
    (hlam : 0 ≤ lam)
    (ht₃ : t₃ ∈ symmetrization R)
    (heq : palindrome c₃ t₃ = P₃ ++ M₃)
    (hc : c₃.length ≤ D) (hD : D ≤ P₃.length)
    (hP : P₃.length ≤ c₃.length + t₃.length)
    (hfront : ((D - c₃.length : ℕ) : ℚ) < lam * (t₃.length : ℚ))
    (hback : ((c₃.length + t₃.length - P₃.length : ℕ) : ℚ)
      < lam * (t₃.length : ℚ)) :
    GreendlingerAtSharp R lam 0 ((P₃ ++ B₃).drop D) := by
  rw [window_of_palindrome_survivor heq hc hD hP]
  have hlen : P₃.length - D
      = t₃.length - (D - c₃.length)
        - (c₃.length + t₃.length - P₃.length) := by omega
  rw [hlen]
  refine greendlingerAtSharp_of_two_piece_window (A := []) (C := B₃)
    (i := D - c₃.length) (k := c₃.length + t₃.length - P₃.length) hlam ht₃ ?_
    (Nat.zero_le _) (by omega) hfront hback
  rw [List.nil_append]

/-- **The same, in the shape `DeepWindowDropSharp` asks for.**

The predicate does not want an arc: it wants a symmetrized relator, a window of
it longer than `(1 − 3λ)` of it, and the decomposition exhibiting that window
inside what survives.  This is that payload, with the landing factor's own
rotation supplied as the relator, `A = []` and `C = B₃`.

So a prover who has arranged the induction that turns
`DeepWindowDropSharp`'s hypotheses into a landing factor with a survivor
decomposition, a front bound and a back bound can finish with this and nothing
else.  The three arranging steps are the open part; this is not. -/
theorem exists_windowSharp_of_landing_survivor {R : Set (List (α × Bool))}
    {lam : ℚ} {c₃ t₃ P₃ M₃ B₃ : List (α × Bool)} {D : ℕ}
    (hlam : 0 ≤ lam)
    (ht₃ : t₃ ∈ symmetrization R)
    (heq : palindrome c₃ t₃ = P₃ ++ M₃)
    (hc : c₃.length ≤ D) (hD : D ≤ P₃.length)
    (hP : P₃.length ≤ c₃.length + t₃.length)
    (hfront : ((D - c₃.length : ℕ) : ℚ) < lam * (t₃.length : ℚ))
    (hback : ((c₃.length + t₃.length - P₃.length : ℕ) : ℚ)
      < lam * (t₃.length : ℚ)) :
    ∃ (s A C : List (α × Bool)) (k m : ℕ),
      s ∈ symmetrization R ∧
        (P₃ ++ B₃).drop D = A ++ (s.drop k).take m ++ C ∧
        k + m ≤ s.length ∧
        (1 - 3 * lam) * (s.length : ℚ) < (m : ℚ) := by
  refine ⟨t₃, [], B₃, D - c₃.length, P₃.length - D, ht₃, ?_, ?_, ?_⟩
  · rw [window_of_palindrome_survivor heq hc hD hP, List.nil_append]
  · omega
  · have hlen : t₃.length - (D - c₃.length)
        - (c₃.length + t₃.length - P₃.length) = P₃.length - D := by omega
    have hb := sharp_survivor_of_two_pieces (t₃ := t₃)
      (i := D - c₃.length) (k := c₃.length + t₃.length - P₃.length)
      hlam (by omega) hfront hback
    rw [hlen] at hb
    exact hb

end SmallCancellationRouter
end GroupApproximation
