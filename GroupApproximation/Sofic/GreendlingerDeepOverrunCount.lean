import GroupApproximation.Sofic.GreendlingerDeepThreeFactor

/-!
# The overrun count: what pins the depth, and what does not

`GreendlingerDeepThreeFactor` reduces the three-factor overrun to one
inequality, `2(i + d) < |t₃|`, and splits it into a piece bound on the intrusion
`i` and a bound on the overrun depth `d`.  This file settles the second half —
and finds that it is pinned to the **wrong rotation**.

## The depth is the head's deficiency

Writing the block as `M = E ++ invRev c` with `E` a suffix of the head rotation,

    d = |M| + j − (|c| + |t|) = |E| + j − |t| ≤ j,

because `|E| ≤ |t|`.  That is `deep_depth_le_offset`, and with `6j < |t|` it
gives `d < |t| / 6`: the overrun depth is bounded, but by a sixth of the **head**
rotation, and by nothing at all involving the rotation the block lands in.

## The offset is a free parameter

`GreendlingerCascade` manufactures `j` in two places.  The gate calls the
descent at `j = 0`; the recursion calls it at `j = i`, the landing offset stored
in `LandsIn`, whose only constraint is `6 i < |t'|` for the landing factor's own
rotation — which is the next stage's head rotation.  So at every stage the
offset carries exactly the hypothesis the predicate states, `6 j < |t|`, and
nothing more.  It is free in that range, and in particular may sit just under a
sixth of a head rotation of any size.

## Consequently the count needs a length ratio

`two_mul_lt_of_relator_ratio` is the exact arithmetic: from `6 i < |t₃|`,
`6 j < |t|` and `d ≤ j`, the inequality `2(i + d) < |t₃|` follows as soon as

    |t| ≤ 2 · |t₃|,

and `greendlingerAt_of_landing_ratio` is the resulting producer — the
three-factor overrun closes whenever the head rotation is at most twice the
landing rotation.  The same ratio is what the sharp form needs: there the
budget is `i + d < 3λ|t₃|`, split as `i < λ|t₃|` and `d < 2λ|t₃|`, and `d ≤ j`
with `j < λ|t|` turns the second into `|t| ≤ 2|t₃|` again, with the `λ` dividing
out.  So the ratio is constant-free.

Nothing here supplies that ratio, and nothing in `DeepArcSource`'s hypotheses
implies it: a family may carry relators of wildly different lengths and still be
`C'(1/6)`.  Where the ratio fails, the surviving word is a suffix of the last
palindrome whose only relator is `t₃`, every arc of `t₃` is shorter than the
offset the conclusion demands, and no arc at all is available — so the deficit is
in the located offset, not in the count.

## The coincidence, killed at any depth

The one obstruction reported earlier as blocked is not.  The containment does
run the wrong way — the landing factor's effective conjugator word **extends**
the head conjugator — but that is the hypothesis of
`GreendlingerOverlap.mk_palindrome_mul_eq_one_of_coincidence'` rather than of its
unprimed twin, and `GreendlingerThreeFactor.conj_ne_inv_of_minimal` already
forbids cancellation between factors at any distance.  Composing the two gives
`ne_rotate_invRev_of_minimal_forward`, the mirror of
`GreendlingerCoincidence.invRev_ne_rotate_of_minimal`, which refutes the
coincidence in the orientation the overrun actually produces.  It is proved for
an arbitrary block `e₁` of factors in between, so it is not a three-factor
statement.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The overrun depth is bounded by the offset -/

/-- **The depth is the head's own deficiency.**  With the block written as
`E ++ invRev c`, the amount by which it overruns the head palindrome is
`|E| + j − |t|`, and `E` is a suffix of `t`, so the overrun never exceeds the
offset it was launched with.

This is the sharpest bound available on `d`, and it is pinned to the head
rotation.  Nothing here — and nothing in `DeepArcSource` — relates it to the
rotation of the factor the block lands in. -/
theorem deep_depth_le_offset {c t M E : List (α × Bool)} {j : ℕ}
    (hM : M = E ++ FreeGroup.invRev c) (hEt : E <:+ t) :
    M.length + j - (c.length + t.length) ≤ j := by
  obtain ⟨z, hz⟩ := hEt
  have hElen : z.length + E.length = t.length := by
    have hb := congrArg List.length hz
    rw [List.length_append] at hb
    exact hb
  have hMlen : M.length = E.length + c.length := by
    rw [hM, List.length_append, FreeGroup.invRev_length]
  omega

/-! ## 2.  The count, and the ratio it needs -/

/-- **The three-factor count, from a length ratio.**  A piece-bounded intrusion
and an offset under a sixth of the head rotation give the landing inequality as
soon as the head rotation is at most twice the landing rotation.

The ratio is not decoration: `d` is bounded only through `j`, and `j` only
through `|t|`, so some comparison between `|t|` and `|t₃|` has to enter, and this
is the weakest one that works. -/
theorem two_mul_lt_of_relator_ratio {t t₃ : List (α × Bool)} {i j d : ℕ}
    (hi : 6 * i < t₃.length) (hj : 6 * j < t.length) (hd : d ≤ j)
    (hratio : t.length ≤ 2 * t₃.length) :
    2 * (i + d) < t₃.length := by
  omega

/-- **The three-factor overrun, closed under the ratio.**  Everything the
configuration supplies is here — the block's orientation, the offset bound, the
piece bound on the intrusion — plus the one comparison the count cannot do
without.

Read the other way, this locates the hole exactly: drop `hratio` and the arc is
no longer available from `t₃`, which at three factors is the only relator the
surviving word contains. -/
theorem greendlingerAt_of_landing_ratio {R : Set (List (α × Bool))}
    {c t c₃ t₃ M E : List (α × Bool)} {N j : ℕ}
    (ht₃ : t₃ ∈ symmetrization R)
    (hM : M = E ++ FreeGroup.invRev c) (hEt : E <:+ t)
    (hj : 6 * j < t.length)
    (hpiece : 6 * (N - c₃.length) < t₃.length)
    (hratio : t.length ≤ 2 * t₃.length) :
    GreendlingerAt R (M.length + j - (c.length + t.length))
      ((palindrome c₃ t₃).drop N) := by
  refine greendlingerAt_of_landing_drop ht₃ ?_
  have hd := deep_depth_le_offset (j := j) hM hEt
  exact two_mul_lt_of_relator_ratio hpiece hj hd hratio

/-! ## 3.  The coincidence in the overrun orientation -/

/-- **No cancelling pair, when the effective conjugator extends the head one.**

`GreendlingerCoincidence.invRev_ne_rotate_of_minimal` refutes the coincidence
when the head conjugator overhangs the landing factor's effective conjugator,
`c = d ++ q`.  In an overrun the containment is the other way round, `d = c ++ y`
with `y` a stretch of head-relator letters, and that orientation is exactly what
`GreendlingerOverlap.mk_palindrome_mul_eq_one_of_coincidence'` computes.

The rest is unchanged: naming the effective conjugator turns the pair into a
product of two palindromes, and
`GreendlingerThreeFactor.conj_ne_inv_of_minimal` forbids such a product for
factors at **any** distance — deleting both and conjugating everything between
them by the head leaves a strictly shorter expression, and a minimal expression
has none.

`e₁ = []` is the adjacent case, where this reproves the coincidence step of
`GreendlingerDeepVacuity.not_deep_overhang_adjacent`; that lemma's other half,
the rigidity that produces the coincidence in the first place, is not restated
here. -/
theorem ne_rotate_invRev_of_minimal_forward [DecidableEq α]
    {R : Set (List (α × Bool))} {c t t' c' dw y : List (α × Bool)}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c', t') :: f))) g)
    (hd : FreeGroup.mk dw = conjEval e₁ * FreeGroup.mk c')
    (hcy : dw = c ++ y) (hy : y <+: FreeGroup.invRev t) :
    t' ≠ (FreeGroup.invRev t).rotate y.length := by
  intro hrot
  have hcoin := mk_palindrome_mul_eq_one_of_coincidence' hcy hy hrot
  refine conj_ne_inv_of_minimal hmin ?_
  have hexp : conjEval e₁ * (FreeGroup.mk c' * FreeGroup.mk t'
        * (FreeGroup.mk c')⁻¹) * (conjEval e₁)⁻¹
      = FreeGroup.mk dw * FreeGroup.mk t' * (FreeGroup.mk dw)⁻¹ := by
    rw [hd]
    group
  rw [hexp, ← mk_palindrome, ← mk_palindrome]
  exact hcoin

/-! ## 4.  The orientation package the overrun does not get for free -/

/-- **The overrun-side swallow bound, named.**  `GreendlingerRegime`'s
`swallow_bound_of_minimal` proves `|M| ≤ |c| + |t|` from the *confined*
hypothesis `palindrome c' t' = invRev M ++ B'`.  In the overrun regime that
hypothesis is exactly what fails, so the bound is not available and the block
may in principle eat the whole head rotation and part of the head's leading
conjugator.

Every statement that names the eaten stretch `E` depends on this — the
orientation itself, `five_mul_lt_six_mul_eaten`, `eq_rotate_of_deep_eaten`,
`greendlingerAt_of_deep_arc` and `deep_depth_le_offset` all do — so it is named
here rather than assumed silently.  `GreendlingerRegime.exists_swallow_split`
describes what the failing case looks like: `invRev M = c ++ invRev t ++ invRev c₂`,
so the whole inverted head rotation sits in the tail word, and the depth becomes
`|c₂| + j`, which no bound above controls. -/
def DeepOverrunSwallowBound [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
  ∀ (c t c' t' M B' : List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) (j : ℕ),
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g →
    t ∈ symmetrization R → t' ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c' t') →
    M <:+ palindrome c t →
    (conjEval ((FreeGroup.mk c', t') :: f)).toWord
      = FreeGroup.invRev M ++ B' →
    ¬ (FreeGroup.invRev M <+: palindrome c' t') →
    c.length < M.length → 6 * j < t.length →
    c.length + t.length < M.length + j →
    M.length ≤ c.length + t.length

/-- **Everything the deep regime gives, once the swallow bound is in hand.**
The orientation, the five-sixths bound and the depth bound in one package,
stated against the suffix form of the block that the seed predicates carry.

This is what a frame should hand a deep-regime argument: it is the whole of the
geometry, and its only non-trivial input is the bound named above. -/
theorem exists_deep_orientation {c t M : List (α × Bool)} {j : ℕ}
    (hMsuf : M <:+ palindrome c t)
    (hlow : c.length < M.length)
    (hhigh : M.length ≤ c.length + t.length)
    (hj : 6 * j < t.length)
    (hgt : c.length + t.length < M.length + j) :
    ∃ E : List (α × Bool),
      M = E ++ FreeGroup.invRev c ∧
        FreeGroup.invRev M = c ++ FreeGroup.invRev E ∧
        E <:+ t ∧ 5 * t.length < 6 * E.length ∧
        M.length + j - (c.length + t.length) ≤ j := by
  obtain ⟨P', hP'⟩ := hMsuf
  obtain ⟨E, hM, hinvM, hEt, -, -⟩ :=
    eaten_prefix_orientation hP'.symm hlow hhigh
  exact ⟨E, hM, hinvM, hEt, five_mul_lt_six_mul_eaten hM hj hgt,
    deep_depth_le_offset hM hEt⟩

end SmallCancellationRouter
end GroupApproximation
