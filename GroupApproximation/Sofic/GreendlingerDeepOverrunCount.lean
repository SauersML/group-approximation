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

/-! ## 0.  The balanced-family invariant -/

/-- Every relator in the symmetrized family is at most twice every other one.

This is the precise extra geometry used by the balanced positive presentation:
the presentation pads its finitely many relators to lengths differing by at
most one, and symmetrization preserves length.  Stating the invariant on the
symmetrization avoids repeatedly transporting membership and length through a
rotation or formal inverse at the cancellation sites below. -/
def RelatorLengthRatioTwo (R : Set (List (α × Bool))) : Prop :=
  ∀ r ∈ symmetrization R, ∀ s ∈ symmetrization R,
    r.length ≤ 2 * s.length

theorem RelatorLengthRatioTwo.apply {R : Set (List (α × Bool))}
    (h : RelatorLengthRatioTwo R) {r s : List (α × Bool)}
    (hr : r ∈ symmetrization R) (hs : s ∈ symmetrization R) :
    r.length ≤ 2 * s.length :=
  h r hr s hs

/-- It is enough to balance the finite base family.  Rotation and formal
inversion, the two operations used by `symmetrization`, preserve word length.
-/
theorem relatorLengthRatioTwo_of_base {R : Set (List (α × Bool))}
    (h : ∀ r ∈ R, ∀ s ∈ R, r.length ≤ 2 * s.length) :
    RelatorLengthRatioTwo R := by
  intro r hr s hs
  obtain ⟨r₀, hr₀, n, hrot | hrot⟩ := hr
  · have hlenr : r.length = r₀.length := by rw [hrot, List.length_rotate]
    obtain ⟨s₀, hs₀, m, hsrot | hsrot⟩ := hs
    · have hlens : s.length = s₀.length := by rw [hsrot, List.length_rotate]
      rw [hlenr, hlens]
      exact h r₀ hr₀ s₀ hs₀
    · have hlens : s.length = s₀.length := by
        rw [hsrot, List.length_rotate, FreeGroup.invRev_length]
      rw [hlenr, hlens]
      exact h r₀ hr₀ s₀ hs₀
  · have hlenr : r.length = r₀.length := by
      rw [hrot, List.length_rotate, FreeGroup.invRev_length]
    obtain ⟨s₀, hs₀, m, hsrot | hsrot⟩ := hs
    · have hlens : s.length = s₀.length := by rw [hsrot, List.length_rotate]
      rw [hlenr, hlens]
      exact h r₀ hr₀ s₀ hs₀
    · have hlens : s.length = s₀.length := by
        rw [hsrot, List.length_rotate, FreeGroup.invRev_length]
      rw [hlenr, hlens]
      exact h r₀ hr₀ s₀ hs₀

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

/-- **The sharp three-factor count, from the same length ratio.**

The intrusion consumes less than `λ|t₃|`.  The transported depth is at most
the old offset, hence less than `λ|t|`, and the balanced-family comparison
turns the latter into at most `2λ|t₃|`.  Together they fit strictly inside
the sharp conclusion's full `3λ|t₃|` allowance. -/
theorem cast_add_lt_three_mul_of_relator_ratio
    {lam : ℚ} {t t₃ : List (α × Bool)} {i j d : ℕ}
    (hi : (i : ℚ) < lam * (t₃.length : ℚ))
    (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hd : d ≤ j) (hlam0 : 0 ≤ lam)
    (hratio : t.length ≤ 2 * t₃.length) :
    (i : ℚ) + (d : ℚ) < 3 * lam * (t₃.length : ℚ) := by
  have hdq : (d : ℚ) ≤ (j : ℚ) := by exact_mod_cast hd
  have hratioq : (t.length : ℚ) ≤ 2 * (t₃.length : ℚ) := by
    exact_mod_cast hratio
  have hj' : (d : ℚ) < 2 * lam * (t₃.length : ℚ) := by
    calc
      (d : ℚ) ≤ (j : ℚ) := hdq
      _ < lam * (t.length : ℚ) := hj
      _ ≤ lam * (2 * (t₃.length : ℚ)) :=
        mul_le_mul_of_nonneg_left hratioq hlam0
      _ = 2 * lam * (t₃.length : ℚ) := by ring
  linarith

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

/-- **The sharp landing arc, closed by the balanced-family ratio.**  This is
the sharp twin of `greendlingerAt_of_landing_ratio`.  The bound above supplies
the `3·λ` budget, while `λ ≤ 1/6` makes that budget at most half a relator and
therefore also supplies the list-theoretic fit required by the arc constructor.
-/
theorem greendlingerAtSharp_of_landing_ratio {R : Set (List (α × Bool))}
    {lam : ℚ} {c t c₃ t₃ M E Z : List (α × Bool)} {N j : ℕ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 6)
    (ht₃ : t₃ ∈ symmetrization R)
    (hM : M = E ++ FreeGroup.invRev c) (hEt : E <:+ t)
    (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hpiece : ((N - c₃.length : ℕ) : ℚ) < lam * (t₃.length : ℚ))
    (hratio : t.length ≤ 2 * t₃.length) :
    GreendlingerAtSharp R lam (M.length + j - (c.length + t.length))
      ((t₃ ++ Z).drop (N - c₃.length)) := by
  let i := N - c₃.length
  let d := M.length + j - (c.length + t.length)
  have hd : d ≤ j := by
    dsimp [d]
    exact deep_depth_le_offset (j := j) hM hEt
  have hbound : (i : ℚ) + (d : ℚ) <
      3 * lam * (t₃.length : ℚ) :=
    cast_add_lt_three_mul_of_relator_ratio (by simpa [i] using hpiece) hj hd
      hlam0 hratio
  have ht₃q : (0 : ℚ) ≤ (t₃.length : ℚ) := by positivity
  have hhalf : (3 * lam) * (t₃.length : ℚ)
      ≤ (t₃.length : ℚ) := by
    have hcoef : 3 * lam ≤ 1 := by linarith
    simpa using mul_le_mul_of_nonneg_right hcoef ht₃q
  have hfitq : ((i + d : ℕ) : ℚ) < (t₃.length : ℚ) := by
    rw [Nat.cast_add]
    exact lt_of_lt_of_le hbound (by simpa [mul_assoc] using hhalf)
  have hfit : i + d ≤ t₃.length := by
    exact_mod_cast (le_of_lt hfitq)
  exact greendlingerAtSharp_of_landing_intrusion ht₃ hfit hbound

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
`|c₂| + j`, which no bound above controls.

The hole is narrower than it first appears, and the narrowing is now a theorem.
`GreendlingerRegime.swallow_bound_of_minimal_of_prefix` is that file's argument
with the confinement hypothesis replaced by the only thing it ever read from it,
`c ++ invRev t <+: palindrome c' t'` — the branch that looks like it needs the
whole block discards `invRev c₂` at its second step, and no branch consumes more
than `|c| + |t|` letters of the adjacent palindrome.  So the swallow bound is
available in the overrun regime too, whenever those letters still fit inside the
adjacent palindrome; `swallow_bound_of_minimal` is now the confined instance of
it.

What is left open below is therefore only the residue: the case where the
adjacent factor's survivor is shorter than `c ++ invRev t`, so that not even the
inverted head rotation fits beside the head conjugator before the block runs on. -/
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

/-! ## 5.  The piece bound on the intrusion, at any depth -/

/-- **The intrusion into the landing rotation is a piece.**

This is the step the drop-form descent still needs from the deep regime, and it
is the only one where the eaten stretch is read: the block's deep end matches
head-relator letters against the opening letters of `t₃`, so `t₃.take i` is a
common prefix of `t₃` and of the rotation of `invRev t` the alignment names.  A
common prefix that reached a sixth of `t₃` would force the two to coincide
(`GreendlingerDeepArc.eq_of_sixth_common_prefix`), and the coincidence is
refuted by `ne_rotate_invRev_of_minimal_forward` above — in the orientation the
overrun produces, with the landing factor's effective conjugator extending the
head conjugator.

`e₁` is arbitrary, so this holds at every distance: the landing factor need not
be adjacent to the head, and `GreendlingerCoincidence.exists_effectiveConjugator`
supplies `dw` for any `e₁` and `c₃`.

No bound on `i` is assumed — if the alignment ran past the whole of `t₃` the
`take` would saturate and the same contradiction follows, so the statement is
about the alignment and not about which of the two rotations is longer. -/
theorem six_mul_intrusion_lt_of_forward [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {c t c₃ t₃ dw y : List (α × Bool)} {i : ℕ}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f))) g)
    (ht : t ∈ symmetrization R) (ht₃ : t₃ ∈ symmetrization R)
    (hd : FreeGroup.mk dw = conjEval e₁ * FreeGroup.mk c₃)
    (hcy : dw = c ++ y) (hy : y <+: FreeGroup.invRev t)
    (halign : t₃.take i <+: (FreeGroup.invRev t).rotate y.length) :
    6 * i < t₃.length := by
  by_contra hcon
  refine ne_rotate_invRev_of_minimal_forward hmin hd hcy hy ?_
  refine eq_of_sixth_common_prefix hmetric ht₃
    (rotate_mem_symmetrization (invRev_mem_symmetrization ht) y.length)
    (List.take_prefix i t₃) halign ?_
  rw [List.length_take]
  omega

/-! ## 6.  The back-side loss, at the landing factor's own junction -/

/-- **Rotating back.**  A rotation by `k` is undone by a rotation by `|l| − k`.

The two coincidence lemmas name the same identification at complementary
offsets — `GreendlingerOverlap.mk_palindrome_mul_eq_one_of_coincidence` reads it
as `invRev t = t'.rotate q`, its primed twin as `t' = (invRev t).rotate y` — and
this is the conversion between them.  The rigidity core produces the first form;
the forward containment refutes the second. -/
theorem eq_rotate_invRev_of_invRev_eq_rotate {t₃ t₄ : List (α × Bool)} {k : ℕ}
    (hk : k ≤ t₄.length) (h : FreeGroup.invRev t₃ = t₄.rotate k) :
    t₄ = (FreeGroup.invRev t₃).rotate (t₄.length - k) := by
  rw [h, List.rotate_rotate,
    show k + (t₄.length - k) = t₄.length from by omega]
  exact (List.rotate_length t₄).symm

/-- **The landing factor's own block eats only a piece of its rotation**, in the
orientation where its conjugator overhangs the next factor's effective one.

It is the same piece-or-coincidence argument as the head's, read one junction
down with the landing factor in the head's place:
`GreendlingerDeepestMatch.six_mul_intrusion_lt` turns the intrusion into the
bound once the two relators are distinct, and
`GreendlingerCoincidence.invRev_ne_rotate_of_minimal` supplies distinctness for
an arbitrary block `e₁` of factors in between.

**Scope, stated because the hypothesis hides it.**  With
`palindrome c₃ t₃ = P₃ ++ M₃` the back loss is `|M₃| − |c₃|`, so `E₃` is the
landing factor's *own* eaten stretch and `6|E₃| < |t₃|` says exactly that the
landing factor is not itself deep — the negation, at that factor, of
`five_mul_lt_six_mul_eaten`.  That is not a theorem, and this lemma does not
claim it: what it assumes is `hintr`, that the stretch lands in the next
factor's relator territory, which is precisely what fails when the landing
factor's own block overruns.  So this closes the back side at a **shallow**
landing factor and says nothing at a deep one.

A route that needs the back bound unconditionally is therefore mis-shaped.  The
one that does not is `GreendlingerDeepInvariant`'s: it recurses inside the
descent, so a deep landing factor is handed to its own stage and the rotation
eaten from behind is simply not the one that pays.  Only the front bound,
`six_mul_intrusion_lt_of_forward`, is load-bearing there. -/
theorem six_mul_back_lt_of_backward [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {c₃ t₃ c₄ t₄ dw q E₃ : List (α × Bool)}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c₃, t₃) :: (e₁ ++ ((FreeGroup.mk c₄, t₄) :: f))) g)
    (ht₃ : t₃ ∈ symmetrization R) (ht₄ : t₄ ∈ symmetrization R)
    (hE : E₃ <:+ t₃)
    (hd : FreeGroup.mk dw = conjEval e₁ * FreeGroup.mk c₄)
    (hcq : c₃ = dw ++ q) (hq : q <+: t₄)
    (hintr : FreeGroup.invRev E₃ <+: t₄.rotate q.length) :
    6 * E₃.length < t₃.length :=
  (six_mul_intrusion_lt hmetric ht₃ ht₄ hE hintr
    (invRev_ne_rotate_of_minimal hmin hd hcq hq)).1

/-- **The same bound, in the overrun orientation.**  Where the next factor's
effective conjugator extends the landing factor's own, distinctness comes from
`ne_rotate_invRev_of_minimal_forward` instead, and the two rotation offsets have
to be matched up: the rigidity core hands back `invRev t₃ = t₄.rotate k` while
that lemma refutes `t₄ = (invRev t₃).rotate |y|`, and `hindex` is the geometric
identification `|y| = |t₄| − k` between them.

`hindex` is the one field a caller must supply from the cascade's own
bookkeeping; everything else is the same data the backward version takes, and
the scope note there applies verbatim: `hintr` fails at a deep landing factor,
so this too closes the back side only at a shallow one. -/
theorem six_mul_back_lt_of_forward [DecidableEq α]
    {R : Set (List (α × Bool))} (hmetric : MetricSmallCancellation R (1 / 6))
    {c₃ t₃ c₄ t₄ dw y E₃ : List (α × Bool)} {k : ℕ}
    {e₁ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c₃, t₃) :: (e₁ ++ ((FreeGroup.mk c₄, t₄) :: f))) g)
    (ht₃ : t₃ ∈ symmetrization R) (ht₄ : t₄ ∈ symmetrization R)
    (hE : E₃ <:+ t₃)
    (hd : FreeGroup.mk dw = conjEval e₁ * FreeGroup.mk c₄)
    (hcy : dw = c₃ ++ y) (hy : y <+: FreeGroup.invRev t₃)
    (hk : k ≤ t₄.length) (hindex : y.length = t₄.length - k)
    (hintr : FreeGroup.invRev E₃ <+: t₄.rotate k) :
    6 * E₃.length < t₃.length := by
  refine (six_mul_intrusion_lt hmetric ht₃ ht₄ hE hintr ?_).1
  intro hcon
  refine ne_rotate_invRev_of_minimal_forward hmin hd hcy hy ?_
  rw [hindex]
  exact eq_rotate_invRev_of_invRev_eq_rotate hk hcon

/-! ## 7.  The effective conjugator is a word the cascade already names -/

/-- **The effective conjugator, computed.**  Along a cascade step
`W = A ++ V.drop N` into the landing factor's own word `V`, the element the
landing factor presents to the head — everything between them folded in, times
the landing conjugator — is spelled by the concrete word `A ++ c₃.drop N`.

`GreendlingerCoincidence.exists_effectiveConjugator` produces *some* word for
that element, by taking a reduced word; it is of no use to the coincidence
lemmas, which need the word to begin with the head conjugator.  This produces a
*named* word instead, built from the surviving block `A` of the cascade and what
the drop leaves of `c₃` — and that is the word the block is actually read
against, so it is the one whose prefix can be compared with `c`.

The proof is three cancellations and no combinatorics: the cascade gives
`mk W = mk A * mk (V.drop N)`, the hypothesis `hPQ` gives `mk W = P * Q`, and
splitting `V` at `N` lets `mk (V.drop N)` be cancelled from both, leaving
`mk A = P * mk (c₃.take N)`.  Multiplying by `mk (c₃.drop N)` reassembles `c₃`.

Stated over a bare word `V` and bare elements `P`, `Q` rather than over
`conjEval` and `toWord`: the content is group cancellation and none of it reads
the expression, so the cascade plumbing stays at the call site.  There, take
`V := Q.toWord` and `W := (conjEval (e₁ ++ ((mk c₃, t₃) :: f))).toWord` with
`P := conjEval e₁` and `Q := conjEval ((mk c₃, t₃) :: f)`; `hQ` is then
`FreeGroup.mk_toWord` and `hPQ` is `mk_toWord` followed by
`GreendlingerWeight.conjEval_append`.

`hW` at that instantiation is `GreendlingerAlphaPlumb.exists_cascade_split`,
which is `GreendlingerCascade.exists_cascade` read at `k = |e₁|` and carries no
side conditions.  It is **not**
`GreendlingerDeepInduction.exists_postJunction_drop`, which collapses the
intermediate factors and so splits at a different place; that one is for turning
the deep regime's overrun from a hypothesis into a theorem, not for this.

`hVc` is the one input from outside: that the landing sub-expression's word
opens with `c₃`, up to the depth the drop reaches.  It is the
leading-cancellation decomposition of that sub-expression, read at `N`. -/
theorem mk_effectiveConjugator_of_split {A c₃ V W : List (α × Bool)} {N : ℕ}
    {P Q : FreeGroup α}
    (hW : W = A ++ V.drop N)
    (hVc : V.take N = c₃.take N)
    (hQ : FreeGroup.mk V = Q)
    (hPQ : FreeGroup.mk W = P * Q) :
    FreeGroup.mk (A ++ c₃.drop N) = P * FreeGroup.mk c₃ := by
  have hsplitV : Q = FreeGroup.mk (c₃.take N) * FreeGroup.mk (V.drop N) := by
    rw [← hQ, ← hVc, FreeGroup.mul_mk, List.take_append_drop]
  have hWsplit : FreeGroup.mk W
      = FreeGroup.mk A * FreeGroup.mk (V.drop N) := by
    rw [hW, FreeGroup.mul_mk]
  have hkey : FreeGroup.mk A = P * FreeGroup.mk (c₃.take N) := by
    refine mul_right_cancel (b := FreeGroup.mk (V.drop N)) ?_
    rw [← hWsplit, hPQ, hsplitV, mul_assoc]
  have hc₃ : FreeGroup.mk c₃
      = FreeGroup.mk (c₃.take N) * FreeGroup.mk (c₃.drop N) := by
    rw [FreeGroup.mul_mk, List.take_append_drop]
  rw [← FreeGroup.mul_mk, hkey, hc₃, mul_assoc]

/-- **The effective conjugator extends the head conjugator.**  The positional
half of the same fact: the word `A ++ c₃.drop N` that
`mk_effectiveConjugator_of_cascade` names does begin with `c`, and what follows
lies inside the eaten stretch.

This is the containment the coincidence lemmas need, in the orientation the
overrun produces — and it is why that orientation arises at all: the block's
matching prefix opens with the whole head conjugator, so anything read against
it past position `|c|` is head-relator material.

Everything is one decomposition.  The cascade puts `A ++ c₃.drop N` at the front
of the tail word; the block puts `c ++ invRev E` there too; the shorter of the
two is a prefix of the longer, and `hhigh` says which.  `hlow` says the landing
factor's relator territory does not begin before the head conjugator ends, which
is what makes `y` nonempty material rather than a truncation of `c`.

`hc₃V` — that the landing sub-expression's word opens with its own conjugator —
is the same input `mk_effectiveConjugator_of_cascade` takes as `hV`, in the
stronger form the positional argument needs. -/
theorem exists_forward_containment
    {W A c₃ V Z M E c : List (α × Bool)} {N : ℕ}
    (hcasc : W = A ++ V.drop N)
    (hc₃V : V = c₃ ++ Z) (hN : N ≤ c₃.length)
    (hM : FreeGroup.invRev M = c ++ FreeGroup.invRev E)
    (hMW : FreeGroup.invRev M <+: W)
    (hlow : c.length ≤ A.length + (c₃.length - N))
    (hhigh : A.length + (c₃.length - N) ≤ M.length) :
    ∃ y : List (α × Bool), A ++ c₃.drop N = c ++ y ∧
      y <+: FreeGroup.invRev E := by
  have hdrop : V.drop N = c₃.drop N ++ Z := by
    rw [hc₃V, drop_append_of_le N c₃ Z hN]
  have hlen : (A ++ c₃.drop N).length = A.length + (c₃.length - N) := by
    rw [List.length_append, List.length_drop]
  have hpre : A ++ c₃.drop N <+: W := by
    refine ⟨Z, ?_⟩
    rw [hcasc, hdrop, List.append_assoc]
  have hsub : A ++ c₃.drop N <+: c ++ FreeGroup.invRev E := by
    rw [← hM]
    refine List.prefix_of_prefix_length_le hpre hMW ?_
    rw [hlen, FreeGroup.invRev_length]
    omega
  obtain ⟨y, hy⟩ :=
    List.prefix_of_prefix_length_le
      (show c <+: c ++ FreeGroup.invRev E from ⟨FreeGroup.invRev E, rfl⟩)
      hsub (by rw [hlen]; omega)
  refine ⟨y, hy.symm, ?_⟩
  refine (List.prefix_append_right_inj c).mp ?_
  rw [hy]
  exact hsub

/-- **The alignment, from the same decomposition.**  The block covers the
effective conjugator and then `i` letters of the landing rotation, so those
letters are read against the head rotation `y` letters in — which is exactly
`halign`, the last field `six_mul_intrusion_lt_of_forward` needs.

Nothing new is set up: this is `exists_forward_containment` with the prefix
taken `i` letters further, and the rotation appears only through
`GreendlingerOverlap.prefix_rotate_of_append_prefix`, which turns a prefix
beginning `|y|` letters into a word into a prefix of that word's rotation by
`|y|`.  So the alignment is not an extra geometric fact — it is the containment
read one step longer, which is why `hhigh` is the same bound with `i` added.

`hZ` says the landing sub-expression's word carries `i` letters of `t₃` after
its conjugator; that is the surviving stretch, and it is what the piece bound
will then cap. -/
theorem exists_forward_alignment
    {W A c₃ V Z M E c t t₃ : List (α × Bool)} {N i : ℕ}
    (hcasc : W = A ++ V.drop N)
    (hc₃V : V = c₃ ++ Z) (hN : N ≤ c₃.length)
    (hZ : t₃.take i <+: Z)
    (hM : FreeGroup.invRev M = c ++ FreeGroup.invRev E)
    (hEsuf : E <:+ t)
    (hMW : FreeGroup.invRev M <+: W)
    (hlow : c.length ≤ A.length + (c₃.length - N))
    (hhigh : A.length + (c₃.length - N) + i ≤ M.length) :
    ∃ y : List (α × Bool), A ++ c₃.drop N = c ++ y ∧
      t₃.take i <+: (FreeGroup.invRev t).rotate y.length := by
  obtain ⟨y, hy, -⟩ :=
    exists_forward_containment hcasc hc₃V hN hM hMW hlow (by omega)
  refine ⟨y, hy, ?_⟩
  obtain ⟨Z', hZ'⟩ := hZ
  have hdrop : V.drop N = c₃.drop N ++ Z := by
    rw [hc₃V, drop_append_of_le N c₃ Z hN]
  have hlen : (A ++ c₃.drop N).length = A.length + (c₃.length - N) := by
    rw [List.length_append, List.length_drop]
  have hpre : (A ++ c₃.drop N) ++ t₃.take i <+: W := by
    refine ⟨Z', ?_⟩
    rw [hcasc, hdrop, ← hZ']
    simp only [List.append_assoc]
  have hsub : (A ++ c₃.drop N) ++ t₃.take i <+: c ++ FreeGroup.invRev E := by
    rw [← hM]
    refine List.prefix_of_prefix_length_le hpre hMW ?_
    rw [List.length_append, hlen, List.length_take, FreeGroup.invRev_length]
    omega
  rw [hy] at hsub
  have hyt : y ++ t₃.take i <+: FreeGroup.invRev E := by
    refine (List.prefix_append_right_inj c).mp ?_
    rw [← List.append_assoc]
    exact hsub
  exact prefix_rotate_of_append_prefix
    (hyt.trans (invRev_prefix_of_suffix hEsuf))

end SmallCancellationRouter
end GroupApproximation
