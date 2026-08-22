import GroupApproximation.Sofic.GreendlingerDeepArc

/-!
# The deep regime is empty at the adjacent junction

`GreendlingerDeepArc` reduces the deep half of `CascadeLanding` to `DeepTailArc`
and records four configurations the five-sixths bound refutes.  This file runs
the case analysis those four were built for, and finds that **it closes**: at the
junction between the head factor and the factor next to it, the deep regime
admits no configuration at all.

## The tree

The block destroys `M = E ++ invRev c` with `5 * |t| < 6 * |E|`, and the prefix
it destroys in the tail word is `c ++ invRev E`.  Suppose that prefix stops
inside the next palindrome, `c ++ invRev E <+: palindrome c' t'`.  Comparing the
two conjugators splits into five leaves, and each one dies:

* `|c'| ≤ |c|` and `|t'| ≤ |q|`, the overhang swallowing the next rotation —
  `GreendlingerWeight.not_absorb_of_minimal`, by reordering the two factors.
* `|c'| ≤ |c|`, `|q| < |t'|`, and `|q| + |E| ≤ |t'|`, the stretch landing inside
  the next rotation — `not_deep_hug_adjacent`: five sixths is not a piece, so
  the two rotations coincide and the factors cancel.
* `|c'| ≤ |c|`, `|q| < |t'|`, and `|t'| < |q| + |E|`, the stretch running out the
  far end of the next rotation — `not_hug_overrun`, proved here.  The hug pin
  leaves at least half of `t'` inside the stretch, and half is not a piece
  either.  **This leaf never looks at the deep regime.**
* `|c| < |c'|` and `|E| < |y|`, the stretch buried in the next conjugator —
  `not_deep_eaten_buried`: the eaten half-pin against five sixths.
* `|c| < |c'|` and `|y| ≤ |E|`, the stretch escaping the conjugator.  The eaten
  half-pin caps the buried part `E₂` at half of `t`, so the escaping part `E₁`
  keeps more than a third, which is over the sixth the rigidity core needs.  It
  then either stops inside `t'` — `not_deep_overhang_adjacent` — or swallows it
  whole, and a relator that prefixes a rotation of another relator *and* itself
  is a piece of itself unless the two agree: `not_relator_swallowed`, proved
  here and also independent of the deep regime.

`not_deep_confined` is the assembled statement.  Two corollaries are immediate:
every **two-factor** deep configuration is impossible, and more generally the
deep regime survives only where the block overruns the whole adjacent palindrome
and reaches a factor it is not next to.

## What is left

`DeepOverrunArc`, the residual: `DeepTailArc` with the extra hypothesis that
`invRev M` is *not* a prefix of the adjacent palindrome.  Unlike the passage
from `DeepArcSource` to `DeepTailArc`, this one is a **strict** weakening — the
confined case is discharged, not relocated — so there is no converse to prove
and none is claimed.

That residual is exactly the configuration `GreendlingerThreeFactor`'s header
isolates as the one thing its four-case descent could not reach: a block that
overruns and then exhausts the chunk it lands in, reaching the conjugator of a
factor it is not adjacent to, where no reroute identity applies.  A reroute
moves one factor past its neighbour and no further, which is why every kill
above is a junction kill and why none of them extends to the overrun by itself.
The tools that do reach that far are `not_deep_intrusion_of_reduced`, which
needs neither minimality nor adjacency, and the two arc producers of
`GreendlingerDeepArc`.

Depends on `C'(1/6)` where a piece bound is read and on minimality where a
coincidence or an absorption is refuted.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  Splitting the destroyed prefix against the next palindrome -/

/-- **The overhang split.**  When the head conjugator is the longer of the two,
it extends the next one by `q`, and what the block destroys past it begins `q`
letters into the next factor's rotation territory.

This is the first half of `GreendlingerOverlap.exists_split_of_overlap_prefix`,
taken on its own because the analysis below has to case on whether the tail of
that territory is reached, which that lemma's `hfit` hypothesis rules out. -/
theorem exists_overhang_of_prefix {c c' t' p : List (α × Bool)}
    (hpre : c ++ p <+: palindrome c' t') (hle : c'.length ≤ c.length) :
    ∃ q : List (α × Bool), c = c' ++ q ∧
      q ++ p <+: t' ++ FreeGroup.invRev c' := by
  have hP : palindrome c' t' = c' ++ (t' ++ FreeGroup.invRev c') := by
    unfold palindrome
    rw [List.append_assoc]
  have hc'pre : c' <+: palindrome c' t' := by
    rw [hP]
    exact ⟨t' ++ FreeGroup.invRev c', rfl⟩
  have hcpre : c <+: palindrome c' t' :=
    (show c <+: c ++ p from ⟨p, rfl⟩).trans hpre
  obtain ⟨q, hq⟩ := List.prefix_of_prefix_length_le hc'pre hcpre hle
  refine ⟨q, hq.symm, ?_⟩
  have h1 : c' ++ (q ++ p) <+: c' ++ (t' ++ FreeGroup.invRev c') := by
    rw [← List.append_assoc, hq, ← hP]
    exact hpre
  exact (List.prefix_append_right_inj c').mp h1

/-- **The forward split**, the mirror: when the next conjugator is the longer
one it extends the head conjugator by `y`, and the destroyed stretch is read
against `y` first and the next rotation after it. -/
theorem exists_forward_of_prefix {c c' t' p : List (α × Bool)}
    (hpre : c ++ p <+: palindrome c' t') (hle : c.length ≤ c'.length) :
    ∃ y : List (α × Bool), c' = c ++ y ∧
      p <+: y ++ (t' ++ FreeGroup.invRev c') := by
  have hP : palindrome c' t' = c' ++ (t' ++ FreeGroup.invRev c') := by
    unfold palindrome
    rw [List.append_assoc]
  have hc'pre : c' <+: palindrome c' t' := by
    rw [hP]
    exact ⟨t' ++ FreeGroup.invRev c', rfl⟩
  have hcpre : c <+: palindrome c' t' :=
    (show c <+: c ++ p from ⟨p, rfl⟩).trans hpre
  obtain ⟨y, hy⟩ := List.prefix_of_prefix_length_le hcpre hc'pre hle
  refine ⟨y, hy.symm, ?_⟩
  have h1 : c ++ p <+: c ++ (y ++ (t' ++ FreeGroup.invRev c')) := by
    rw [← List.append_assoc, hy, ← hP]
    exact hpre
  exact (List.prefix_append_right_inj c).mp h1

/-! ## 2.  Two junction kills that do not need the deep regime -/

/-- **A hug cannot be run out the far end of the rotation it hugs.**  The head
conjugator overhangs the next one by `q`, the next rotation is `q ++ X`, and the
destroyed stretch covers all of `X`.

The hug pin of `GreendlingerBetaBranch.two_mul_hug_le_of_minimal_reroute` says
`2|q| ≤ |t'|`, so `X` is at least half of `t'`; and `X` prefixes both the
inverted head rotation and `t'.rotate |q|`, so it is a piece unless those two
coincide.  Half against a sixth closes the first branch and minimality closes
the second.

No hypothesis about how much of the head rotation was eaten enters, so this
holds outside the deep regime as well. -/
theorem not_hug_overrun [DecidableEq α] {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c c' q X t t' E : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredc : FreeGroup.IsReduced c) (hredc' : FreeGroup.IsReduced c')
    (hEt : E <:+ t)
    (hcq : c = c' ++ q) (hqX : t' = q ++ X)
    (hX : X <+: FreeGroup.invRev E) : False := by
  have hpin : 2 * q.length ≤ (q ++ X).length := by
    have hm : IsMinimalConjExpr R
        ((FreeGroup.mk (c' ++ q), t) :: (FreeGroup.mk c', q ++ X) :: f) g := by
      rw [← hcq, ← hqX]
      exact hmin
    exact two_mul_hug_le_of_minimal_reroute hm
      (by rw [← hcq]; exact hredc) hredc'
  have hqt : q <+: t' := ⟨X, hqX.symm⟩
  have hXrot : X <+: t'.rotate q.length := by
    rw [hqX, rotate_append]
    exact ⟨q, rfl⟩
  have hXinv : X <+: FreeGroup.invRev t :=
    hX.trans (invRev_prefix_of_suffix hEt)
  by_cases hcoin : FreeGroup.invRev t = t'.rotate q.length
  · exact mk_palindrome_mul_ne_one_of_minimal hmin
      (mk_palindrome_mul_eq_one_of_coincidence hcq hqt hcoin)
  · have hpiece : IsPiece (symmetrization R) X :=
      isPiece_of_prefix_two (invRev_mem_symmetrization ht)
        (rotate_mem_symmetrization ht' q.length) hcoin hXinv hXrot
    have h6 := six_mul_length_lt_of_isPiece hmetric hpiece
      (rotate_mem_symmetrization ht' q.length) hXrot
    rw [List.length_rotate] at h6
    have ht'len : t'.length = q.length + X.length := by
      rw [hqX, List.length_append]
    rw [List.length_append] at hpin
    omega

/-- **A rotation cannot be swallowed by the stretch destroyed out of another.**
The next conjugator extends the head one by `y`, the destroyed stretch reads
`y ++ p` against the inverted head rotation, and `p` covers the whole of the
next rotation `t'`.

Then `t'` prefixes `(invRev t).rotate |y|` and prefixes itself, so it is a piece
of itself unless the two agree — and `6|t'| < |t'|` is impossible whatever `t'`
is.  Agreement is a coincidence, which minimality refutes.

Like `not_hug_overrun`, this spends no length hypothesis about the eaten
stretch. -/
theorem not_relator_swallowed [DecidableEq α] {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {c t t' y p : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk (c ++ y), t') :: f) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hyp : y ++ p <+: FreeGroup.invRev t)
    (ht'p : t' <+: p) : False := by
  have hy : y <+: FreeGroup.invRev t :=
    (show y <+: y ++ p from ⟨p, rfl⟩).trans hyp
  have ht'rot : t' <+: (FreeGroup.invRev t).rotate y.length :=
    ht'p.trans (prefix_rotate_of_append_prefix hyp)
  by_cases hcoin : t' = (FreeGroup.invRev t).rotate y.length
  · exact mk_palindrome_mul_ne_one_of_minimal hmin
      (mk_palindrome_mul_eq_one_of_coincidence' (y := y) rfl hy hcoin)
  · have hpiece : IsPiece (symmetrization R) t' :=
      isPiece_of_prefix_two ht'
        (rotate_mem_symmetrization (invRev_mem_symmetrization ht) y.length)
        hcoin (List.prefix_refl t') ht'rot
    have h6 :=
      six_mul_length_lt_of_isPiece hmetric hpiece ht' (List.prefix_refl t')
    omega

/-! ## 3.  The junction is empty in the deep regime -/

/-- **The deep regime admits no confined configuration.**

If the head's block runs deep — past five sixths of its own rotation — and the
prefix it destroys in the tail word stops inside the adjacent palindrome, the
expression is not minimal.  Five leaves, each closed by one of the five kills
named in the header, and the case split is on the two conjugator lengths and on
where the destroyed stretch stops.

The tail `f` is arbitrary, so this is a statement about the junction and not
about the length of the expression. -/
theorem not_deep_confined [DecidableEq α] {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    {c t c' t' P' M B' : List (α × Bool)}
    {f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {j : ℕ}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hj : 6 * j < t.length)
    (hgt : c.length + t.length < M.length + j) : False := by
  have hredc : FreeGroup.IsReduced c :=
    isReduced_of_infix ⟨[], t ++ FreeGroup.invRev c, by simp [palindrome]⟩ hredp
  have hredc' : FreeGroup.IsReduced c' :=
    isReduced_of_infix ⟨[], t' ++ FreeGroup.invRev c', by simp [palindrome]⟩
      hredp'
  have ht'ne : t' ≠ [] := ne_nil_of_mem_symmetrization hRne ht'
  have hhigh : M.length ≤ c.length + t.length :=
    swallow_bound_of_minimal hRne hmetric hmin ht ht' hredp hredp' heq heq'
  obtain ⟨E, hM, hinvM, hEt, -, -⟩ := eaten_prefix_orientation heq hlow hhigh
  have hdeep : 5 * t.length < 6 * E.length := five_mul_lt_six_mul_eaten hM hj hgt
  have hpre : c ++ FreeGroup.invRev E <+: palindrome c' t' := by
    rw [← hinvM]
    exact ⟨B', heq'.symm⟩
  rcases le_or_gt c'.length c.length with hle | hlt
  · -- the head conjugator is the longer one
    obtain ⟨q, hcq, hqp⟩ := exists_overhang_of_prefix hpre hle
    have ht'pre : t' <+: t' ++ FreeGroup.invRev c' := ⟨FreeGroup.invRev c', rfl⟩
    have hqpre : q <+: t' ++ FreeGroup.invRev c' :=
      (show q <+: q ++ FreeGroup.invRev E from
        ⟨FreeGroup.invRev E, rfl⟩).trans hqp
    rcases le_or_gt t'.length q.length with habs | hqlt
    · -- the overhang swallows the next rotation
      obtain ⟨q'', hq''⟩ := List.prefix_of_prefix_length_le ht'pre hqpre habs
      have hceq : c = c' ++ (t' ++ q'') := by
        rw [hcq, ← hq'']
      rw [hceq] at hmin hredc
      exact not_absorb_of_minimal hmin hredc ht'ne
    · have hqt' : q <+: t' :=
        List.prefix_of_prefix_length_le hqpre ht'pre hqlt.le
      rcases le_or_gt (q.length + E.length) t'.length with hfit | hover
      · -- the stretch lands inside the next rotation
        have hqEt' : q ++ FreeGroup.invRev E <+: t' :=
          List.prefix_of_prefix_length_le hqp ht'pre (by
            rw [List.length_append, FreeGroup.invRev_length]
            exact hfit)
        exact not_deep_hug_adjacent hmetric hmin ht ht' hEt
          (length_le_six_mul_of_deep hdeep) hcq hqt'
          (prefix_rotate_of_append_prefix hqEt')
      · -- the stretch runs out the far end of the next rotation
        obtain ⟨X, hXt⟩ := hqt'
        have hlenX : t'.length = q.length + X.length := by
          rw [← hXt, List.length_append]
        have hqXpre : q ++ X <+: t' ++ FreeGroup.invRev c' := by
          rw [hXt]
          exact ht'pre
        have hsub : q ++ X <+: q ++ FreeGroup.invRev E :=
          List.prefix_of_prefix_length_le hqXpre hqp (by
            rw [List.length_append, List.length_append, FreeGroup.invRev_length]
            omega)
        exact not_hug_overrun hmetric hmin ht ht' hredc hredc' hEt hcq hXt.symm
          ((List.prefix_append_right_inj q).mp hsub)
  · -- the next conjugator is the longer one
    obtain ⟨y, hc'y, hpy⟩ := exists_forward_of_prefix hpre hlt.le
    have hypre : y <+: y ++ (t' ++ FreeGroup.invRev c') :=
      ⟨t' ++ FreeGroup.invRev c', rfl⟩
    rcases le_or_gt y.length E.length with hyle | hygt
    · -- the stretch escapes the next conjugator
      obtain ⟨p₂, hp₂⟩ :=
        List.prefix_of_prefix_length_le hypre hpy (by
          rw [FreeGroup.invRev_length]
          exact hyle)
      have hEsplit : E = FreeGroup.invRev p₂ ++ FreeGroup.invRev y := by
        have hb := congrArg FreeGroup.invRev hp₂
        rw [FreeGroup.invRev_append, FreeGroup.invRev_invRev] at hb
        exact hb.symm
      have hp₂pre : p₂ <+: t' ++ FreeGroup.invRev c' := by
        have h1 : y ++ p₂ <+: y ++ (t' ++ FreeGroup.invRev c') := by
          rw [hp₂]
          exact hpy
        exact (List.prefix_append_right_inj y).mp h1
      have ht'pre : t' <+: t' ++ FreeGroup.invRev c' := ⟨FreeGroup.invRev c', rfl⟩
      rcases le_or_gt p₂.length t'.length with hin | hout
      · -- the escaping part stops inside the next rotation
        have hp₂t' : p₂ <+: t' :=
          List.prefix_of_prefix_length_le hp₂pre ht'pre hin
        obtain ⟨t₀, ht₀⟩ : ∃ z, z ++ FreeGroup.invRev y = t := by
          obtain ⟨w, hw⟩ := hEt
          refine ⟨w ++ FreeGroup.invRev p₂, ?_⟩
          rw [List.append_assoc, ← hEsplit]
          exact hw
        have hpin : 2 * y.length ≤ t.length := by
          have hm : IsMinimalConjExpr R
              ((FreeGroup.mk c, t₀ ++ FreeGroup.invRev y)
                :: (FreeGroup.mk (c ++ (FreeGroup.invRev (FreeGroup.invRev y)
                  ++ [])), t') :: f) g := by
            rw [FreeGroup.invRev_invRev, List.append_nil, ← hc'y, ht₀]
            exact hmin
          have h := two_mul_eaten_le_of_minimal_reroute hm
            (by
              rw [FreeGroup.invRev_invRev, List.append_nil, ← hc'y]
              exact hredc') hredc
          rw [List.length_append, FreeGroup.invRev_length] at h
          rw [← ht₀, List.length_append, FreeGroup.invRev_length]
          omega
        have hElen : E.length = p₂.length + y.length := by
          rw [hEsplit, List.length_append, FreeGroup.invRev_length,
            FreeGroup.invRev_length]
        have hlong : t.length ≤ 6 * (FreeGroup.invRev p₂).length := by
          rw [FreeGroup.invRev_length]
          omega
        have hEt2 : FreeGroup.invRev p₂ ++ FreeGroup.invRev y <:+ t := by
          rw [← hEsplit]
          exact hEt
        have hm2 : IsMinimalConjExpr R
            ((FreeGroup.mk c, t)
              :: (FreeGroup.mk (c ++ FreeGroup.invRev (FreeGroup.invRev y)),
                t') :: f) g := by
          rw [FreeGroup.invRev_invRev, ← hc'y]
          exact hmin
        have hintr : FreeGroup.invRev (FreeGroup.invRev p₂) <+: t' := by
          rw [FreeGroup.invRev_invRev]
          exact hp₂t'
        exact not_deep_overhang_adjacent hmetric hm2 ht ht' hEt2 hlong hintr
      · -- the escaping part swallows the next rotation
        have ht'p₂ : t' <+: p₂ :=
          List.prefix_of_prefix_length_le ht'pre hp₂pre hout.le
        have hyp : y ++ p₂ <+: FreeGroup.invRev t := by
          rw [hp₂]
          exact invRev_prefix_of_suffix hEt
        have hm3 : IsMinimalConjExpr R
            ((FreeGroup.mk c, t) :: (FreeGroup.mk (c ++ y), t') :: f) g := by
          rw [← hc'y]
          exact hmin
        exact not_relator_swallowed hmetric hm3 ht ht' hyp ht'p₂
    · -- the stretch is buried in the next conjugator
      obtain ⟨Z, hZ⟩ :=
        List.prefix_of_prefix_length_le hpy hypre (by
          rw [FreeGroup.invRev_length]
          omega)
      obtain ⟨t₀, ht₀⟩ := hEt
      have hm : IsMinimalConjExpr R
          ((FreeGroup.mk c, t₀ ++ E)
            :: (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)), t') :: f) g := by
        rw [hZ, ← hc'y, ht₀]
        exact hmin
      refine not_deep_eaten_buried hm ?_ hredc ?_
      · rw [hZ, ← hc'y]
        exact hredc'
      · rw [ht₀]
        exact hdeep

/-! ## 4.  What the junction kill settles -/

/-- **No two-factor expression is ever deep.**  With a single factor in the tail
the destroyed prefix has nowhere to go but the adjacent palindrome, so the
junction kill is the whole story. -/
theorem not_deep_two_factor [DecidableEq α] {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    {c t c' t' P' M B' : List (α × Bool)} {g : FreeGroup α} {j : ℕ}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: [(FreeGroup.mk c', t')]) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hj : 6 * j < t.length)
    (hgt : c.length + t.length < M.length + j) : False :=
  not_deep_confined hRne hmetric hmin ht ht' hredp hredp' heq heq' hlow hj hgt

/-! ## 5.  The residual, and the reduction to it -/

/-- **What the deep regime still owes, after the junction.**  `DeepTailArc` with
one hypothesis added: the prefix the head's block destroys is *not* confined to
the adjacent palindrome.

This is a strict weakening — `not_deep_confined` discharges the complementary
case outright rather than moving it elsewhere — so no converse holds and none is
claimed.  It is the configuration in which the block reaches a factor it is not
next to, where a reroute identity, which moves one factor past its neighbour and
no further, has nothing to say. -/
def DeepOverrunArc [DecidableEq α] (R : Set (List (α × Bool))) : Prop :=
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
    GreendlingerAt R (M.length + j - (c.length + t.length)) B'

/-- **The tail obligation, from the overrun obligation.**  Normalize the tail's
leading factor, then split on whether the destroyed prefix stays inside the
adjacent palindrome: if it does, `not_deep_confined` says the configuration does
not exist, and if it does not, the residual applies. -/
theorem deepTailArc_of_deepOverrunArc [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (h : DeepOverrunArc R) : DeepTailArc R := by
  intro c t M B' e g j hmin ht hredp hMsuf htail hlow hj hgt
  obtain ⟨c', t', f, ht', hredp', hmin', hev, -⟩ :=
    exists_deep_tail_setup hR hRne hmin htail hlow
  rw [← hev] at htail
  by_cases hconf : FreeGroup.invRev M <+: palindrome c' t'
  · exfalso
    obtain ⟨P', hP'⟩ := hMsuf
    obtain ⟨B'', hB''⟩ := hconf
    exact not_deep_confined hRne hmetric hmin' ht ht' hredp hredp'
      hP'.symm hB''.symm hlow hj hgt
  · exact h c t c' t' M B' f g j hmin' ht ht' hredp hredp' hMsuf htail hconf
      hlow hj hgt

/-! ## 6.  The gate, through the residual -/

/-- `DeepArcSource` from the overrun obligation. -/
theorem deepArcSource_of_deepOverrunArc [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (h : DeepOverrunArc R) : DeepArcSource R :=
  deepArcSource_of_deepTailArc (deepTailArc_of_deepOverrunArc hR hRne hmetric h)

/-- **The free-group half-form gate, reduced to the overrun obligation and the
landing production.**  The deep branch of `CascadeLanding` now costs exactly one
statement about blocks that reach past the factor next to them. -/
theorem greendlingerConclusion_of_deepOverrunArc_of_landing [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hdeep : DeepOverrunArc R) (hland : LandingProduction R) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_deepTailArc_of_landing hR hRne
    (deepTailArc_of_deepOverrunArc hR hRne hmetric hdeep) hland

end SmallCancellationRouter
end GroupApproximation
