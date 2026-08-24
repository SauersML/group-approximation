import GroupApproximation.Sofic.GreendlingerEmptyConjCorner
import GroupApproximation.Sofic.GreendlingerFreeGate
import GroupApproximation.Sofic.MinimalNoCancellingPair

/-!
# The curvature count, assembled — and what the count has to deliver

This file is the **arithmetic scaffold** for the diagram route to
`GreendlingerFreeGate.SharpGreendlingerGate`.  It takes the two inputs the
curvature count is meant to produce as explicit named hypotheses, checks that
they compose to the sharp conclusion, and — the point of writing it before the
inputs exist — records *precisely which form* of the degree bound the count has
to prove.

Nothing here is a result about small cancellation groups.  Everything below the
`ShellGate` definition is conditional on it.

## 1.  The verdict: a bare degree bound is **not enough**

The count is supposed to hand over a region `Δ` of the diagram, with boundary
label a symmetrized relator `r`, that meets at most three other regions, each
along a maximal run which `C'(λ)` bounds by `λ·|r|`.  Subtracting, the part of
`∂Δ` that lies on the boundary of the diagram is longer than `(1 − 3λ)·|r|`.
That is the right total, and `total_length_of_split_runs` proves it.

**It is not the conclusion.**  `GreendlingerConclusionSharp` asks for a *single*
subword `u` of `w` with `(1 − 3λ)·|r| < |u|`, and three interior runs that are
not consecutive around `∂Δ` cut the boundary part into up to three arcs.  The
count then bounds only their sum.

`split_threshold` is the exact arithmetic.  With `k` interior runs the boundary
part splits into at most `k` arcs, the longest is longer than
`(1 − k·λ)·|r| / k`, and that beats `(1 − 3λ)·|r|` exactly when

    `1 − k + 2·k·λ > 0`.

At `λ ≤ 1/6` this holds for `k = 1` and fails for `k = 2` and `k = 3`.
`three_arc_shortfall` is the numeric witness: `λ = 1/6`, `|r| = 12`, three
interior runs of one letter and three boundary arcs of three letters satisfies
every constraint, and `3 < 6 = (1 − 3λ)·|r|`; the arc is not even more than half
of `r`, so the **half**-form fails there too.

**So the degree bound has to be sharpened to a *shell*:** a region meeting the
boundary of the diagram in one *consecutive* arc, with its at most three
interior runs consecutive too.  This is what Lyndon–Schupp's proof of
Greendlinger's lemma actually produces (a boundary region of the first kind),
and it is a strictly stronger statement than "degree at most three".  Anything
`CyclicTwoArc` proves for (D) has to carry the contiguity, not just the count.

A second thing the count must carry, for the same reason: the arc `δ` runs along
`∂D`, which is the *cyclic* word `w`, so `δ` is a cyclic subword and can straddle
the basepoint.  `ShellDecomposition` below therefore asks for `δ <:+: w`
outright.  The classical route to that is two disjoint shells — at most one of
the two arcs can contain the basepoint — which is exactly why Greendlinger's
lemma is proved in a two-region form.  `GreendlingerCyclicTwoArc` is where that
lives.

## 2.  What is proved here

* `length_lt_of_piece_infix` — the metric condition applies to a run wherever it
  sits in the relator, not only at the front: rotate the relator so the run
  prefixes it (`exists_prefix_mem_symmetrization_of_infix`), and the rotation has
  the same length.  This is input (ii), "each run is a piece", in usable form.
* `length_arc_of_shell` — the arithmetic of a shell: one arc, longer than
  `(1 − 3λ)·|r|`.  Exact, with the three runs allowed to be empty.
* `total_length_of_split_runs` and `three_arc_shortfall` — §1.
* `greendlingerConclusionSharp_of_shell` and `sharpGreendlingerGate_of_shellGate`
  — the assembly, conditional on `ShellGate`.
* `greendlingerConclusionSharp_of_nonpos` — the gate's own `λ ≤ 0` corner, which
  the shell hypothesis cannot reach and which is empty for a different reason:
  `C'(λ)` at a non-positive constant forbids the empty piece, so the
  symmetrization has at most one member, so every relator is trivial.

## 3.  Reducedness: the count may assume it

The classical curvature lemma is false on an unreduced diagram, so the count
needs the reduced-diagram condition.  It does not have to assume it.
`ShellFromMinimal` is `ShellGate` with an expression for `w` named and assumed
shortest-then-lightest, `shellGate_of_shellFromMinimal` shows that asks for no
less (`exists_isMinimalConjExpr_of_mem_normalClosure`: a word of the normal
closure has a minimal expression), and on that hypothesis
`MinimalNoCancellingPair.ne_inv_conj_of_minimal` is free —
`noCancellingPair_of_shellFromMinimal_input` reads it at exactly the expression
the bridge supplies, so the shapes are checked here rather than discovered later.

`sharpGreendlingerGate_of_shellFromMinimal` is therefore the statement to aim the
count at.

Nothing here discharges `ShellGate` or `ShellFromMinimal`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  A run of a region's boundary, bounded -/

/-- **The metric condition, read at any position.**  `C'(λ)` bounds a piece
against every symmetrized relator it *prefixes*; a run of a region's boundary
sits at an arbitrary position of the relator, and rotating the relator to bring
the run to the front changes neither membership nor length. -/
theorem length_lt_of_piece_infix {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam) {r p : List (α × Bool)}
    (hr : r ∈ symmetrization R) (hp : p <:+: r)
    (hpiece : IsPiece (symmetrization R) p) :
    (p.length : ℚ) < lam * (r.length : ℚ) := by
  obtain ⟨v, hv, hpv, hvlen⟩ := exists_prefix_mem_symmetrization_of_infix hr hp
  have h := hmetric p hpiece v hv hpv
  rwa [hvlen] at h

/-- **An interior run of a region**: a stretch of its boundary shared with
another region of the diagram.  Either it is empty — the two regions do not meet
there — or it is a common subword of two distinct symmetrized relators, which is
a piece.

This is hypothesis (ii) of the assembly, stated as a property of one run. -/
def InteriorRun (R : Set (List (α × Bool))) (r p : List (α × Bool)) : Prop :=
  p <:+: r ∧ (p = [] ∨ IsPiece (symmetrization R) p)

theorem length_lt_of_interiorRun {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) (hmetric : MetricSmallCancellation R lam)
    {r p : List (α × Bool)} (hr : r ∈ symmetrization R) (hrne : r ≠ [])
    (h : InteriorRun R r p) : (p.length : ℚ) < lam * (r.length : ℚ) := by
  obtain ⟨hp, hcase⟩ := h
  rcases hcase with hnil | hpiece
  · subst hnil
    have hpos : 0 < r.length := List.length_pos_iff.mpr hrne
    have hposq : (0 : ℚ) < (r.length : ℚ) := by exact_mod_cast hpos
    have hlt : (0 : ℚ) < lam * (r.length : ℚ) := mul_pos hlam0 hposq
    simpa using hlt
  · exact length_lt_of_piece_infix hmetric hr hp hpiece

/-! ## 2.  A shell delivers one long arc; a bare degree bound does not -/

/-- **The arithmetic of a shell.**  A region whose boundary reads
`δ ++ p₁ ++ p₂ ++ p₃`, with the three interior runs consecutive and each shorter
than `λ·|r|`, meets the boundary of the diagram in a **single** arc longer than
`(1 − 3λ)·|r|` — which is exactly what `GreendlingerConclusionSharp` asks for. -/
theorem length_arc_of_shell {r δ p₁ p₂ p₃ : List (α × Bool)} {lam : ℚ}
    (hsplit : r = δ ++ (p₁ ++ (p₂ ++ p₃)))
    (h₁ : (p₁.length : ℚ) < lam * (r.length : ℚ))
    (h₂ : (p₂.length : ℚ) < lam * (r.length : ℚ))
    (h₃ : (p₃.length : ℚ) < lam * (r.length : ℚ)) :
    (1 - 3 * lam) * (r.length : ℚ) < (δ.length : ℚ) := by
  have hlen : r.length = δ.length + (p₁.length + (p₂.length + p₃.length)) := by
    rw [hsplit, List.length_append, List.length_append, List.length_append]
  have hq : (r.length : ℚ)
      = (δ.length : ℚ) + ((p₁.length : ℚ) + ((p₂.length : ℚ) + (p₃.length : ℚ))) := by
    exact_mod_cast hlen
  linarith

/-- **What a bare degree bound gives, and all it gives.**  If the three interior
runs are not consecutive, the region's boundary part is cut into three arcs and
the count bounds only their **sum**. -/
theorem total_length_of_split_runs {r δ₁ p₁ δ₂ p₂ δ₃ p₃ : List (α × Bool)} {lam : ℚ}
    (hsplit : r = δ₁ ++ (p₁ ++ (δ₂ ++ (p₂ ++ (δ₃ ++ p₃)))))
    (h₁ : (p₁.length : ℚ) < lam * (r.length : ℚ))
    (h₂ : (p₂.length : ℚ) < lam * (r.length : ℚ))
    (h₃ : (p₃.length : ℚ) < lam * (r.length : ℚ)) :
    (1 - 3 * lam) * (r.length : ℚ)
      < (δ₁.length : ℚ) + ((δ₂.length : ℚ) + (δ₃.length : ℚ)) := by
  have hlen : r.length
      = δ₁.length + (p₁.length + (δ₂.length + (p₂.length + (δ₃.length + p₃.length)))) := by
    rw [hsplit, List.length_append, List.length_append, List.length_append,
      List.length_append, List.length_append]
  have hq : (r.length : ℚ)
      = (δ₁.length : ℚ) + ((p₁.length : ℚ) + ((δ₂.length : ℚ)
          + ((p₂.length : ℚ) + ((δ₃.length : ℚ) + (p₃.length : ℚ))))) := by
    exact_mod_cast hlen
  linarith

/-- **The threshold.**  With `k` interior runs the boundary part of the region is
cut into at most `k` arcs, so the longest exceeds `(1 − k·λ)·|r| / k`, and that
beats the target `(1 − 3λ)·|r|` exactly when `1 − k + 2·k·λ > 0`.

At `λ ≤ 1/6` the inequality holds for one interior run and fails for two and for
three.  So contiguity is not a convenience: without it the count reaches the
conclusion only for a region of interior degree at most one. -/
theorem split_threshold (lam : ℚ) (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6) :
    0 < 1 - 1 + 2 * 1 * lam ∧ ¬ (0 < 1 - 2 + 2 * 2 * lam) ∧
      ¬ (0 < 1 - 3 + 2 * 3 * lam) := by
  refine ⟨by linarith, fun h => ?_, fun h => ?_⟩
  · linarith
  · linarith

/-- **The numeric witness.**  At `λ = 1/6` and `|r| = 12`, three interior runs of
one letter each and three boundary arcs of three letters each satisfy every
constraint the degree bound imposes, and no single arc reaches
`(1 − 3λ)·|r| = 6`.  Since `6 = |r|/2` as well, the half-form fails there too. -/
theorem three_arc_shortfall :
    (12 : ℚ) = 3 * 3 + 3 * 1 ∧ (1 : ℚ) < 1 / 6 * 12 ∧
      ¬ ((1 - 3 * (1 / 6 : ℚ)) * 12 < 3) := by
  norm_num

/-! ## 3.  The two open inputs, as one gate -/

/-- **OPEN — the curvature count's output, in the form the assembly consumes.**

For every `C'(λ)` family at a positive constant at most `1/6` and every nonempty
reduced word `w` of the normal closure: some symmetrized relator `r` splits as

    `r = δ ++ p₁ ++ p₂ ++ p₃`

with `δ` a contiguous subword of `w` and `p₁, p₂, p₃` interior runs.  Read on a
reduced van Kampen diagram for `w`: a region of interior degree at most three
whose interior runs are **consecutive**, so that its boundary part is a single
arc, and that arc does not straddle the basepoint of `∂D`.

The three parts of that sentence are the three things the count has to prove,
and §1 of the header explains why the first alone does not suffice for the last
two. -/
def ShellGate (α : Type*) : Prop :=
  ∀ (R : Set (List (α × Bool))) (lam : ℚ),
    (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → 0 < lam → lam ≤ 1 / 6 →
    MetricSmallCancellation R lam →
    ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
      FreeGroup.mk w ∈ Subgroup.normalClosure (FreeGroup.mk '' R) →
      ∃ r ∈ symmetrization R, r ≠ [] ∧ ∃ δ p₁ p₂ p₃ : List (α × Bool),
        r = δ ++ (p₁ ++ (p₂ ++ p₃)) ∧ δ <:+: w ∧
          InteriorRun R r p₁ ∧ InteriorRun R r p₂ ∧ InteriorRun R r p₃

/-! ## 4.  The assembly -/

/-- **The assembly, at one family.**  A shell plus the metric condition is the
sharp Greendlinger conclusion, with no rounding: the arc bound `(1 − 3λ)·|r|` is
what subtracting three pieces from a relator leaves. -/
theorem greendlingerConclusionSharp_of_shell {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam0 : 0 < lam) (hmetric : MetricSmallCancellation R lam)
    (hshell : ∀ w : List (α × Bool), FreeGroup.IsReduced w → w ≠ [] →
      FreeGroup.mk w ∈ Subgroup.normalClosure (FreeGroup.mk '' R) →
      ∃ r ∈ symmetrization R, r ≠ [] ∧ ∃ δ p₁ p₂ p₃ : List (α × Bool),
        r = δ ++ (p₁ ++ (p₂ ++ p₃)) ∧ δ <:+: w ∧
          InteriorRun R r p₁ ∧ InteriorRun R r p₂ ∧ InteriorRun R r p₃) :
    GreendlingerConclusionSharp R lam := by
  intro w hw hwne hmem
  obtain ⟨r, hr, hrne, δ, p₁, p₂, p₃, hsplit, hδw, hi₁, hi₂, hi₃⟩ :=
    hshell w hw hwne hmem
  exact ⟨r, hr, δ, hδw, ⟨p₁ ++ (p₂ ++ p₃), hsplit.symm⟩,
    length_arc_of_shell hsplit
      (length_lt_of_interiorRun hlam0 hmetric hr hrne hi₁)
      (length_lt_of_interiorRun hlam0 hmetric hr hrne hi₂)
      (length_lt_of_interiorRun hlam0 hmetric hr hrne hi₃)⟩

/-- **The gate's non-positive corner is empty.**  `C'(λ)` at `λ ≤ 0` forbids
every piece, and the empty word is a piece as soon as the symmetrization has two
members — which it does for any nonempty relator, since a cyclically reduced
relator and its formal inverse are distinct: were they equal, `r ++ r` would be
reduced and spell the identity.

So every relator is trivial, the normal closure is trivial, and no nonempty
reduced word lies in it. -/
theorem greendlingerConclusionSharp_of_nonpos {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hlam : lam ≤ 0)
    (hmetric : MetricSmallCancellation R lam) : GreendlingerConclusionSharp R lam := by
  classical
  intro w hw hwne hmem
  exfalso
  have hRnil : ∀ r ∈ R, FreeGroup.mk r = (1 : FreeGroup α) := by
    intro r hrR
    by_contra hne
    have hcyc := hR r hrR
    have hrne : r ≠ [] := by
      intro hnil
      exact hne (by rw [hnil, ← FreeGroup.one_eq_mk])
    have hrmem : r ∈ symmetrization R := subset_symmetrization R hrR
    have hinv : FreeGroup.invRev r ∈ symmetrization R := invRev_mem_symmetrization hrmem
    have hdist : r ≠ FreeGroup.invRev r := by
      intro heq
      have hmkinv : FreeGroup.mk r = (FreeGroup.mk r)⁻¹ := by
        rw [← mk_invRev_eq_inv, ← heq]
      have hcc : FreeGroup.IsCyclicallyReduced ((List.replicate 2 r).flatten) :=
        hcyc.flatten_replicate 2
      have hflat : (List.replicate 2 r).flatten = r ++ r := by simp
      rw [hflat] at hcc
      have hstep : FreeGroup.mk r * FreeGroup.mk r
          = FreeGroup.mk r * (FreeGroup.mk r)⁻¹ := by rw [← hmkinv]
      have hone : FreeGroup.mk (r ++ r) = 1 := by
        rw [mk_append_mul, hstep, mul_inv_cancel]
      have h2 := FreeGroup.reduce.sound
        (show FreeGroup.mk (r ++ r) = FreeGroup.mk ([] : List (α × Bool)) by
          rw [← FreeGroup.one_eq_mk]; exact hone)
      rw [hcc.isReduced.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
      have hlen := congrArg List.length h2
      rw [List.length_append, List.length_nil] at hlen
      exact hrne (List.length_eq_zero_iff.mp (by omega))
    have hpiece : IsPiece (symmetrization R) ([] : List (α × Bool)) :=
      ⟨r, hrmem, FreeGroup.invRev r, hinv, hdist, by simp, by simp⟩
    have hb := hmetric ([] : List (α × Bool)) hpiece r hrmem (by simp)
    rw [List.length_nil] at hb
    have hb' : (0 : ℚ) < lam * (r.length : ℚ) := by exact_mod_cast hb
    have hrnn : (0 : ℚ) ≤ (r.length : ℚ) := by positivity
    have h0 : lam * (r.length : ℚ) ≤ 0 * (r.length : ℚ) :=
      mul_le_mul_of_nonneg_right hlam hrnn
    rw [zero_mul] at h0
    linarith
  have hsub : FreeGroup.mk '' R ⊆ (⊥ : Subgroup (FreeGroup α)) := by
    rintro _ ⟨r, hrR, rfl⟩
    exact Subgroup.mem_bot.mpr (hRnil r hrR)
  have hle : Subgroup.normalClosure (FreeGroup.mk '' R) ≤ (⊥ : Subgroup (FreeGroup α)) :=
    Subgroup.normalClosure_le_normal hsub
  have h1 : FreeGroup.mk w = 1 := Subgroup.mem_bot.mp (hle hmem)
  have h2 := FreeGroup.reduce.sound
    (show FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) by
      rw [← FreeGroup.one_eq_mk]; exact h1)
  rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
  exact hwne h2

/-- **The scaffold.**  `ShellGate` — the curvature count in the shell form §1
argues for — is the whole of what the gate still needs.

This is a reduction, not a result: `ShellGate` is open. -/
theorem sharpGreendlingerGate_of_shellGate (h : ShellGate α) :
    GreendlingerFreeGate.SharpGreendlingerGate α := by
  intro R lam hR hlam hmetric
  rcases lt_or_ge 0 lam with hpos | hnonpos
  · exact greendlingerConclusionSharp_of_shell hpos hmetric
      (fun w hw hwne hmem => h R lam hR hpos hlam hmetric w hw hwne hmem)
  · exact greendlingerConclusionSharp_of_nonpos hR hnonpos hmetric

/-! ## 5.  Handing the count a *reduced* diagram -/

/-- Every element of the normal closure has a shortest-then-lightest expression.
The two well-orderings are `GreendlingerWeight.exists_isMinimalConjExpr`; this is
that, keyed to membership rather than to a factor count. -/
theorem exists_isMinimalConjExpr_of_mem_normalClosure [DecidableEq α]
    {R : Set (List (α × Bool))} {g : FreeGroup α}
    (hg : g ∈ Subgroup.normalClosure (FreeGroup.mk '' R)) :
    ∃ e, IsMinimalConjExpr R e g := by
  obtain ⟨n, hcount⟩ := (mem_normalClosure_iff R g).mp hg
  obtain ⟨e₀, hv₀, -, he₀⟩ := (isConjProduct_iff_exists_conjExpr n g).mp hcount
  exact exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩

/-- **OPEN — the curvature count, on a *minimal* expression.**  `ShellGate` with
an expression for `w` named and assumed shortest-then-lightest.

This is the form the count should actually be proved in, because the classical
curvature lemma is false without reducedness of the diagram, and minimality is
where reducedness comes from: on this hypothesis
`MinimalNoCancellingPair.ne_inv_conj_of_minimal` is free, so no two regions of
the picture cancel across the product between them.  The count never has to
assume that separately. -/
def ShellFromMinimal (α : Type*) [DecidableEq α] : Prop :=
  ∀ (R : Set (List (α × Bool))) (lam : ℚ),
    (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → 0 < lam → lam ≤ 1 / 6 →
    MetricSmallCancellation R lam →
    ∀ (w : List (α × Bool)) (e : List (FreeGroup α × List (α × Bool))),
      FreeGroup.IsReduced w → w ≠ [] →
      IsMinimalConjExpr R e (FreeGroup.mk w) →
      ∃ r ∈ symmetrization R, r ≠ [] ∧ ∃ δ p₁ p₂ p₃ : List (α × Bool),
        r = δ ++ (p₁ ++ (p₂ ++ p₃)) ∧ δ <:+: w ∧
          InteriorRun R r p₁ ∧ InteriorRun R r p₂ ∧ InteriorRun R r p₃

/-- **Minimality is free.**  A word of the normal closure has a minimal
expression, so asking the count for a shell only on minimal expressions asks for
no less. -/
theorem shellGate_of_shellFromMinimal [DecidableEq α] (h : ShellFromMinimal α) :
    ShellGate α := by
  intro R lam hR hlam0 hlam hmetric w hw hwne hmem
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr_of_mem_normalClosure hmem
  exact h R lam hR hlam0 hlam hmetric w e hw hwne hmin

/-- **What the count gets for its reducedness, checked.**  On the expression
`shellGate_of_shellFromMinimal` hands it, the reduced-diagram condition holds
outright: two regions of the picture, with any product between them, are never
mirror images glued so as to cancel.

This is `MinimalNoCancellingPair.ne_inv_conj_of_minimal` read at that
expression, and it is the whole of what `ShellFromMinimal`'s minimality
hypothesis is there to supply. -/
theorem noCancellingPair_of_shellFromMinimal_input [DecidableEq α]
    {R : Set (List (α × Bool))} {g : FreeGroup α}
    {A B C : List (FreeGroup α × List (α × Bool))} {c₁ c₂ : FreeGroup α}
    {s₁ s₂ : List (α × Bool)}
    (hmin : IsMinimalConjExpr R (A ++ (c₁, s₁) :: (B ++ (c₂, s₂) :: C)) g) :
    (conjEval B)⁻¹ * factorValue c₁ s₁ * conjEval B * factorValue c₂ s₂ ≠ 1 :=
  ne_inv_conj_of_minimal hmin

/-- **The scaffold, on the minimal form.**  This is the statement the curvature
count should be aimed at: prove `ShellFromMinimal` and the sharp gate follows.

Still a reduction, not a result: `ShellFromMinimal` is open. -/
theorem sharpGreendlingerGate_of_shellFromMinimal [DecidableEq α]
    (h : ShellFromMinimal α) : GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_shellGate (shellGate_of_shellFromMinimal h)

end SmallCancellationRouter
end GroupApproximation
