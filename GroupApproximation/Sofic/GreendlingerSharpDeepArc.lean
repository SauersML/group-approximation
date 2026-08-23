import GroupApproximation.Sofic.GreendlingerSharpRigidity

/-!
# The deep arc at an arbitrary constant

`GreendlingerDeepArc` runs the deep regime at `λ = 1/6`.  Its regime hypotheses
are `6 * j < |t|` and `|c| + |t| < |M| + j`, its engine is
`5|t| < 6|E|`, and every kill it performs is a reading of that one number
against the piece bound `C'(1/6)`.

Three pieces of that file are already twinned elsewhere:
`GreendlingerDeepVacuitySharp` carries the regime arithmetic
(`one_sub_lam_mul_lt_eaten`) and the two arc producers
(`greendlingerAtSharp_of_untouched_rotation`,
`greendlingerAtSharp_of_deep_arc`), and `GreendlingerSharpRigidity` carries the
rigidity core (`eq_of_lam_common_prefix`) and its intrusion form
(`eq_rotate_of_deep_intrusion_sharp`).  What was left untwinned is the middle of
the file: the weakening that feeds the rigidity core, and the four
impossibility statements §4 reads off it.

This file supplies exactly those.

## The weakening, and the only new side condition

At `1/6` the step from the deep bound to the rigidity bound is
`5|t| < 6|E| → |t| ≤ 6|E|`, which is `omega`.  Rationally it is
`(1 − λ)|t| < |E| → λ|t| ≤ |E|`, and that holds precisely because `λ ≤ 1 − λ`,
i.e. because `λ ≤ 1/2`.  `lam_mul_le_of_deep` is that step and `λ ≤ 1/2` is the
only hypothesis this file adds anywhere; it is free in range, since the lane's
consumers ask for `λ ≤ 1/8` and the gate assembly for `λ ≤ 1/6`.

The three coincidence kills of §2 take the rigidity bound `λ|t| ≤ |E|` as a
hypothesis, exactly as their `λ`-free originals take `|t| ≤ 6|E|`, so they need
no side condition at all: the constant enters only through `C'(λ)`.

`not_deep_eaten_buried_sharp` is the one kill that never touches relator
letters.  It weighs the half-pin `2|E| ≤ |t|` of
`GreendlingerBetaBranch.two_mul_eaten_le_of_minimal_reroute` against the deep
bound `(1 − λ)|t| < |E|`; the two are incompatible for every `λ ≤ 1/2`, which
at `λ = 1/6` is the "half against five sixths" of the `λ`-free file.

## The residual

§3 twins `DeepTailArc` and both directions of its equivalence with
`DeepArcSource`.  The sharp lane reaches `DeepArcSourceSharp` directly through
`GreendlingerDeepVacuitySharp.deepArcSourceSharp_of_deepOverrunArcSharp`, so
`DeepTailArcSharp` is not on the critical path to
`GreendlingerSharpResidualWiring.SharpResiduals`; it is here because the
head-side arithmetic it discharges is `λ`-free — the position bookkeeping never
sees the constant — and so the tail-form residual is available at every `λ` at
the same price it was available at a sixth.

Depends on `C'(λ)` exactly where the piece bound is read, and on minimality
exactly where a coincidence is refuted.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The weakening the rigidity core consumes -/

/-- **The deep bound is in particular the rigidity bound.**  The `λ`-twin of
`GreendlingerDeepArc.length_le_six_mul_of_deep`.

`GreendlingerDeepVacuitySharp.one_sub_lam_mul_lt_eaten` reads the deep regime as
`(1 − λ)|t| < |E|`; `eq_of_lam_common_prefix` asks for `λ|t| ≤ |E|`.  The step
between them is `λ ≤ 1 − λ`, which is `λ ≤ 1/2` — free in the lane's range, and
invisible at `λ = 1/6`, where the `λ`-free version is `5|t| < 6|E| → |t| ≤ 6|E|`
and closes by `omega`. -/
theorem lam_mul_le_of_deep {lam : ℚ} (hlam : lam ≤ 1 / 2)
    {t E : List (α × Bool)}
    (h : (1 - lam) * (t.length : ℚ) < (E.length : ℚ)) :
    lam * (t.length : ℚ) ≤ (E.length : ℚ) := by
  have hT : (0 : ℚ) ≤ (t.length : ℚ) := Nat.cast_nonneg _
  have hkey : (0 : ℚ) ≤ (1 - 2 * lam) * (t.length : ℚ) :=
    mul_nonneg (by linarith) hT
  linarith

/-- **The intrusion lands in the head relator, read off the regime.**  The
`λ`-twin of `GreendlingerDeepArc.eq_rotate_of_deep_eaten`.

Same composition as there — the regime arithmetic, then the weakening, then the
rigidity core — with `one_sub_lam_mul_lt_eaten` in place of
`five_mul_lt_six_mul_eaten` and `lam_mul_le_of_deep` in place of
`length_le_six_mul_of_deep`. -/
theorem eq_rotate_of_deep_eaten_sharp {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 2) (hmetric : MetricSmallCancellation R lam)
    {c t t' M E : List (α × Bool)} {j k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hM : M = E ++ FreeGroup.invRev c) (hEt : E <:+ t)
    (hj : (j : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + j)
    (hintr : FreeGroup.invRev E <+: t'.rotate k) :
    FreeGroup.invRev t = t'.rotate k :=
  eq_rotate_of_deep_intrusion_sharp hmetric ht ht' hEt
    (lam_mul_le_of_deep hlam (one_sub_lam_mul_lt_eaten hM hj hgt)) hintr

/-! ## 2.  The four coincidences the rigidity produces are all refuted -/

/-- **The (β) intrusion is impossible, at any depth and any constant.**  The
`λ`-twin of `GreendlingerDeepArc.not_deep_intrusion_of_reduced`.

Only the rigidity bound moves: `|t| ≤ 6|E|` becomes `λ|t| ≤ |E|`, and
`eq_rotate_of_deep_intrusion_sharp` replaces `eq_rotate_of_deep_intrusion`.  The
refutation itself is `GreendlingerReducedness.invRev_ne_rotate_of_isReduced`,
which is `λ`-free — it spends nothing but reducedness of the head palindrome —
so this kill still applies to a landing factor anywhere in the cascade. -/
theorem not_deep_intrusion_of_reduced_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c t t' E : List (α × Bool)} {i k : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hpal : FreeGroup.IsReduced (palindrome c t))
    (hEt : E <:+ t) (hlong : lam * (t.length : ℚ) ≤ (E.length : ℚ))
    (hi : 0 < i) (hic : i ≤ c.length)
    (halign : c.drop (c.length - i) <+: t'.rotate k)
    (hintr : FreeGroup.invRev E <+: t'.rotate (k + i)) : False :=
  invRev_ne_rotate_of_isReduced hpal hi hic halign
    (eq_rotate_of_deep_intrusion_sharp hmetric ht ht' hEt hlong hintr)

/-- **The hug intrusion is impossible.**  The `λ`-twin of
`GreendlingerDeepArc.not_deep_hug_adjacent`.

The head conjugator overhangs the next one by `q`, a prefix of the next
rotation, and the eaten stretch lands `q` letters in; rigidity turns that into
`invRev t = t'.rotate |q|`, which makes the two adjacent factors mutually
inverse.  Only the rigidity bound moves — the cancelling-pair argument
(`GreendlingerOverlap.mk_palindrome_mul_eq_one_of_coincidence` against
`GreendlingerRegime.mk_palindrome_mul_ne_one_of_minimal`) never sees the
constant. -/
theorem not_deep_hug_adjacent_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c c' q t t' E : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E <:+ t) (hlong : lam * (t.length : ℚ) ≤ (E.length : ℚ))
    (hcq : c = c' ++ q) (hqt : q <+: t')
    (hintr : FreeGroup.invRev E <+: t'.rotate q.length) : False :=
  mk_palindrome_mul_ne_one_of_minimal hmin
    (mk_palindrome_mul_eq_one_of_coincidence hcq hqt
      (eq_rotate_of_deep_intrusion_sharp hmetric ht ht' hEt hlong hintr))

/-- **The overhang intrusion is impossible.**  The `λ`-twin of
`GreendlingerDeepArc.not_deep_overhang_adjacent`.

The mirror configuration: the next conjugator is the head conjugator followed by
the inverse of a trailing block `E₂` of the eaten stretch, and what is left of
the stretch prefixes the next rotation.  The proof is quoted line for line from
the `λ`-free version with `eq_of_lam_common_prefix` in place of
`eq_of_sixth_common_prefix`; as there, the bound is spent on `E₁` alone, since
`E₁` is only the part of the stretch that escapes the conjugator, and the buried
part is `not_deep_eaten_buried_sharp`'s business. -/
theorem not_deep_overhang_adjacent_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hmetric : MetricSmallCancellation R lam)
    {c t t' E₁ E₂ : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t)
        :: (FreeGroup.mk (c ++ FreeGroup.invRev E₂), t') :: e) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hEt : E₁ ++ E₂ <:+ t) (hlong : lam * (t.length : ℚ) ≤ (E₁.length : ℚ))
    (hintr : FreeGroup.invRev E₁ <+: t') : False := by
  have hpre : FreeGroup.invRev E₂ ++ FreeGroup.invRev E₁
      <+: FreeGroup.invRev t := by
    have h := invRev_prefix_of_suffix hEt
    rwa [FreeGroup.invRev_append] at h
  have hy : FreeGroup.invRev E₂ <+: FreeGroup.invRev t :=
    (show FreeGroup.invRev E₂ <+: FreeGroup.invRev E₂ ++ FreeGroup.invRev E₁
      from ⟨FreeGroup.invRev E₁, rfl⟩).trans hpre
  have hrot : FreeGroup.invRev E₁
      <+: (FreeGroup.invRev t).rotate (FreeGroup.invRev E₂).length :=
    prefix_rotate_of_append_prefix hpre
  have heq : (FreeGroup.invRev t).rotate (FreeGroup.invRev E₂).length = t' := by
    refine eq_of_lam_common_prefix hmetric
      (rotate_mem_symmetrization (invRev_mem_symmetrization ht)
        (FreeGroup.invRev E₂).length) ht' hrot hintr ?_
    rw [List.length_rotate, FreeGroup.invRev_length, FreeGroup.invRev_length]
    exact hlong
  exact mk_palindrome_mul_ne_one_of_minimal hmin
    (mk_palindrome_mul_eq_one_of_coincidence'
      (y := FreeGroup.invRev E₂) rfl hy heq.symm)

/-- **A deep block cannot be buried in the next conjugator.**  The `λ`-twin of
`GreendlingerDeepArc.not_deep_eaten_buried`.

The one configuration in the adjacent junction analysis that carries no relator
letters at all, so `C'(λ)` has nothing to say and the weight move does the work
alone: `GreendlingerBetaBranch.two_mul_eaten_le_of_minimal_reroute` pins the
buried stretch at `2|E| ≤ |t₀ ++ E|`, and the deep regime puts it above
`(1 − λ)|t₀ ++ E|`.  Doubling the second and comparing gives
`(1 − 2λ)|t₀ ++ E| < 0`, which `λ ≤ 1/2` forbids.  At `λ = 1/6` this is the
`λ`-free file's "half against five sixths", discharged there by `omega`. -/
theorem not_deep_eaten_buried_sharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 2)
    {c t₀ E Z m : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t₀ ++ E)
        :: (FreeGroup.mk (c ++ (FreeGroup.invRev E ++ Z)), m) :: e) g)
    (hred : FreeGroup.IsReduced (c ++ (FreeGroup.invRev E ++ Z)))
    (hredc : FreeGroup.IsReduced c)
    (hdeep : (1 - lam) * ((t₀ ++ E).length : ℚ) < (E.length : ℚ)) : False := by
  have h := two_mul_eaten_le_of_minimal_reroute hmin hred hredc
  have hq : (2 : ℚ) * (E.length : ℚ) ≤ ((t₀ ++ E).length : ℚ) := by
    exact_mod_cast h
  have hX : (0 : ℚ) ≤ ((t₀ ++ E).length : ℚ) := Nat.cast_nonneg _
  have hkey : (0 : ℚ) ≤ (1 - 2 * lam) * ((t₀ ++ E).length : ℚ) :=
    mul_nonneg (by linarith) hX
  linarith

/-! ## 3.  The tail-form residual, and the reduction to it -/

/-- **The `λ`-twin of `GreendlingerDeepArc.DeepTailArc`.**  What the deep regime
still owes, stated on the tail word alone: the part of the tail that survives
the head's cancellation carries a located sharp arc, beginning at or after the
depth by which the block overran its own palindrome.

Every field is quoted from the `λ`-free predicate; only the offset hypothesis
and the conclusion's bound move, exactly as they do between `DeepArcSource` and
`GreendlingerSharpTwins.DeepArcSourceSharp`. -/
def DeepTailArcSharp [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t M B' : List (α × Bool))
    (e : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α) (j : ℕ),
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    t ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    M <:+ palindrome c t →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (j : ℚ) < lam * (t.length : ℚ) →
    c.length + t.length < M.length + j →
    GreendlingerAtSharp R lam (M.length + j - (c.length + t.length)) B'

/-- **The sharp deep obligation, from the sharp tail obligation.**  The `λ`-twin
of `GreendlingerDeepArc.deepArcSource_of_deepTailArc`.

The proof is the `λ`-free one unchanged, because none of it reads the constant:
prepending the head survivor moves the arc later by exactly `|P'|`, and
`|P'| + (|M| + j − (|c| + |t|))` is `|c| + j` by the same natural-number
identity.  The offset hypothesis is passed through opaquely. -/
theorem deepArcSourceSharp_of_deepTailArcSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (h : DeepTailArcSharp R lam) :
    DeepArcSourceSharp R lam := by
  intro c t e g P' M B' j hmin ht hredp heq htail hlow hj hgt
  have hlenP : P'.length + M.length = c.length + t.length + c.length := by
    have hb := congrArg List.length heq
    rw [List.length_append, length_palindrome] at hb
    exact hb.symm
  have harc :=
    h c t M B' e g j hmin ht hredp ⟨P', heq.symm⟩ htail hlow hj hgt
  refine (harc.append_left P').mono ?_
  omega

/-- **And conversely**, so the isolation is exact at every constant.  The
`λ`-twin of `GreendlingerDeepArc.deepTailArc_of_deepArcSource`.

In the deep regime the head survivor is strictly shorter than the required
offset, so any arc `DeepArcSourceSharp` produces begins strictly inside the tail
survivor and reading it there is the tail obligation.  The relator bound of the
arc is carried across untouched, which is why the `λ`-free proof serves
verbatim. -/
theorem deepTailArcSharp_of_deepArcSourceSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (h : DeepArcSourceSharp R lam) :
    DeepTailArcSharp R lam := by
  intro c t M B' e g j hmin ht hredp hMsuf htail hlow hj hgt
  obtain ⟨P', hP'⟩ := hMsuf
  have hlenP : P'.length + M.length = c.length + t.length + c.length := by
    have hb := congrArg List.length hP'
    rw [List.length_append, length_palindrome] at hb
    exact hb
  obtain ⟨A, u, C, hw, hAlen, s, hs, hupre, hlt⟩ :=
    h c t e g P' M B' j hmin ht hredp hP'.symm htail hlow hj hgt
  have hPpre : P' <+: P' ++ B' := ⟨B', rfl⟩
  have hApre : A <+: P' ++ B' :=
    ⟨u ++ C, by rw [hw]; simp only [List.append_assoc]⟩
  obtain ⟨A₂, hA₂⟩ := List.prefix_of_prefix_length_le hPpre hApre (by omega)
  have hA₂len : P'.length + A₂.length = A.length := by
    have hb := congrArg List.length hA₂
    rw [List.length_append] at hb
    exact hb
  have hB' : B' = A₂ ++ u ++ C := by
    have hb : P' ++ B' = P' ++ (A₂ ++ u ++ C) := by
      rw [hw, ← hA₂]
      simp only [List.append_assoc]
    exact List.append_cancel_left hb
  exact ⟨A₂, u, C, hB', by omega, s, hs, hupre, hlt⟩

/-! ## 4.  The gate, through the sharp residual -/

/-- `CascadeLandingSharp` from the sharp tail obligation and the sharp landing
production.  The `λ`-twin of
`GreendlingerDeepArc.cascadeLanding_of_deepTailArc_of_landing`. -/
theorem cascadeLandingSharp_of_deepTailArcSharp_of_landingSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hdeep : DeepTailArcSharp R lam) (hland : LandingProductionSharp R lam) :
    CascadeLandingSharp R lam :=
  cascadeLandingSharp_of_deepArcSharp_of_landingSharp
    (deepArcSourceSharp_of_deepTailArcSharp hdeep) hland

/-- **The sharp conclusion, reduced to the sharp tail obligation and the (β)
landing residual.**  The `λ`-twin of
`GreendlingerDeepArc.greendlingerConclusion_of_deepTailArc_of_landing`, taken at
the (β) form of the landing side, which is the one the assembly consumes.

Nothing else is assumed: the head-side arithmetic of the deep regime is
discharged by §3, and what the deep branch still owes is a located sharp arc in
the surviving tail word. -/
theorem greendlingerConclusionSharp_of_deepTailArcSharp_of_betaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepTailArcSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_deepArcSharp_of_betaSharp hR hRne hlam0 hlam
    hmetric (deepArcSourceSharp_of_deepTailArcSharp hdeep) hbeta

end SmallCancellationRouter
end GroupApproximation
