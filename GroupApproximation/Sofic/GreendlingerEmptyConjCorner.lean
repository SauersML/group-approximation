import GroupApproximation.Sofic.GreendlingerNoDeepCollapse

/-!
# The empty-conjugator corner is a Greendlinger statement about a short prefix

`GreendlingerNoDeepCollapse` chases the residual `NoDeepCollapse` down to one
corner, `NoDeepCollapseEmptyConj`: the head conjugator is empty, the head
factor already carries weight `0`, and the move that spends weight minimality
everywhere else only ties.  Its docstring records what a proof has to
contradict, and names it "a Greendlinger-shaped statement about the relator
family".  This file makes that exact, and settles two things about it.

## 1.  What the corner actually says

At `c = []` the head palindrome *is* the relator: `palindrome [] t = t`, so the
drop equation reads `t = P' ++ M`, and the collapse gives `g = mk P'`
(`mk_eq_of_collapse`) with `P' ≠ []` (`prefix_ne_nil_of_collapse`).  The two
overrun hypotheses, unused in `ne_nil_of_conj_ne_nil`, are what carry the corner:
with `c = []` they read `|P'| < i` and `(i : ℚ) < lam·|t|`, so

    `P'` is a **nonempty reduced prefix of a symmetrized relator `t`, shorter
    than `lam·|t|`, spelling an element of the normal closure.**

`emptyConj_collapse_data` packages exactly that.  Greendlinger's lemma forbids
it outright, and `not_short_arc_of_metric` is the piece computation that turns
the forbidding into a contradiction: an arc of more than half of some `r` sitting
inside such a `P'` is shorter than `lam·|t|`, hence `|r| < |t|`, hence `r` is not
the rotation of `t` that carries the arc, hence the arc is a *piece* — and
`C'(lam)` caps a piece of `r` at `lam·|r| < |r|/2`.

`noDeepCollapseEmptyConj_of_greendlingerConclusion` is the resulting reduction.
It reads the **half-form** `GreendlingerConclusion`, not the sharp form, and it
does **not** go through `GreendlingerDehn`'s open `DehnReduceClosed`: any route
to the half-form closes the corner, and `GreendlingerFreeGate` converts the
sharp form to the half-form at `lam ≤ 1/6`.

This is not a discharge.  `GreendlingerConclusion` is a definition, and the
routing lane consumes `DeepCompositeLandsSharp` on its own way to
`GreendlingerConclusionSharp` (`GreendlingerSharpDropGate`), so feeding the
lane's own output back into this leaf is circular.  What the reduction buys is
an *ordering*: the corner is no harder than the half-form, so a family that
obtains the half-form by any other route — the Dehn route once
`DehnReduceClosed` lands, a hand-checked family — closes the corner, and with it
the gap between `DeepCompositeLandsSharp'` and `DeepCompositeLandsSharp`.

## 2.  What is proved without Greendlinger

`not_collapse_of_length_one` settles the corner's first case, `|e| = 1`, from
`C'(lam)` alone.  A one-factor tail spells a conjugate of a symmetrized relator,
which `GreendlingerWeight.exists_palindrome_factor` puts in palindromic normal
form; the collapse pins that palindrome to be `invRev M` letter for letter, so
its rotation `t₀` is a symmetrized relator sitting *inside* `invRev t` as a
contiguous subword.  `eq_length_of_infix_of_mem` — a symmetrized relator
occurring inside another one is a piece of itself, so the two have equal length —
then forces `|t₀| = |t|`, against `|t₀| ≤ |M| = |t| − |P'| < |t|`.

That lemma needs `lam ≤ 1` only, and it costs one hypothesis the deep lane does
not otherwise carry: cyclic reducedness of `R`.

## 3.  The metric hypothesis is not optional

`NoDeepCollapseEmptyConj R lam` carries no small-cancellation hypothesis at all,
and it is **false** at `lam = 1/6`.  Witness, over `ℕ` with all letters positive
(stated here, not formalized): `t = x₀x₁⋯x₁₂`, `P' = x₀`, `M = x₁⋯x₁₂`,
`R = {t, M}`, and the expression `[(1, t), (1, invRev M)]` for `g = mk x₀`.  It
is valid, spells `g`, has weight `0`, and is minimal — a shorter expression is
either empty, and `‖x₀‖ = 1 ≠ 0`, or one conjugate, and then
`exists_palindrome_factor` writes `x₀` as a reduced palindrome around a
symmetrized relator, forcing a relator of length `1` where `R` has only lengths
`12` and `13`.  Every field of the corner then holds at `i = 2`:
`2 < (1/6)·13` and `0 + 13 < 12 + 2`, with `B' = []`.

So `lam ≤ 1/6` alone cannot prove the corner; only `MetricSmallCancellation`
can, and `R = {t, M}` indeed fails it — `M` is a piece of length `12`.  So
every statement below carries the metric hypothesis explicitly, and
`deepCompositeLandsSharp_of_sharp'_of_emptyConj` can only ever be discharged
with it in scope.

Nothing here discharges `NoDeepCollapse`, `NoDeepCollapseEmptyConj`,
`GreendlingerConclusion`, `DeepCompositeLandsSharp` or
`DeepCompositeLandsSharp'`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  Rotating an occurrence to the front -/

/-- **An occurrence inside a symmetrized relator is a prefix of one.**  The
symmetrization is closed under rotation, so a contiguous subword of a member
prefixes a member of the same length. -/
theorem exists_prefix_mem_symmetrization_of_infix {R : Set (List (α × Bool))}
    {w u : List (α × Bool)} (hw : w ∈ symmetrization R) (hu : u <:+: w) :
    ∃ v, v ∈ symmetrization R ∧ u <+: v ∧ v.length = w.length := by
  obtain ⟨A, B, hAB⟩ := hu
  have hsplit : A ++ (u ++ B) = w := by
    rw [← List.append_assoc]
    exact hAB
  refine ⟨u ++ B ++ A, append_swap_mem_symmetrization (by rw [hsplit]; exact hw),
    ⟨B ++ A, (List.append_assoc u B A).symm⟩, ?_⟩
  have h1 : (u ++ B ++ A).length = u.length + B.length + A.length := by
    rw [List.length_append, List.length_append]
  have h2 : w.length = A.length + (u.length + B.length) := by
    rw [← hsplit, List.length_append, List.length_append]
  omega

/-- **A symmetrized relator inside a symmetrized relator has the same length.**

Rotate the occurrence to the front: either the rotation *is* the inner relator,
and the lengths agree, or the two are distinct members of the symmetrization
with the inner one a common prefix — that is, the inner relator is a piece of
itself, which `C'(lam)` forbids for any `lam ≤ 1`.

This is the whole small-cancellation content of the `|e| = 1` case below, and it
is the classical statement that no relator is a subword of another. -/
theorem eq_length_of_infix_of_mem {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1) (hmetric : MetricSmallCancellation R lam)
    {w v : List (α × Bool)} (hw : w ∈ symmetrization R)
    (hv : v ∈ symmetrization R) (hvw : v <:+: w) : v.length = w.length := by
  obtain ⟨v', hv', hpre, hlenv'⟩ := exists_prefix_mem_symmetrization_of_infix hw hvw
  rcases eq_or_ne v v' with h | h
  · rw [h]
    exact hlenv'
  · exfalso
    have hpiece : IsPiece (symmetrization R) v :=
      ⟨v, hv, v', hv', h, List.prefix_refl v, hpre⟩
    have hlt : (v.length : ℚ) < lam * (v.length : ℚ) :=
      hmetric v hpiece v hv (List.prefix_refl v)
    have hnn : (0 : ℚ) ≤ (v.length : ℚ) := by positivity
    have hb : lam * (v.length : ℚ) ≤ 1 * (v.length : ℚ) :=
      mul_le_mul_of_nonneg_right hlam hnn
    rw [one_mul] at hb
    linarith

/-! ## 2.  A short Greendlinger arc inside a relator is a piece -/

/-- **No short arc.**  Suppose an arc `u` occurs inside a symmetrized relator
`w`, prefixes a symmetrized relator `r` of which it is more than half, and is
shorter than `lam·|w|`.  Then `|r| < 2|u| < 2·lam·|w| ≤ |w|/3`, so `r` is not the
rotation of `w` that carries the occurrence; the two are distinct members of the
symmetrization sharing the prefix `u`, so `u` is a piece, and `C'(lam)` caps it
at `lam·|r| ≤ |r|/6 < |u|/3`.

This is the contradiction Greendlinger's lemma runs into on a *short* subword of
a relator, and it is the only small-cancellation input the reduction below
needs. -/
theorem not_short_arc_of_metric {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    {w r u : List (α × Bool)} (hw : w ∈ symmetrization R)
    (hr : r ∈ symmetrization R) (huw : u <:+: w) (hur : u <+: r)
    (hhalf : r.length < 2 * u.length)
    (hshort : (u.length : ℚ) < lam * (w.length : ℚ)) : False := by
  have hupos : 0 < u.length := by omega
  have huwlen : u.length ≤ w.length := huw.length_le
  obtain ⟨v, hv, huv, hvlen⟩ := exists_prefix_mem_symmetrization_of_infix hw huw
  have hcast1 : (r.length : ℚ) < 2 * (u.length : ℚ) := by exact_mod_cast hhalf
  have hwpos : (1 : ℚ) ≤ (w.length : ℚ) := by
    exact_mod_cast (show 1 ≤ w.length by omega)
  have hwnn : (0 : ℚ) ≤ (w.length : ℚ) := by positivity
  have hmul : 2 * lam * (w.length : ℚ) ≤ 1 / 3 * (w.length : ℚ) :=
    mul_le_mul_of_nonneg_right (by linarith) hwnn
  have hrw : (r.length : ℚ) < (w.length : ℚ) := by linarith
  have hne : r ≠ v := by
    intro h
    rw [h, hvlen] at hrw
    exact lt_irrefl _ hrw
  have hpiece : IsPiece (symmetrization R) u := ⟨r, hr, v, hv, hne, hur, huv⟩
  have hfin : (u.length : ℚ) < lam * (r.length : ℚ) := hmetric u hpiece r hr hur
  have hunn : (1 : ℚ) ≤ (u.length : ℚ) := by exact_mod_cast hupos
  have hrnn : (0 : ℚ) ≤ (r.length : ℚ) := by positivity
  rcases le_or_gt lam 0 with hl | hl
  · have h0 : lam * (r.length : ℚ) ≤ 0 * (r.length : ℚ) :=
      mul_le_mul_of_nonneg_right hl hrnn
    rw [zero_mul] at h0
    linarith
  · have h1 : lam * (r.length : ℚ) < lam * (2 * (u.length : ℚ)) :=
      mul_lt_mul_of_pos_left hcast1 hl
    have h2 : 2 * lam * (u.length : ℚ) ≤ 1 / 3 * (u.length : ℚ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith

/-! ## 3.  What the corner hands a prover -/

/-- **The corner, unpacked.**  At an empty head conjugator a collapsed deep
configuration is exactly a nonempty reduced prefix of the symmetrized relator
`t`, shorter than `lam·|t|`, spelling an element of the normal closure.

The two overrun hypotheses are spent here and nowhere else: with `c = []` the
drop bound reads `|P'| < i` and the metric bound reads `i < lam·|t|`.  Compare
`ne_nil_of_conj_ne_nil`, which uses neither. -/
theorem emptyConj_collapse_data [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} {t P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {i : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk ([] : List (α × Bool)), t) :: e) g)
    (hredp : FreeGroup.IsReduced (palindrome ([] : List (α × Bool)) t))
    (heq : palindrome ([] : List (α × Bool)) t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : ([] : List (α × Bool)).length + t.length < M.length + i)
    (hnil : B' = []) :
    t = P' ++ M ∧ P' ≠ [] ∧ FreeGroup.IsReduced P' ∧ P' <+: t ∧
      FreeGroup.mk P' ∈ Subgroup.normalClosure (FreeGroup.mk '' R) ∧
      (P'.length : ℚ) < lam * (t.length : ℚ) := by
  have hsplit : t = P' ++ M := by
    have h := heq
    rwa [palindrome_nil] at h
  have hredt : FreeGroup.IsReduced t := by
    have h := hredp
    rwa [palindrome_nil] at h
  have hP'ne : P' ≠ [] := prefix_ne_nil_of_collapse hmin heq htail hnil
  have hg : g = FreeGroup.mk P' := mk_eq_of_collapse hmin heq htail hnil
  have hP'pre : P' <+: t := ⟨M, hsplit.symm⟩
  have hP'red : FreeGroup.IsReduced P' :=
    isReduced_of_infix hP'pre.isInfix hredt
  have hmem : FreeGroup.mk P' ∈ Subgroup.normalClosure (FreeGroup.mk '' R) := by
    have hcp : IsConjProduct R
        ((FreeGroup.mk ([] : List (α × Bool)), t) :: e).length g :=
      (isConjProduct_iff_exists_conjExpr _ g).mpr
        ⟨(FreeGroup.mk ([] : List (α × Bool)), t) :: e, hmin.1, rfl, hmin.2.1⟩
    have hmg := mem_normalClosure_of_isConjProduct hcp
    rwa [hg] at hmg
  have hlenT : t.length = P'.length + M.length := by
    rw [hsplit, List.length_append]
  have hP'lt : P'.length < i := by
    rw [List.length_nil] at hgt
    omega
  have hshort : (P'.length : ℚ) < lam * (t.length : ℚ) :=
    lt_trans (by exact_mod_cast hP'lt) hi
  exact ⟨hsplit, hP'ne, hP'red, hP'pre, hmem, hshort⟩

/-! ## 4.  The corner from the half-form Greendlinger conclusion -/

/-- **The empty-conjugator corner, from the Greendlinger conclusion.**

The corner exhibits a nonempty reduced word of the normal closure inside a
symmetrized relator and shorter than `lam` times it.  Greendlinger's conclusion
puts more than half of some relator inside that word, and
`not_short_arc_of_metric` shows `C'(lam)` has no room for it.

Only the *half-form* is read.  `GreendlingerFreeGate.greendlingerConclusion_of_sharp`
supplies it from `GreendlingerConclusionSharp R lam` at `lam ≤ 1/6`, and
`GreendlingerDehn.greendlingerConclusion_of_dehnReduceClosed` supplies it from
`DehnReduceClosed`; either route closes the corner. -/
theorem noDeepCollapseEmptyConj_of_greendlingerConclusion [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hgreen : GreendlingerConclusion R) : NoDeepCollapseEmptyConj R lam := by
  intro c t _c₂ _t₂ e _f g P' M B' i hc hmin _hmin₂ ht _ht₂ hredp _hredp₂ heq
    htail _hlow hi hgt hnil
  subst hc
  obtain ⟨-, hP'ne, hP'red, hP'pre, hmem, hshort⟩ :=
    emptyConj_collapse_data hmin hredp heq htail hi hgt hnil
  obtain ⟨r, hr, u, huP', hur, hhalf⟩ := hgreen P' hP'red hP'ne hmem
  have hut : u <:+: t := huP'.trans hP'pre.isInfix
  have hushort : (u.length : ℚ) < lam * (t.length : ℚ) :=
    lt_of_le_of_lt (by exact_mod_cast huP'.length_le) hshort
  exact not_short_arc_of_metric hlam hmetric ht hr hut hur hhalf hushort

/-- The residual itself, from the same input. -/
theorem noDeepCollapse_of_greendlingerConclusion [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hgreen : GreendlingerConclusion R) : NoDeepCollapse R lam :=
  noDeepCollapse_of_emptyConj
    (noDeepCollapseEmptyConj_of_greendlingerConclusion hlam hmetric hgreen)

/-- **The repair, closed by the half-form.**  `DeepCompositeLandsSharp'` gives
back `DeepCompositeLandsSharp` for any family whose Greendlinger conclusion is
known — the gap between the repaired leaf and the original is exactly a
half-form statement about the relators. -/
theorem deepCompositeLandsSharp_of_sharp'_of_greendlingerConclusion
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ} (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hgreen : GreendlingerConclusion R) (h : DeepCompositeLandsSharp' R lam) :
    DeepCompositeLandsSharp R lam :=
  deepCompositeLandsSharp_of_sharp'_of_emptyConj h
    (noDeepCollapseEmptyConj_of_greendlingerConclusion hlam hmetric hgreen)

/-! ## 5.  The first case of the corner, without Greendlinger -/

/-- **The corner's one-factor case is empty.**

`|e| = 1` makes the pinned tail a single conjugate of a symmetrized relator, so
`exists_palindrome_factor` writes it as a reduced palindrome `c₀ ++ t₀ ++ invRev c₀`
around a symmetrized `t₀`.  The collapse says that palindrome *is* `invRev M`
letter for letter, so `t₀` occurs inside `invRev M`, hence inside the symmetrized
relator `invRev t`.  By `eq_length_of_infix_of_mem` the two then have equal
length — but `|t₀| ≤ |M| = |t| − |P'| < |t|`, because the survivor `P'` is
nonempty.

No Greendlinger conclusion is read, and no numeric hypothesis beyond `lam ≤ 1`:
the overrun bounds go unused.  The price is `hcyc`, which the deep lane does not
otherwise carry. -/
theorem not_collapse_of_length_one [DecidableEq α] {R : Set (List (α × Bool))}
    {lam : ℚ} (hlam : lam ≤ 1)
    (hcyc : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R lam)
    {c t P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (ht : t ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hc : c = []) (hlen : e.length = 1) : B' ≠ [] := by
  intro hnil
  subst hc
  rcases e with _ | ⟨xs, e'⟩
  · rw [List.length_nil] at hlen
    omega
  · have he' : e' = [] := by
      rw [List.length_cons] at hlen
      exact List.length_eq_zero_iff.mp (by omega)
    subst he'
    obtain ⟨x, s⟩ := xs
    have hvalid := conjValid_cons_iff.mp hmin.1
    have hs : s ∈ symmetrization R := (conjValid_cons_iff.mp hvalid.2).1
    have hev : conjEval [(x, s)] = (FreeGroup.mk M)⁻¹ :=
      conjEval_eq_inv_of_collapse htail hnil
    have hP'ne : P' ≠ [] := prefix_ne_nil_of_collapse hmin heq htail hnil
    have hsplit : t = P' ++ M := by
      have h := heq
      rwa [palindrome_nil] at h
    have hredt : FreeGroup.IsReduced t := by
      have h := hredp
      rwa [palindrome_nil] at h
    have hredM : FreeGroup.IsReduced M :=
      isReduced_of_infix ⟨P', [], by rw [List.append_nil]; exact hsplit.symm⟩ hredt
    have hredIM : FreeGroup.IsReduced (FreeGroup.invRev M) :=
      isReduced_invRev_iff.mpr hredM
    obtain ⟨c₀, t₀, ht₀, hred₀, heq₀, -⟩ := exists_palindrome_factor hcyc hRne hs x
    have hmkpal : FreeGroup.mk (palindrome c₀ t₀)
        = FreeGroup.mk (FreeGroup.invRev M) := by
      rw [mk_palindrome, heq₀, mk_invRev_eq_inv, ← hev, conjEval_cons,
        conjEval_nil, mul_one]
    have hpal : palindrome c₀ t₀ = FreeGroup.invRev M := by
      have h6 := FreeGroup.reduce.sound hmkpal
      rwa [hred₀.reduce_eq, hredIM.reduce_eq] at h6
    have hP2 : palindrome c₀ t₀ = c₀ ++ (t₀ ++ FreeGroup.invRev c₀) := by
      unfold palindrome
      rw [List.append_assoc]
    have hlenpal : (palindrome c₀ t₀).length
        = c₀.length + (t₀.length + c₀.length) := by
      rw [hP2, List.length_append, List.length_append, FreeGroup.invRev_length]
    have hlenrel : c₀.length + (t₀.length + c₀.length) = M.length := by
      have h := congrArg List.length hpal
      rw [hlenpal, FreeGroup.invRev_length] at h
      exact h
    have ht₀inf : t₀ <:+: FreeGroup.invRev M := by
      refine ⟨c₀, FreeGroup.invRev c₀, ?_⟩
      have h := hpal
      unfold palindrome at h
      exact h
    have hinvt : FreeGroup.invRev t
        = FreeGroup.invRev M ++ FreeGroup.invRev P' := by
      rw [hsplit, FreeGroup.invRev_append]
    have hMinf : FreeGroup.invRev M <:+: FreeGroup.invRev t := by
      refine ⟨[], FreeGroup.invRev P', ?_⟩
      rw [hinvt, List.nil_append]
    have hinvtmem : FreeGroup.invRev t ∈ symmetrization R :=
      invRev_mem_symmetrization ht
    have heqlen : t₀.length = (FreeGroup.invRev t).length :=
      eq_length_of_infix_of_mem hlam hmetric hinvtmem ht₀ (ht₀inf.trans hMinf)
    have hinvtlen : (FreeGroup.invRev t).length = t.length := by
      rw [FreeGroup.invRev_length]
    have hlenT : t.length = P'.length + M.length := by
      rw [hsplit, List.length_append]
    have hP'pos : 0 < P'.length := List.length_pos_iff.mpr hP'ne
    omega

end SmallCancellationRouter
end GroupApproximation
