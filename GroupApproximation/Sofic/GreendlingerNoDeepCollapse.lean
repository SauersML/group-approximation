import GroupApproximation.Sofic.GreendlingerCompositeWellPosed

/-!
# The collapse corner is a statement about the head conjugator

`GreendlingerCompositeWellPosed.NoDeepCollapse` is the residual the minimal
repair of the deep composite leaf leaves behind: *no deep configuration has its
tail word eaten whole*, `B' ≠ []`.  `tail_ne_nil_of_deep` settles its two-factor
case from the junction kill; this file settles everything except a single
corner, and the corner is not where the deep numerics live.

## 1.  What an eaten tail word says

`B' = []` turns the hypothesis `(conjEval e).toWord = invRev M ++ B'` into
`conjEval e = (mk M)⁻¹` (`conjEval_eq_inv_of_collapse`), and then the head
factor's own palindrome telescopes:

    g = mk (palindrome c t) * (mk M)⁻¹ = mk P' * mk M * (mk M)⁻¹ = mk P'.

So a collapsed configuration *computes* `g`: it is spelled by the survivor `P'`
of the head's palindrome (`mk_eq_of_collapse`).  Two consequences are immediate
and both are spent below:

* `P' ≠ []` (`prefix_ne_nil_of_collapse`) — otherwise `g = 1` and the empty
  expression beats the minimal one on length;
* `IsMinimalConjExpr R e ((mk M)⁻¹)` (`isMinimalConjExpr_tail_of_collapse`) —
  a shorter or lighter expression for `(mk M)⁻¹` would, with the head factor
  put back in front, be a shorter or lighter expression for `g`.

## 2.  The move that spends weight minimality

`not_isMinimalConjExpr_of_tail_move` is the whole mechanism.  Since
`conjEval e` is pinned, the head factor is redundant *where it stands*: any
symmetrized `s` and conjugator `x` with
`conjEval e * (x * mk s * x⁻¹) = g` gives an expression `e ++ [(x, s)]` of the
same length as `(mk c, t) :: e` and of weight `conjWeight e + |x|`, against the
original's `conjWeight e + |c|`.  Weight-minimality therefore forbids
`|x| < |c|`.

The head factor can always be moved to the end: the identity
`g⁻¹ * mk (palindrome c t) * g` is a conjugate of `mk t`, so `x = g⁻¹ * mk c`
works, and with `g = mk P'` that conjugator is measured by how `P'` and `c`
overlap inside `palindrome c t = c ++ t ++ invRev c`.  Three positions, and
`|c| < |M|` kills the third:

* `|P'| ≤ |c|` — then `c = P' ++ c''` and `x = mk c''`, of norm `|c| − |P'|`.
  The move is strictly lighter because `P' ≠ []`.  **No hypothesis on `c`.**
* `|c| < |P'| ≤ |c| + |t|` — then `P' = c ++ T₀` with `t = T₀ ++ E₁`, and the
  same conjugator is `(mk T₀)⁻¹`.  Rotating the relator absorbs it: `E₁ ++ T₀`
  is a rotation of `t`, hence symmetrized, and the moved factor is
  `(1, E₁ ++ T₀)` — weight `0`.  The move is strictly lighter as soon as
  `c ≠ []`.
* `|c| + |t| < |P'|` — then `|M| < |c|`, which `hlow` denies.

So `ne_nil_of_conj_ne_nil` proves the collapse impossible whenever the head
conjugator is nonempty, and it reads *none* of the deep numerics beyond
`c.length < M.length`: no `λ`, no `i`, no metric condition, no adjacent factor,
no `hRne`.  The two overrun hypotheses `(i : ℚ) < λ|t|` and
`|c| + |t| < |M| + i` are not used at all.

## 3.  What is left

`NoDeepCollapseEmptyConj` is `NoDeepCollapse` restricted to `c = []`, and
`noDeepCollapse_of_emptyConj` says that restriction is the whole remaining
content.  In that corner the head factor already carries weight `0`, so the
move above is a tie rather than a saving, and the configuration is
self-dual under `conjInv`: writing `t = P' ++ M`, the expression
`e ++ [(1, M ++ P')]` is another *minimal* expression for `g = mk P'`, and its
backwards reading is again a collapsed configuration with empty head
conjugator.  Weight minimality is therefore exhausted there; what a proof of
the corner has to contradict is

    `mk M` — a suffix of a symmetrized relator `t`, with `t = P' ++ M` and
    `P' ≠ []` — is spelled *exactly*, with no free cancellation left over, by a
    minimal product of `|e|` conjugates.

That is a Greendlinger-shaped statement about the relator family, not a
statement about landing sites, and it is not available here:
`GreendlingerDehn`'s route to it turns on the open `DehnReduceClosed`.

Nothing here discharges `NoDeepCollapse`, `NoDeepCollapseEmptyConj`,
`DeepCompositeLandsSharp` or `DeepCompositeLandsSharp'`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  Replacing the tail of an expression -/

/-- Two expressions with the same value behind the same leading factor spell the
same element. -/
theorem conjEval_cons_eq_of_tail {c t : List (α × Bool)}
    {e e' : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (he : conjEval ((FreeGroup.mk c, t) :: e) = g)
    (hee' : conjEval e' = conjEval e) :
    conjEval ((FreeGroup.mk c, t) :: e') = g := by
  rw [conjEval_cons, hee', ← conjEval_cons]
  exact he

/-- **The move that spends weight minimality.**

If the element the tail spells already determines `g` up to one conjugate of a
symmetrized relator, that conjugate can be appended at the *end* of the tail
instead of standing in front of it.  The result has the same length, so
weight-minimality of the original bounds the new conjugator from below: no
admissible replacement is lighter than the head conjugator `c`.

This is the only place minimality is spent below, and it is spent in the same
currency as `GreendlingerWeight.not_absorb_of_minimal` — length fixed, weight
strictly down — but with the *whole* head factor relocated rather than two
adjacent factors reordered. -/
theorem not_isMinimalConjExpr_of_tail_move [DecidableEq α]
    {R : Set (List (α × Bool))} {c t : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (x : FreeGroup α) (s : List (α × Bool)) (hs : s ∈ symmetrization R)
    (hval : conjEval e * (x * FreeGroup.mk s * x⁻¹) = g)
    (hlt : FreeGroup.norm x < FreeGroup.norm (FreeGroup.mk c)) : False := by
  obtain ⟨hv, -, -, hw⟩ := hmin
  obtain ⟨-, h2⟩ := conjValid_cons_iff.mp hv
  have hv2 : ConjValid R (e ++ [(x, s)]) :=
    conjValid_append h2 (conjValid_cons_iff.mpr ⟨hs, conjValid_nil R⟩)
  have he2 : conjEval (e ++ [(x, s)]) = g := by
    rw [conjEval_append, conjEval_cons, conjEval_nil, mul_one]
    exact hval
  have hlen2 : (e ++ [(x, s)]).length = ((FreeGroup.mk c, t) :: e).length := by
    simp
  have hb := hw (e ++ [(x, s)]) hv2 he2 hlen2
  simp only [conjWeight_cons, conjWeight_append, conjWeight_nil] at hb
  omega

/-! ## 2.  What an eaten tail word says -/

/-- **An eaten tail word pins the tail.**  If nothing survives the head's
cancellation then the expression past the head spells exactly the inverse of the
block. -/
theorem conjEval_eq_inv_of_collapse [DecidableEq α] {M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))}
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B') (hnil : B' = []) :
    conjEval e = (FreeGroup.mk M)⁻¹ := by
  have h : FreeGroup.mk (conjEval e).toWord = conjEval e := FreeGroup.mk_toWord
  rw [htail, hnil, List.append_nil, mk_invRev_eq_inv] at h
  exact h.symm

/-- **A collapsed configuration computes its own element.**  The head's
palindrome telescopes against the pinned tail, and what is left is the survivor
`P'`:  `g = mk P'`.

Nothing but the drop equation and the collapse enters; minimality is not read. -/
theorem mk_eq_of_collapse [DecidableEq α] {R : Set (List (α × Bool))}
    {c t P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B') (hnil : B' = []) :
    g = FreeGroup.mk P' := by
  have hev : conjEval e = (FreeGroup.mk M)⁻¹ :=
    conjEval_eq_inv_of_collapse htail hnil
  have hMg : FreeGroup.mk P' * FreeGroup.mk M
      = FreeGroup.mk c * FreeGroup.mk t * (FreeGroup.mk c)⁻¹ := by
    rw [← mk_palindrome, heq, mk_append_mul]
  have h := hmin.2.1
  rw [conjEval_cons, hev, ← hMg, mul_inv_cancel_right] at h
  exact h.symm

/-- **The survivor of a collapsed configuration is nonempty.**  An empty
survivor makes `g` trivial, and the empty expression then beats the minimal one
on length. -/
theorem prefix_ne_nil_of_collapse [DecidableEq α] {R : Set (List (α × Bool))}
    {c t P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B') (hnil : B' = []) :
    P' ≠ [] := by
  have hg : g = FreeGroup.mk P' := mk_eq_of_collapse hmin heq htail hnil
  intro hP'
  have hone : (1 : FreeGroup α) = FreeGroup.mk ([] : List (α × Bool)) :=
    FreeGroup.one_eq_mk
  have h0 : conjEval ([] : List (FreeGroup α × List (α × Bool))) = g := by
    rw [conjEval_nil, hone, hg, hP']
  have hb := hmin.2.2.1 ([] : List (FreeGroup α × List (α × Bool)))
    (conjValid_nil R) h0
  simp only [List.length_cons, List.length_nil] at hb
  omega

/-- **The tail of a collapsed configuration is itself minimal.**  A shorter — or,
at equal length, a lighter — expression for `(mk M)⁻¹` becomes, with the head
factor put back in front of it, a shorter or lighter expression for `g`.

Recorded because it is what a proof of the remaining corner has to contradict:
in the corner the block `M` is a suffix of the symmetrized relator `t` itself,
and the statement says a minimal product of `|e|` conjugates spells it exactly. -/
theorem isMinimalConjExpr_tail_of_collapse [DecidableEq α]
    {R : Set (List (α × Bool))} {c t M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B') (hnil : B' = []) :
    IsMinimalConjExpr R e ((FreeGroup.mk M)⁻¹) := by
  have hev : conjEval e = (FreeGroup.mk M)⁻¹ :=
    conjEval_eq_inv_of_collapse htail hnil
  obtain ⟨hv, he, hlen, hw⟩ := hmin
  obtain ⟨h1, h2⟩ := conjValid_cons_iff.mp hv
  refine ⟨h2, hev, ?_, ?_⟩
  · intro e' hv' he'
    have hb := hlen ((FreeGroup.mk c, t) :: e')
      (conjValid_cons_iff.mpr ⟨h1, hv'⟩)
      (conjEval_cons_eq_of_tail he (by rw [he', hev]))
    simp only [List.length_cons] at hb
    omega
  · intro e' hv' he' hlen'
    have hb := hw ((FreeGroup.mk c, t) :: e')
      (conjValid_cons_iff.mpr ⟨h1, hv'⟩)
      (conjEval_cons_eq_of_tail he (by rw [he', hev]))
      (by simp only [List.length_cons, hlen'])
    simp only [conjWeight_cons] at hb
    omega

/-! ## 3.  The collapse is impossible off the empty conjugator -/

/-- **`NoDeepCollapse`, everywhere the head conjugator is nonempty.**

The head factor is moved to the end of the expression, conjugated by `g⁻¹` so
that the value is unchanged, and the resulting conjugator is measured against
`c`:

* `|P'| ≤ |c|` — the head conjugator loses its `P'`, and `P' ≠ []`;
* `|c| < |P'|` — the head conjugator is replaced by nothing at all, because the
  overshoot into the rotation is absorbed by rotating the relator, and `c ≠ []`;
* `|c| + |t| < |P'|` — impossible, since it forces `|M| < |c|`.

Only `hlow` is read of the deep hypothesis set: the overrun bounds
`(i : ℚ) < λ|t|` and `|c| + |t| < |M| + i`, the metric condition, `hRne` and the
adjacent factor `(c₂, t₂)` all go unused, and so does the second minimality
hypothesis.  The statement is a fact about *one* minimal expression and the
suffix its head's cancellation exposes. -/
theorem ne_nil_of_conj_ne_nil [DecidableEq α] {R : Set (List (α × Bool))}
    {c t P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length) (hc : c ≠ []) : B' ≠ [] := by
  intro hnil
  have ht : t ∈ symmetrization R := (conjValid_cons_iff.mp hmin.1).1
  have hev : conjEval e = (FreeGroup.mk M)⁻¹ :=
    conjEval_eq_inv_of_collapse htail hnil
  have hg : g = FreeGroup.mk P' := mk_eq_of_collapse hmin heq htail hnil
  have hP'ne : P' ≠ [] := prefix_ne_nil_of_collapse hmin heq htail hnil
  have hP2 : palindrome c t = c ++ (t ++ FreeGroup.invRev c) := by
    unfold palindrome
    rw [List.append_assoc]
  have hredc : FreeGroup.IsReduced c :=
    isReduced_of_infix ⟨[], t ++ FreeGroup.invRev c, by simp [palindrome]⟩ hredp
  have hcpre : c <+: palindrome c t := by
    rw [hP2]
    exact ⟨t ++ FreeGroup.invRev c, rfl⟩
  have hP'pre : P' <+: palindrome c t := ⟨M, heq.symm⟩
  have hMg : FreeGroup.mk P' * FreeGroup.mk M
      = FreeGroup.mk c * FreeGroup.mk t * (FreeGroup.mk c)⁻¹ := by
    rw [← mk_palindrome, heq, mk_append_mul]
  have hM : FreeGroup.mk M
      = (FreeGroup.mk P')⁻¹
        * (FreeGroup.mk c * FreeGroup.mk t * (FreeGroup.mk c)⁻¹) := by
    rw [← hMg, inv_mul_cancel_left]
  have hlenpal : (palindrome c t).length
      = c.length + (t.length + c.length) := by
    have h : (palindrome c t).length
        = c.length + (t.length + (FreeGroup.invRev c).length) := by
      rw [hP2, List.length_append, List.length_append]
    rw [FreeGroup.invRev_length] at h
    exact h
  have hsplitlen : P'.length + M.length = c.length + (t.length + c.length) := by
    rw [← hlenpal, heq, List.length_append]
  have hP'pos : 0 < P'.length := List.length_pos_iff.mpr hP'ne
  rcases le_or_gt P'.length c.length with hcase | hcase
  · -- the survivor stops inside the head conjugator: the move deletes it
    obtain ⟨c'', hc''⟩ := List.prefix_of_prefix_length_le hP'pre hcpre hcase
    have hredc'' : FreeGroup.IsReduced c'' :=
      isReduced_of_infix ⟨P', [], by rw [List.append_nil]; exact hc''⟩ hredc
    have hxc : (FreeGroup.mk P')⁻¹ * FreeGroup.mk c = FreeGroup.mk c'' := by
      rw [← hc'', mk_append_mul, inv_mul_cancel_left]
    have hlenc : c.length = P'.length + c''.length := by
      rw [← hc'', List.length_append]
    have hval : conjEval e
        * (FreeGroup.mk c'' * FreeGroup.mk t * (FreeGroup.mk c'')⁻¹) = g := by
      rw [hev, hg, ← hxc, hM]
      group
    have hwt : FreeGroup.norm (FreeGroup.mk c'')
        < FreeGroup.norm (FreeGroup.mk c) := by
      rw [norm_mk_of_isReduced hredc'', norm_mk_of_isReduced hredc]
      omega
    exact not_isMinimalConjExpr_of_tail_move hmin (FreeGroup.mk c'') t ht hval
      hwt
  · rcases le_or_gt P'.length (c.length + t.length) with hcase2 | hcase2
    · -- the survivor runs into the rotation: rotating the relator absorbs it
      obtain ⟨T₀, hT₀⟩ :=
        List.prefix_of_prefix_length_le hcpre hP'pre (le_of_lt hcase)
      have hlenT : P'.length = c.length + T₀.length := by
        rw [← hT₀, List.length_append]
      have hsplit : t ++ FreeGroup.invRev c = T₀ ++ M := by
        have h : c ++ (t ++ FreeGroup.invRev c) = c ++ (T₀ ++ M) := by
          rw [← hP2, heq, ← hT₀, List.append_assoc]
        exact List.append_cancel_left h
      have hTle : T₀.length ≤ t.length := by omega
      obtain ⟨E₁, hE₁⟩ : T₀ <+: t :=
        List.prefix_of_prefix_length_le ⟨M, hsplit.symm⟩
          ⟨FreeGroup.invRev c, rfl⟩ hTle
      have hsym : E₁ ++ T₀ ∈ symmetrization R :=
        append_swap_mem_symmetrization (by rw [hE₁]; exact ht)
      have hPc : FreeGroup.mk P' = FreeGroup.mk c * FreeGroup.mk T₀ := by
        rw [← hT₀, mk_append_mul]
      have hTt : FreeGroup.mk t = FreeGroup.mk T₀ * FreeGroup.mk E₁ := by
        rw [← hE₁, mk_append_mul]
      have hval : conjEval e
          * ((1 : FreeGroup α) * FreeGroup.mk (E₁ ++ T₀)
            * (1 : FreeGroup α)⁻¹) = g := by
        rw [hev, hg, hM, hPc, hTt, mk_append_mul]
        group
      have hwt : FreeGroup.norm (1 : FreeGroup α)
          < FreeGroup.norm (FreeGroup.mk c) := by
        rw [FreeGroup.norm_one, norm_mk_of_isReduced hredc]
        exact List.length_pos_iff.mpr hc
      exact not_isMinimalConjExpr_of_tail_move hmin 1 (E₁ ++ T₀) hsym hval hwt
    · -- the survivor would run past the rotation, leaving `|M| < |c|`
      omega

/-! ## 4.  The residual, shrunk to the empty conjugator -/

/-- **`NoDeepCollapse` at an empty head conjugator.**  Every field is quoted
verbatim from `GreendlingerCompositeWellPosed.NoDeepCollapse`, with `c = []`
added.

`noDeepCollapse_of_emptyConj` shows this is the whole of what the residual still
asks for. -/
def NoDeepCollapseEmptyConj [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c₂ t₂ : List (α × Bool))
    (e f : List (FreeGroup α × List (α × Bool)))
    (g : FreeGroup α) (P' M B' : List (α × Bool)) (i : ℕ),
    c = [] →
    IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g →
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g →
    t ∈ symmetrization R → t₂ ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c₂ t₂) →
    palindrome c t = P' ++ M →
    (conjEval e).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → (i : ℚ) < lam * (t.length : ℚ) →
    c.length + t.length < M.length + i →
    B' ≠ []

/-- **The residual is exactly the empty-conjugator corner.**  Off `c = []` the
collapse is refuted outright by `ne_nil_of_conj_ne_nil`, so a proof of the
corner is a proof of `NoDeepCollapse`. -/
theorem noDeepCollapse_of_emptyConj [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (h : NoDeepCollapseEmptyConj R lam) : NoDeepCollapse R lam := by
  intro c t c₂ t₂ e f g P' M B' i hmin hmin₂ ht ht₂ hredp hredp₂ heq htail
    hlow hi hgt
  rcases eq_or_ne c [] with hc | hc
  · exact h c t c₂ t₂ e f g P' M B' i hc hmin hmin₂ ht ht₂ hredp hredp₂ heq
      htail hlow hi hgt
  · exact ne_nil_of_conj_ne_nil hmin hredp heq htail hlow hc

/-- **The repair, measured against the shrunken residual.**
`GreendlingerCompositeWellPosed.deepCompositeLandsSharp_of_sharp'_of_noDeepCollapse`
closes the gap between `DeepCompositeLandsSharp'` and `DeepCompositeLandsSharp`
once `NoDeepCollapse` is discharged; this is the same statement with the
residual replaced by its empty-conjugator corner. -/
theorem deepCompositeLandsSharp_of_sharp'_of_emptyConj [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (h : DeepCompositeLandsSharp' R lam) (hno : NoDeepCollapseEmptyConj R lam) :
    DeepCompositeLandsSharp R lam :=
  deepCompositeLandsSharp_of_sharp'_of_noDeepCollapse h
    (noDeepCollapse_of_emptyConj hno)

end SmallCancellationRouter
end GroupApproximation
