import GroupApproximation.Sofic.GreendlingerCascade

/-!
# Landing sites compose, and confinement is one of them

`GreendlingerCascade` reduces the gate to `CascadeLanding`: at the head of a
minimal expression, either the leading factor already delivers the located
conclusion, or the block it loses stops in a later factor within a sixth of that
factor's rotation past its conjugator.  This file supplies the two things that
statement needs to be usable.

## Landing sites compose

`LandsIn.compose` is the whole arithmetic of following a block past a factor.
If the word `V` is `A₀ ++ V₂.drop N₀` --- one cascade step, `A₀` the survivor of
the factor and `N₀` the block that factor lost --- then a landing site for the
**residual** block inside `V₂` is a landing site for the original block inside
`V`, provided the block arrives at all (`N₀ ≤ b'`) and the arithmetic of the
overrun matches (`b + N₀ ≤ b' + |A₀|`).  `landsIn_of_overrun` is the case those
two conditions are designed for: the residual block is `b + N₀ - |A₀|`, which is
exactly what is left of the block once the survivor `A₀` has absorbed part of it
and the factor's own block `N₀` has been added in front.

Both are unconditional, and both are the reason the cascade is the right frame:
the block is followed one factor at a time, and each step is bookkeeping.  The
recursion terminates because the expression is one factor shorter each time,
which is what `LandsIn`'s length parameter records.

## Confinement is a landing site

`cascadeLanding_of_leadingConfinement` proves the new hypothesis from the old
one.  It replays the four cases of `GreendlingerThreeFactor`'s descent --- the
block inside the trailing conjugator, the overlap regime, the block buried in
the next conjugator, the block meeting the next rotation --- and in each case
either the leading factor delivers the conclusion outright or the tail is itself
the landing site, with nothing dropped and nothing surviving in front.

So `CascadeLanding` is a **weakening** of `LeadingConfinement`: everything that
route proves, this one proves.  What it adds is the case confinement cannot
reach, the block that outruns the next factor's survivor; there
`landsIn_of_overrun` applies and the search moves on to the factor after.  Since
`LeadingConfinement` is refuted by the configuration in
`GreendlingerThreeFactor`'s header --- where the block runs `21` letters past
what the second factor keeps, and the landing site is the third factor's
conjugator --- the implication is strict, and in the only direction that
matters.

Unconditional except where `LeadingConfinement` is named.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Composing landing sites along the cascade -/

/-- **Landing sites compose.**  A landing site inside `V₂` for the residual
block serves as a landing site inside `A₀ ++ V₂.drop N₀` for the original one.

The two side conditions are the whole content: `hstep` is the arithmetic of the
overrun --- what the block still has to travel after the survivor `A₀` has
absorbed part of it --- and `harrive` says the block reaches past the factor's
own block `N₀` at all, which is what keeps the drop inside the landing factor's
conjugator. -/
theorem LandsIn.compose [DecidableEq α] {R : Set (List (α × Bool))}
    {b b' N₀ m : ℕ} {V V₂ A₀ : List (α × Bool)}
    (h : LandsIn R b' V₂ m)
    (hV : V = A₀ ++ V₂.drop N₀)
    (hstep : b + N₀ ≤ b' + A₀.length)
    (harrive : N₀ ≤ b') :
    LandsIn R b V m := by
  obtain ⟨c', t', f, A, N, i, hf, hV₂, ht', hredp', hmin, hi, hN, hb⟩ := h
  rcases le_or_gt N₀ A.length with hle | hgt
  · refine ⟨c', t', f, A₀ ++ A.drop N₀, N, i, hf, ?_, ht', hredp', hmin, hi,
      hN, ?_⟩
    · rw [hV, hV₂, drop_append_of_le N₀ A _ hle, List.append_assoc]
    · rw [List.length_append, List.length_drop]
      omega
  · refine ⟨c', t', f, A₀, N + (N₀ - A.length), i, hf, ?_, ht', hredp', hmin,
      hi, ?_, ?_⟩
    · rw [hV, hV₂, drop_append_of_ge A N₀ _ (by omega), drop_add]
    · omega
    · omega

/-- **Following an overrunning block one factor on.**  When the block is at
least as long as what the factor in front of it keeps, the residual block is
`b + N₀ - |A₀|`, and a landing site for it serves for the block itself. -/
theorem landsIn_of_overrun [DecidableEq α] {R : Set (List (α × Bool))}
    {b N₀ m : ℕ} {V V₂ A₀ : List (α × Bool)}
    (hV : V = A₀ ++ V₂.drop N₀)
    (hover : A₀.length ≤ b)
    (h : LandsIn R (b + N₀ - A₀.length) V₂ m) :
    LandsIn R b V m :=
  h.compose hV (by omega) (by omega)

/-! ## One cascade step, with the next factor in palindromic normal form -/

/-- **The cascade step at a palindromic head.**  The reduced word of an
expression whose leading factor is the palindrome `c' t' invRev c'` is that
palindrome's survivor followed by the reduced word of the rest, with the block
the palindrome destroyed removed.

This is `exists_residual_step` with the two halves named: `P''` is what the
factor keeps, and `|M''|` is what it destroyed.  A block arriving from the left
overruns exactly when it is longer than `P''`. -/
theorem exists_tail_step [DecidableEq α]
    {c' t' : List (α × Bool)} {f : List (FreeGroup α × List (α × Bool))}
    (hredp' : FreeGroup.IsReduced (palindrome c' t')) :
    ∃ P'' M'' : List (α × Bool),
      palindrome c' t' = P'' ++ M'' ∧
        (conjEval ((FreeGroup.mk c', t') :: f)).toWord
          = P'' ++ (conjEval f).toWord.drop M''.length := by
  obtain ⟨P'', M'', B'', h1, h2, h3⟩ :=
    exists_leading_cancellation
      (w := (conjEval ((FreeGroup.mk c', t') :: f)).toWord)
      FreeGroup.isReduced_toWord hredp' (FreeGroup.mk_toWord).symm
  refine ⟨P'', M'', h1, ?_⟩
  have hdrop : (conjEval f).toWord.drop M''.length = B'' := by
    rw [h2, drop_append_of_ge (FreeGroup.invRev M'') M''.length B''
      (le_of_eq FreeGroup.invRev_length), FreeGroup.invRev_length,
      Nat.sub_self, List.drop_zero]
  rw [hdrop]
  exact h3

/-! ## Confinement is a landing site -/

/-- **The old hypothesis implies the new one.**  Every case of
`GreendlingerThreeFactor`'s descent produces either the located conclusion from
the leading factor itself or a landing site in the factor immediately next, with
nothing dropped and nothing surviving in front.

The four cases are unchanged: the block inside the trailing conjugator and the
overlap regime give the conclusion (`greendlingerAt_of_short_cancellation`,
`greendlingerAt_of_overlap`); the block buried in the next conjugator lands at
offset `0`, and the block meeting the next rotation lands at offset `|v|`, the
piece it eats there.  What is new is only that these are read as *landing
sites* rather than as inheritance steps, which is what lets the case confinement
cannot reach --- the block that outruns the next factor's survivor --- be
handled by `landsIn_of_overrun` instead of being assumed away. -/
theorem cascadeLanding_of_leadingConfinement [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hconf : LeadingConfinement R) :
    CascadeLanding R := by
  intro c t e g P' M B' j hmin ht hredp heq hgw hlong hj
  have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
  have hlongc : (FreeGroup.invRev c).length < M.length := by omega
  cases e with
  | nil =>
      exfalso
      have hnil : (conjEval ([] : List (FreeGroup α × List (α × Bool)))).toWord
          = [] := by
        rw [conjEval_nil]
        exact FreeGroup.toWord_eq_nil_iff.mpr rfl
      rw [hnil] at hgw
      have hz := congrArg List.length hgw.symm
      rw [List.length_append, FreeGroup.invRev_length, List.length_nil] at hz
      omega
  | cons x e'' =>
      obtain ⟨x', s'⟩ := x
      obtain ⟨c', t', ht', hredp', hmin₂⟩ := exists_palindromic_snd hR hRne hmin
      have htail : conjEval ((FreeGroup.mk c', t') :: e'')
          = conjEval ((x', s') :: e'') := by
        have h1 := hmin₂.2.1
        have h2 := hmin.2.1
        rw [conjEval_cons] at h1 h2
        exact mul_left_cancel (h1.trans h2.symm)
      rw [← htail] at hgw ⊢
      have ht'pos : 0 < t'.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht')
      have htpos : 0 < t.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht)
      have hredc : FreeGroup.IsReduced c :=
        isReduced_of_infix ⟨[], t ++ FreeGroup.invRev c, by simp [palindrome]⟩
          hredp
      have hredc' : FreeGroup.IsReduced c' :=
        isReduced_of_infix ⟨[], t' ++ FreeGroup.invRev c', by simp [palindrome]⟩
          hredp'
      have hpre : FreeGroup.invRev M
          <+: (conjEval ((FreeGroup.mk c', t') :: e'')).toWord := ⟨B', hgw.symm⟩
      have hconfp : FreeGroup.invRev M <+: palindrome c' t' :=
        hconf c t c' t' P' M e'' g hmin₂ heq hpre (by omega)
      obtain ⟨B'', heq'⟩ := hconfp
      have hhigh : M.length ≤ c.length + t.length :=
        swallow_bound_of_minimal hRne hmetric hmin₂ ht ht' hredp hredp' heq
          heq'.symm
      have hb2 : M.length ≤ c'.length + t'.length :=
        swallow_bound_of_minimal' hRne hmetric hmin₂.leadingPair ht ht' hredp
          hredp' heq heq'.symm
      have hcoin := mk_palindrome_mul_ne_one_of_minimal hmin₂
      have hminf : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: e'')
          (conjEval ((FreeGroup.mk c', t') :: e'')) := hmin₂.tail
      have hshorter : e''.length < ((x', s') :: e'').length := by
        simp only [List.length_cons]
        omega
      rcases le_or_gt c'.length c.length with hle | hgt
      · exact Or.inl (greendlingerAt_of_overlap hmetric ht ht' heq ⟨B'', heq'⟩
          (by omega) hle (by omega) hcoin hj)
      · obtain ⟨E, hM, hEct⟩ := eaten_split ⟨P', heq.symm⟩ hlongc.le
        have hEt : E <:+ t := eaten_suffix_of_le hM hEct (by omega)
        have hElen : M.length = E.length + c.length := by
          rw [hM, List.length_append, FreeGroup.invRev_length]
        have hinvM : FreeGroup.invRev M = c ++ FreeGroup.invRev E :=
          invRev_eaten_block hM
        have hEpre : c ++ FreeGroup.invRev E <+: palindrome c' t' := by
          rw [← hinvM]
          exact ⟨B'', heq'⟩
        have hP2 : palindrome c' t' = c' ++ (t' ++ FreeGroup.invRev c') := by
          unfold palindrome
          rw [List.append_assoc]
        have hc'pre : c' <+: palindrome c' t' := by
          rw [hP2]
          exact ⟨t' ++ FreeGroup.invRev c', rfl⟩
        have hcpre : c <+: palindrome c' t' :=
          (show c <+: c ++ FreeGroup.invRev E from ⟨_, rfl⟩).trans hEpre
        obtain ⟨y, hy⟩ := List.prefix_of_prefix_length_le hcpre hc'pre hgt.le
        have hylen : c'.length = c.length + y.length := by
          rw [← hy, List.length_append]
        rcases le_or_gt M.length c'.length with hin | hout
        · -- the block's image is buried in the second conjugator
          obtain ⟨Z, hZ⟩ := List.prefix_of_prefix_length_le
            (show FreeGroup.invRev M <+: palindrome c' t' from ⟨B'', heq'⟩)
            hc'pre (by rw [FreeGroup.invRev_length]; omega)
          have hc'eq : c' = c ++ (FreeGroup.invRev E ++ Z) := by
            rw [← hZ, hinvM, List.append_assoc]
          obtain ⟨t₀, ht₀⟩ := hEt
          have htlen : t₀.length + E.length = t.length := by
            rw [← ht₀, List.length_append]
          have hreroute : E.length ≤ t₀.length := by
            refine eaten_le_of_minimal_reroute (R := R) (c := c) (t₀ := t₀)
              (E := E) (Z := Z) (m := t') (e := e'') (g := g) ?_ ?_ hredc
            · rw [ht₀, ← hc'eq]
              exact hmin₂
            · rw [← hc'eq]
              exact hredc'
          exact Or.inr ⟨by omega,
            landsIn_of_confined (i := 0) ht' hredp' hminf (by omega) (by omega)
              hshorter⟩
        · -- the block reaches past the second conjugator, meeting its rotation
          have hEstep : FreeGroup.invRev E
              <+: y ++ (t' ++ FreeGroup.invRev c') := by
            refine (List.prefix_append_right_inj c).mp ?_
            rw [← List.append_assoc, hy, ← hP2]
            exact hEpre
          have hEinvlen : (FreeGroup.invRev E).length = E.length :=
            FreeGroup.invRev_length
          have hyE : y <+: FreeGroup.invRev E := by
            refine List.prefix_of_prefix_length_le
              (show y <+: y ++ (t' ++ FreeGroup.invRev c') from ⟨_, rfl⟩)
              hEstep ?_
            omega
          obtain ⟨v, hv⟩ := hyE
          have hvlen : y.length + v.length = E.length := by
            have hb := congrArg List.length hv
            rw [List.length_append, FreeGroup.invRev_length] at hb
            omega
          have hvstep : v <+: t' ++ FreeGroup.invRev c' := by
            refine (List.prefix_append_right_inj y).mp ?_
            rw [hv]
            exact hEstep
          have hvt' : v <+: t' :=
            List.prefix_of_prefix_length_le hvstep
              (show t' <+: t' ++ FreeGroup.invRev c' from ⟨_, rfl⟩) (by omega)
          have hyvinv : y ++ v <+: FreeGroup.invRev t := by
            rw [hv]
            exact invRev_prefix_of_suffix hEt
          obtain ⟨z, hz⟩ := hyvinv
          have hzlen : y.length + v.length + z.length = t.length := by
            have hb := congrArg List.length hz
            rw [List.length_append, List.length_append,
              FreeGroup.invRev_length] at hb
            omega
          have hvrot : v <+: (FreeGroup.invRev t).rotate y.length :=
            prefix_rotate_of_append_prefix ⟨z, hz⟩
          have hypre : y <+: FreeGroup.invRev t :=
            (show y <+: y ++ v from ⟨v, rfl⟩).trans ⟨z, hz⟩
          have hrotmem : (FreeGroup.invRev t).rotate y.length
              ∈ symmetrization R :=
            rotate_mem_symmetrization (invRev_mem_symmetrization ht) y.length
          by_cases hsame : t' = (FreeGroup.invRev t).rotate y.length
          · exact absurd
              (mk_palindrome_mul_eq_one_of_coincidence' hy.symm hypre hsame)
              hcoin
          · have hpiece : IsPiece (symmetrization R) v :=
              isPiece_of_prefix_two ht' hrotmem hsame hvt' hvrot
            have h6t' := six_mul_length_lt_of_isPiece hmetric hpiece ht' hvt'
            have h6t := six_mul_length_lt_of_isPiece hmetric hpiece hrotmem hvrot
            rw [List.length_rotate, FreeGroup.invRev_length] at h6t
            obtain ⟨u, hu⟩ := hvt'
            have htinv : FreeGroup.invRev (y ++ (v ++ z)) = t := by
              rw [← List.append_assoc, hz, FreeGroup.invRev_invRev]
            have hmeet : y.length ≤ z.length := by
              refine overhang_le_of_minimal_reroute_meet (R := R) (c := c)
                (y := y) (v := v) (z := z) (u := u) (e := e'') (g := g) ?_ ?_
              · rw [htinv, hu, hy]
                exact hmin₂
              · rw [hy]
                exact hredc'
            exact Or.inr ⟨by omega,
              landsIn_of_confined (i := v.length) ht' hredp' hminf (by omega)
                (by omega) hshorter⟩

/-! ## The gate, along the old route -/

/-- **The cascade route subsumes the confinement route.**  Anything
`GreendlingerThreeFactor.greendlingerConclusion_of_leadingConfinement` proves,
`GreendlingerCascade.greendlingerConclusion_of_cascadeLanding` proves --- and the
latter's hypothesis survives the configuration that refutes the former's. -/
theorem greendlingerConclusion_of_leadingConfinement' [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    (hconf : LeadingConfinement R) :
    GreendlingerConclusion R :=
  greendlingerConclusion_of_cascadeLanding hR hRne
    (cascadeLanding_of_leadingConfinement hR hRne hmetric hconf)

end SmallCancellationRouter
end GroupApproximation
