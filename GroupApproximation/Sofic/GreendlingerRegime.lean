import GroupApproximation.Sofic.GreendlingerWeight

/-!
# The destroyed block never swallows a rotation

`GreendlingerMinimal` left the two-factor descent asking for one thing:
`TwoFactorRegime`, that the block the product destroys does not swallow either
rotation whole.  This file discharges it, and with it the two-factor case of the
gate becomes unconditional.

## Why the factor count cannot do it

Minimality of the number of factors says only that no two adjacent factors
cancel.  Swallowing a rotation is not a cancellation of factors --- the two
factors' product is perfectly nontrivial --- so the count has nothing to say.
What the configuration *does* admit is a re-expression with the same number of
factors and a strictly shorter total conjugator length, and that is what
minimality of the weight forbids.

## The six ways it can fail, and what kills each

Suppose the block swallows the first rotation: it eats the trailing conjugator,
all of `t`, and a nonempty suffix `c₂` of the leading conjugator
(`exists_swallow_split`).  Then the matching prefix of the second palindrome is
`c ++ invRev t ++ invRev c₂`, and the two conjugators are comparable because
both are prefixes of that palindrome.  Six cases:

* the whole `invRev t` lands inside the second conjugator --- **absorb**, saving
  `|t|`;
* the second conjugator is the shorter, and
  - the whole `t'` lands inside the first conjugator --- **absorb**, saving
    `|t'|`;
  - `t'` reaches into `invRev t`, meeting it in `p` --- **slide**, saving
    `|q| - 2|p|`, and `C'(1/6)` makes `|q| > 5|p|`;
  - `t'` covers `invRev t` --- then `invRev t` is a piece of itself, which
    `C'(1/6)` forbids outright;
* the second conjugator is the longer, and
  - `t'` meets `invRev t` in `v` --- **meet**, saving `|y| - |v|`, and
    `C'(1/6)` makes `|y| > 5|v|`;
  - `invRev t` covers `t'` --- then `t'` is a piece of itself.

Every branch that is not a weight contradiction ends at a *coincidence*: the two
rotations are the same symmetrized relator at the same position, and then the
two factors are mutually inverse, which the factor count forbids.  So both
minimalities are spent, each on exactly the cases the other cannot reach.

The second bound --- that the block does not swallow `t'` either --- is the same
statement read backwards, and `GreendlingerMirror`'s duality supplies it.

Depends on `C'(1/6)`; everything else is unconditional.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The shape of a swallowing block -/

/-- **A block that swallows the rotation** eats the trailing conjugator, all of
the rotation, and a nonempty suffix of the leading conjugator.  Its inverse is
therefore the leading conjugator followed by the inverted rotation and the
inverse of that suffix. -/
theorem exists_swallow_split {c t P' M : List (α × Bool)}
    (heq : palindrome c t = P' ++ M)
    (hlong : c.length + t.length < M.length) :
    ∃ c₁ c₂ : List (α × Bool), c = c₁ ++ c₂ ∧ c₂ ≠ [] ∧
      M = c₂ ++ t ++ FreeGroup.invRev c ∧
      FreeGroup.invRev M
        = c ++ (FreeGroup.invRev t ++ FreeGroup.invRev c₂) := by
  have hcl : (FreeGroup.invRev c).length = c.length := FreeGroup.invRev_length
  have hMsuf : M <:+ (c ++ t) ++ FreeGroup.invRev c := by
    have h : M <:+ palindrome c t := ⟨P', heq.symm⟩
    unfold palindrome at h
    exact h
  obtain ⟨E, hM, hEsuf⟩ := suffix_split_of_length_le hMsuf (by omega)
  have hElen : E.length + c.length = M.length := by
    have hb := congrArg List.length hM
    rw [List.length_append] at hb
    omega
  obtain ⟨c₂, hE, hc₂suf⟩ := suffix_split_of_length_le hEsuf (by omega)
  have hc₂len : c₂.length + t.length = E.length := by
    have hb := congrArg List.length hE
    rw [List.length_append] at hb
    omega
  obtain ⟨c₁, hc₁⟩ := hc₂suf
  refine ⟨c₁, c₂, hc₁.symm, ?_, ?_, ?_⟩
  · intro hnil
    rw [hnil, List.length_nil] at hc₂len
    omega
  · rw [hM, hE]
  · rw [hM, hE, FreeGroup.invRev_append, FreeGroup.invRev_invRev,
      FreeGroup.invRev_append]

/-! ## The two leading factors do not cancel -/

/-- In a minimal expression the two leading factors, in palindromic form, do not
cancel: that is the factor count spent, transported to the palindromes. -/
theorem mk_palindrome_mul_ne_one_of_minimal [DecidableEq α]
    {R : Set (List (α × Bool))} {c t c' t' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g) :
    FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome c' t') ≠ 1 := by
  obtain ⟨-, h2⟩ := conjValid_cons_iff.mp hmin.1
  obtain ⟨-, h4⟩ := conjValid_cons_iff.mp h2
  have hg : g = FreeGroup.mk (palindrome c t)
      * (FreeGroup.mk (palindrome c' t') * conjEval e) := by
    rw [← hmin.2.1, conjEval_cons, conjEval_cons, mk_palindrome, mk_palindrome]
  have hce : IsConjProduct R e.length (conjEval e) :=
    (isConjProduct_iff_exists_conjExpr e.length (conjEval e)).mpr ⟨e, h4, rfl, rfl⟩
  have hcount : IsMinimalConjProduct R (e.length + 1 + 1) g :=
    isMinimalConjProduct_of_isMinimalConjExpr hmin
  exact mk_palindrome_mul_ne_one hcount hg hce

/-! ## The bound -/

/-- **The destroyed block never swallows the first rotation.**  Every way it
could is either a re-expression with strictly shorter total conjugator length,
which weight-minimality forbids, or a relator that is a piece of itself, which
`C'(1/6)` forbids, or a coincidence of the two rotations, which makes the two
factors mutually inverse and so is forbidden by the factor count. -/
theorem swallow_bound_of_minimal [DecidableEq α] {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    {c t c' t' P' M B' : List (α × Bool)}
    {e : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: e) g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B') :
    M.length ≤ c.length + t.length := by
  by_contra hcon
  push Not at hcon
  -- the two rotations are nonempty
  have htne : t ≠ [] := ne_nil_of_mem_symmetrization hRne ht
  have ht'ne : t' ≠ [] := ne_nil_of_mem_symmetrization hRne ht'
  have htpos : 0 < t.length := List.length_pos_iff.mpr htne
  have ht'pos : 0 < t'.length := List.length_pos_iff.mpr ht'ne
  -- the two conjugators are reduced
  have hredc : FreeGroup.IsReduced c :=
    isReduced_of_infix ⟨[], t ++ FreeGroup.invRev c, by simp [palindrome]⟩ hredp
  have hredc' : FreeGroup.IsReduced c' :=
    isReduced_of_infix ⟨[], t' ++ FreeGroup.invRev c', by simp [palindrome]⟩ hredp'
  -- the two factors do not cancel
  have hcoin := mk_palindrome_mul_ne_one_of_minimal hmin
  -- the swallowing shape
  obtain ⟨_c₁, c₂, _hc, _hc₂ne, _hM, hinvM⟩ := exists_swallow_split heq hcon
  have hP2 : palindrome c' t' = c' ++ (t' ++ FreeGroup.invRev c') := by
    unfold palindrome
    rw [List.append_assoc]
  have hpre : c ++ (FreeGroup.invRev t ++ FreeGroup.invRev c₂)
      <+: palindrome c' t' := by
    rw [← hinvM]
    exact ⟨B', heq'.symm⟩
  have hpre2 : (c ++ FreeGroup.invRev t) ++ FreeGroup.invRev c₂
      <+: palindrome c' t' := by
    rw [List.append_assoc]
    exact hpre
  have hcpre : c <+: palindrome c' t' :=
    (show c <+: c ++ (FreeGroup.invRev t ++ FreeGroup.invRev c₂) from
      ⟨_, rfl⟩).trans hpre
  have hctpre : c ++ FreeGroup.invRev t <+: palindrome c' t' :=
    (show c ++ FreeGroup.invRev t
      <+: (c ++ FreeGroup.invRev t) ++ FreeGroup.invRev c₂ from
      ⟨_, rfl⟩).trans hpre2
  have hc'pre : c' <+: palindrome c' t' := by
    rw [hP2]
    exact ⟨t' ++ FreeGroup.invRev c', rfl⟩
  have hc't'pre : c' ++ t' <+: palindrome c' t' := ⟨FreeGroup.invRev c', rfl⟩
  have hctlen : (c ++ FreeGroup.invRev t).length = c.length + t.length := by
    rw [List.length_append, FreeGroup.invRev_length]
  have hc't'len : (c' ++ t').length = c'.length + t'.length := List.length_append
  rcases le_or_gt (c.length + t.length) c'.length with hA | hA
  · -- the whole inverted rotation sits inside the second conjugator
    obtain ⟨Z, hZ⟩ := List.prefix_of_prefix_length_le hctpre hc'pre (by omega)
    have hc'eq : c' = c ++ (FreeGroup.invRev t ++ Z) := by
      rw [← hZ, List.append_assoc]
    rw [hc'eq] at hmin hredc'
    exact not_absorb_inv_of_minimal hmin hredc' htne
  · rcases le_or_gt c'.length c.length with hB | hC
    · -- the second conjugator is the shorter one
      obtain ⟨q, hq⟩ := List.prefix_of_prefix_length_le hc'pre hcpre hB
      have hcq : c = c' ++ q := hq.symm
      have hclen : c.length = c'.length + q.length := by
        rw [hcq, List.length_append]
      rcases le_or_gt (c'.length + t'.length) c.length with hB1 | hB23
      · -- the whole second rotation sits inside the first conjugator
        obtain ⟨q'', hq''⟩ :=
          List.prefix_of_prefix_length_le hc't'pre hcpre (by omega)
        have hceq : c = c' ++ (t' ++ q'') := by
          rw [← hq'', List.append_assoc]
        rw [hceq] at hmin hredc
        exact not_absorb_of_minimal hmin hredc ht'ne
      · rcases le_or_gt (c'.length + t'.length) (c.length + t.length) with hB2 | hB3
        · -- the two rotations meet in a piece
          obtain ⟨W, hW⟩ :=
            List.prefix_of_prefix_length_le hc't'pre hctpre (by omega)
          have hcancel : t' ++ W = q ++ FreeGroup.invRev t := by
            have hb : c' ++ (t' ++ W) = c' ++ (q ++ FreeGroup.invRev t) := by
              rw [← List.append_assoc, hW, hcq, List.append_assoc]
            exact List.append_cancel_left hb
          have hq1 : q <+: q ++ FreeGroup.invRev t := ⟨_, rfl⟩
          have hq2 : t' <+: q ++ FreeGroup.invRev t := by
            rw [← hcancel]
            exact ⟨W, rfl⟩
          obtain ⟨p, hp⟩ := List.prefix_of_prefix_length_le hq1 hq2 (by omega)
          have hplen : q.length + p.length = t'.length := by
            have hb := congrArg List.length hp
            rw [List.length_append] at hb
            omega
          have hppos : 0 < p.length := by omega
          have hpW : p ++ W = FreeGroup.invRev t := by
            have hb : q ++ (p ++ W) = q ++ FreeGroup.invRev t := by
              rw [← List.append_assoc, hp, hcancel]
            exact List.append_cancel_left hb
          have hpt : p <+: FreeGroup.invRev t := ⟨W, hpW⟩
          have hqt' : q <+: t' := ⟨p, hp⟩
          by_cases hsame : FreeGroup.invRev t = t'.rotate q.length
          · exact hcoin (mk_palindrome_mul_eq_one_of_coincidence hcq hqt' hsame)
          · -- the overlap is a piece, and the slide move bounds the overhang
            have hrot' : t'.rotate q.length = p ++ q := by
              rw [← hp, rotate_append]
            have hprot : p <+: t'.rotate q.length := by
              rw [hrot']
              exact ⟨q, rfl⟩
            have hpiece : IsPiece (symmetrization R) p :=
              isPiece_of_prefix_two (invRev_mem_symmetrization ht)
                (rotate_mem_symmetrization ht' q.length) hsame hpt hprot
            have hsix := six_mul_length_lt_of_isPiece hmetric hpiece
              (rotate_mem_symmetrization ht' q.length) hprot
            rw [List.length_rotate] at hsix
            have ht_eq : t = FreeGroup.invRev W ++ FreeGroup.invRev p := by
              have hb := congrArg FreeGroup.invRev hpW
              rw [FreeGroup.invRev_invRev, FreeGroup.invRev_append] at hb
              exact hb.symm
            rw [hcq, ht_eq, ← hp] at hmin
            rw [hcq] at hredc
            have hover := overhang_le_of_minimal hmin hredc
            omega
        · -- the second rotation covers the whole inverted first rotation
          have hstep : q ++ FreeGroup.invRev t <+: t' := by
            refine (List.prefix_append_right_inj c').mp ?_
            rw [← List.append_assoc, ← hcq]
            exact List.prefix_of_prefix_length_le hctpre hc't'pre (by omega)
          have hqt' : q <+: t' :=
            (show q <+: q ++ FreeGroup.invRev t from ⟨_, rfl⟩).trans hstep
          have hinvpre : FreeGroup.invRev t <+: t'.rotate q.length :=
            prefix_rotate_of_append_prefix hstep
          by_cases hsame : FreeGroup.invRev t = t'.rotate q.length
          · exact hcoin (mk_palindrome_mul_eq_one_of_coincidence hcq hqt' hsame)
          · have hpiece : IsPiece (symmetrization R) (FreeGroup.invRev t) :=
              isPiece_of_prefix_two (invRev_mem_symmetrization ht)
                (rotate_mem_symmetrization ht' q.length) hsame
                (List.prefix_refl _) hinvpre
            have hsix := six_mul_length_lt_of_isPiece hmetric hpiece
              (invRev_mem_symmetrization ht) (List.prefix_refl _)
            rw [FreeGroup.invRev_length] at hsix
            omega
    · -- the second conjugator is the longer one
      obtain ⟨y, hy⟩ := List.prefix_of_prefix_length_le hcpre hc'pre (by omega)
      have hc'y : c' = c ++ y := hy.symm
      have hylen : c'.length = c.length + y.length := by
        rw [hc'y, List.length_append]
      have hP2' : palindrome c' t' = c ++ (y ++ (t' ++ FreeGroup.invRev c')) := by
        rw [hP2, hc'y, List.append_assoc]
      have hstep : FreeGroup.invRev t ++ FreeGroup.invRev c₂
          <+: y ++ (t' ++ FreeGroup.invRev c') := by
        refine (List.prefix_append_right_inj c).mp ?_
        rw [← hP2']
        exact hpre
      have hinvpre : FreeGroup.invRev t
          <+: y ++ (t' ++ FreeGroup.invRev c') :=
        (show FreeGroup.invRev t
          <+: FreeGroup.invRev t ++ FreeGroup.invRev c₂ from ⟨_, rfl⟩).trans hstep
      have hyinv : y <+: FreeGroup.invRev t := by
        refine List.prefix_of_prefix_length_le
          (show y <+: y ++ (t' ++ FreeGroup.invRev c') from ⟨_, rfl⟩) hinvpre ?_
        rw [FreeGroup.invRev_length]
        omega
      obtain ⟨v, hv⟩ := hyinv
      have hvlen : y.length + v.length = t.length := by
        have hb := congrArg List.length hv
        rw [List.length_append, FreeGroup.invRev_length] at hb
        omega
      have hvpos : 0 < v.length := by omega
      have hvstep : v ++ FreeGroup.invRev c₂ <+: t' ++ FreeGroup.invRev c' := by
        refine (List.prefix_append_right_inj y).mp ?_
        rw [← List.append_assoc, hv]
        exact hstep
      have hvpre : v <+: t' ++ FreeGroup.invRev c' :=
        (show v <+: v ++ FreeGroup.invRev c₂ from ⟨_, rfl⟩).trans hvstep
      have hvrot : v <+: (FreeGroup.invRev t).rotate y.length := by
        rw [← hv, rotate_append]
        exact ⟨y, rfl⟩
      have hrotmem : (FreeGroup.invRev t).rotate y.length ∈ symmetrization R :=
        rotate_mem_symmetrization (invRev_mem_symmetrization ht) y.length
      by_cases hsame : t' = (FreeGroup.invRev t).rotate y.length
      · exact hcoin (mk_palindrome_mul_eq_one_of_coincidence' hc'y ⟨v, hv⟩ hsame)
      · rcases le_or_gt v.length t'.length with hC1 | hC2
        · -- the two rotations meet in a piece; the meet move bounds the overhang
          obtain ⟨u, hu⟩ := List.prefix_of_prefix_length_le hvpre
            (show t' <+: t' ++ FreeGroup.invRev c' from ⟨_, rfl⟩) hC1
          have hpiece : IsPiece (symmetrization R) v :=
            isPiece_of_prefix_two ht' hrotmem hsame ⟨u, hu⟩ hvrot
          have hsix := six_mul_length_lt_of_isPiece hmetric hpiece hrotmem hvrot
          rw [List.length_rotate, FreeGroup.invRev_length] at hsix
          have ht_eq : t = FreeGroup.invRev v ++ FreeGroup.invRev y := by
            have hb := congrArg FreeGroup.invRev hv
            rw [FreeGroup.invRev_invRev, FreeGroup.invRev_append] at hb
            exact hb.symm
          rw [hc'y, ht_eq, ← hu] at hmin
          rw [hc'y] at hredc'
          have hover := overhang_le_of_minimal_meet hmin hredc'
          omega
        · -- the inverted first rotation covers the whole second rotation
          have ht'v : t' <+: v :=
            List.prefix_of_prefix_length_le
              (show t' <+: t' ++ FreeGroup.invRev c' from ⟨_, rfl⟩) hvpre
              (by omega)
          have ht'rot : t' <+: (FreeGroup.invRev t).rotate y.length :=
            ht'v.trans hvrot
          have hpiece : IsPiece (symmetrization R) t' :=
            isPiece_of_prefix_two ht' hrotmem hsame (List.prefix_refl _) ht'rot
          have hsix := six_mul_length_lt_of_isPiece hmetric hpiece ht'
            (List.prefix_refl _)
          omega

/-! ## The mirrored bound, and the case closed -/

/-- **The block does not swallow the second rotation either.**  This is the same
statement read backwards: `conjInv` inverts the expression, which exchanges the
two factors and inverts their rotations, and minimality is inherited. -/
theorem swallow_bound_of_minimal' [DecidableEq α] {R : Set (List (α × Bool))}
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    {c t c' t' P' M B' : List (α × Bool)} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R [(FreeGroup.mk c, t), (FreeGroup.mk c', t')] g)
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp' : FreeGroup.IsReduced (palindrome c' t'))
    (heq : palindrome c t = P' ++ M)
    (heq' : palindrome c' t' = FreeGroup.invRev M ++ B') :
    M.length ≤ c'.length + t'.length := by
  have hinv := isMinimalConjExpr_conjInv hmin
  have hlist : conjInv [(FreeGroup.mk c, t), (FreeGroup.mk c', t')]
      = [(FreeGroup.mk c', FreeGroup.invRev t'),
        (FreeGroup.mk c, FreeGroup.invRev t)] := by
    simp [conjInv]
  rw [hlist] at hinv
  have hm1 : palindrome c' (FreeGroup.invRev t')
      = FreeGroup.invRev B' ++ M := by
    rw [← invRev_palindrome, heq', FreeGroup.invRev_append,
      FreeGroup.invRev_invRev]
  have hm2 : palindrome c (FreeGroup.invRev t)
      = FreeGroup.invRev M ++ FreeGroup.invRev P' := by
    rw [← invRev_palindrome, heq, FreeGroup.invRev_append]
  have hred1 : FreeGroup.IsReduced (palindrome c' (FreeGroup.invRev t')) := by
    rw [← invRev_palindrome]
    exact isReduced_invRev_iff.mpr hredp'
  have hred2 : FreeGroup.IsReduced (palindrome c (FreeGroup.invRev t)) := by
    rw [← invRev_palindrome]
    exact isReduced_invRev_iff.mpr hredp
  have hb := swallow_bound_of_minimal hRne hmetric hinv
    (invRev_mem_symmetrization ht') (invRev_mem_symmetrization ht) hred1 hred2
    hm1 hm2
  rwa [FreeGroup.invRev_length] at hb

/-- **The two-factor case of the gate, unconditionally.**  A shortest expression
of least total conjugator length with two factors gives the Greendlinger
conclusion: what the descent used to ask for --- that the destroyed block leave
both rotations partly standing --- is now a theorem, proved from the two
minimalities and `C'(1/6)` alone. -/
theorem greendlinger_of_isMinimalConjExpr_two [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w)
    {x x' : FreeGroup α} {s s' : List (α × Bool)}
    (hmin : IsMinimalConjExpr R [(x, s), (x', s')] (FreeGroup.mk w)) :
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: r ∧ r.length < 2 * u.length := by
  obtain ⟨c, t, c', t', ht, ht', hredp, hredp', hmin2⟩ :=
    exists_palindromic_isMinimalConjExpr hR hRne hmin
  have hval : FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome c' t')
      = FreeGroup.mk w := by
    have hb := hmin2.2.1
    rw [conjEval_cons, conjEval_cons, conjEval_nil, mul_one] at hb
    rw [mk_palindrome, mk_palindrome]
    exact hb
  obtain ⟨P', M, B', h1, h2, h3, h4⟩ :=
    exists_cancellation_decomposition (palindrome c' t') hredp'
      (palindrome c t) hredp
  have hwe : w = P' ++ B' := by
    have h5 : FreeGroup.mk w = FreeGroup.mk (P' ++ B') := by
      rw [← hval, h4]
    have h6 := FreeGroup.reduce.sound h5
    rwa [hw.reduce_eq, h3.reduce_eq] at h6
  have hcoin := mk_palindrome_mul_ne_one_of_minimal hmin2
  have hb1 := swallow_bound_of_minimal hRne hmetric hmin2 ht ht' hredp hredp' h1 h2
  have hb2 := swallow_bound_of_minimal' hRne hmetric hmin2 ht ht' hredp hredp' h1 h2
  have hpre : FreeGroup.invRev M <+: palindrome c' t' := by
    rw [h2]
    exact ⟨B', rfl⟩
  rw [hwe]
  rcases regime_cases hb1 hb2 with ⟨hhigh, hle, hfit⟩ | ⟨hhigh, hle, hfit⟩
  · exact greendlinger_of_two_palindromes hRne hmetric ht ht' h1 hpre hhigh hle
      hfit hcoin
  · exact greendlinger_of_two_palindromes_mirror hRne hmetric ht ht' h1 h2 hhigh
      hle hfit hcoin

/-- **The gate for everything the two-factor descent reaches.**  A nonempty
reduced word in the normal closure whose expressions can be taken with at most
two factors contains more than half of a symmetrized relator.  No hypothesis is
left over: `n = 0` is impossible, `n = 1` is the one-relator case, and `n = 2`
is the descent just closed. -/
theorem greendlinger_of_le_two_factors [DecidableEq α]
    {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hmetric : MetricSmallCancellation R (1 / 6))
    {w : List (α × Bool)} (hw : FreeGroup.IsReduced w) (hwne : w ≠ [])
    {n : ℕ} (hn : n ≤ 2) (hcount : IsConjProduct R n (FreeGroup.mk w)) :
    ∃ r ∈ symmetrization R, ∃ u : List (α × Bool),
      u <:+: w ∧ u <+: r ∧ r.length < 2 * u.length := by
  obtain ⟨e₀, hv₀, hlen₀, he₀⟩ :=
    (isConjProduct_iff_exists_conjExpr n (FreeGroup.mk w)).mp hcount
  obtain ⟨e, hmin⟩ := exists_isMinimalConjExpr ⟨e₀, hv₀, he₀⟩
  have hlen : e.length ≤ 2 := by
    have hb := hmin.2.2.1 e₀ hv₀ he₀
    omega
  rcases e with _ | ⟨x, e₁⟩
  · exfalso
    have hb := hmin.2.1
    rw [conjEval_nil] at hb
    have h1 : FreeGroup.mk w = FreeGroup.mk ([] : List (α × Bool)) := by
      rw [← FreeGroup.one_eq_mk]
      exact hb.symm
    have h2 := FreeGroup.reduce.sound h1
    rw [hw.reduce_eq, FreeGroup.IsReduced.nil.reduce_eq] at h2
    exact hwne h2
  · rcases e₁ with _ | ⟨y, e₂⟩
    · obtain ⟨x₁, sx⟩ := x
      obtain ⟨hs, -⟩ := conjValid_cons_iff.mp hmin.1
      have hone : IsConjProduct R 1 (FreeGroup.mk w) := by
        refine ⟨x₁, sx, hs, 1, rfl, ?_⟩
        have hb := hmin.2.1
        rw [conjEval_cons, conjEval_nil, mul_one] at hb
        rw [mul_one]
        exact hb.symm
      exact greendlinger_of_isConjProduct_one hR hRne hw hone
    · rcases e₂ with _ | ⟨z, e₃⟩
      · obtain ⟨x₁, sx⟩ := x
        obtain ⟨x₂, sy⟩ := y
        exact greendlinger_of_isMinimalConjExpr_two hR hRne hmetric hw hmin
      · exfalso
        simp only [List.length_cons] at hlen
        omega

end SmallCancellationRouter
end GroupApproximation
