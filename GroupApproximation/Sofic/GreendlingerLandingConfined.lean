import GroupApproximation.Sofic.GreendlingerLandingProd
import GroupApproximation.Sofic.GreendlingerDeepVacuitySharp

/-!
# The confined configurations of `LargeSegmentLands`, discharged

`GreendlingerLandingProd` reduces the (β) side of the sharp gate to
`LargeSegmentLands`: a head that has already lost at least `λ` of its rotation
must land.  Its §11 records that three of the four configurations such a head
can be in are decided by existing machinery, and that only the non-confined one
— where the block image runs past what the next factor keeps — is genuinely
open.  This file writes that out.

## The split

Normalize the second factor with `GreendlingerThreeFactor.exists_palindromic_snd`
and ask whether the block image `invRev M` stays inside `palindrome c' t'`.

* **Not confined** — handed to `NonConfinedBlockLands`, the one open predicate,
  which is `LargeSegmentLands` with the second factor normalized and the
  confinement explicitly denied.  Nothing else is asked of it.
* **Confined**, and the head conjugator is the longer one (`|c'| ≤ |c|`) — this
  configuration **cannot occur** under `LargeSegmentLands`' own hypothesis.  The
  overlap the block eats out of the head rotation is a piece
  (`GreendlingerOverlap.isPiece_of_overlap`, with the coincidence excluded by
  `GreendlingerRegime.mk_palindrome_mul_ne_one_of_minimal`), so it is shorter
  than `λ·|t|`, and the segment `E` is shorter still — contradicting
  `λ·|t| ≤ |E|`.  This is the case that the disjunctive target hands to the head
  factor instead, and it is why the residual could be restricted to large
  segments at all.
* **Confined**, the next conjugator is longer, and the block stops inside it —
  the *buried* case.  `landsInSharp_of_confined` at offset `0`.
* **Confined**, the next conjugator is longer, and the block reaches the next
  rotation — the *meeting* case.  The meeting segment `v` is a piece against
  `t'` and against the rotated inverted head rotation, so it is under `λ` of
  `t'`, and `GreendlingerLandingProd.meet_length_split` says the block ends
  exactly `|v|` letters in: `landsInSharp_of_confined` at offset `|v|`.

## Where the constant is spent

Twice, and differently.  `0 < λ` makes the zero offset admissible in the buried
case, through `GreendlingerLandingProd.cast_zero_lt_lam_mul`.  `λ ≤ 1/6` is
needed only to reach `GreendlingerRegime.swallow_bound_of_minimal'`, which is
stated at the half constant; `GreendlingerDeepVacuitySharp.metricSmallCancellation_of_le`
converts, and the bound it yields (`|M| ≤ |c'| + |t'|`) is used in the first and
third configurations to keep the block inside the next rotation.  The meeting
case's own piece bound is read at `λ` directly and needs no conversion.

Separate module so that a failure here cannot take `GreendlingerLandingProd`
with it.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The one open configuration -/

/-- **OPEN — the block that outruns the next factor.**  `LargeSegmentLands`
restricted to the configuration where the block image does not stay inside the
next factor's palindrome, with that factor already in palindromic normal form.

This is the whole of what `largeSegmentLands_of_nonConfined` leaves open, and it
is the case `GreendlingerThreeFactor.LeadingConfinement` asserted away — the
configuration in that file's header, where the block runs `21` letters past what
the second factor keeps, is exactly an instance of it.  So the predicate is not
a restatement of a refuted hypothesis: it asks what happens *in* that
configuration rather than asserting it away. -/
def NonConfinedBlockLands [DecidableEq α] (R : Set (List (α × Bool)))
    (lam : ℚ) : Prop :=
  ∀ (c t c' t' E M P' B' : List (α × Bool))
    (f : List (FreeGroup α × List (α × Bool))) (g : FreeGroup α),
    IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c', t') :: f) g →
    t ∈ symmetrization R → t' ∈ symmetrization R →
    FreeGroup.IsReduced (palindrome c t) →
    FreeGroup.IsReduced (palindrome c' t') →
    palindrome c t = P' ++ M →
    (conjEval ((FreeGroup.mk c', t') :: f)).toWord = FreeGroup.invRev M ++ B' →
    c.length < M.length → M.length ≤ c.length + t.length →
    M = E ++ FreeGroup.invRev c →
    E <:+ t → 0 < E.length →
    lam * (t.length : ℚ) ≤ (E.length : ℚ) →
    ¬(FreeGroup.invRev M <+: palindrome c' t') →
    LandsInSharp R lam M.length
      (conjEval ((FreeGroup.mk c', t') :: f)).toWord (f.length + 1)

/-! ## The reduction -/

/-- **`LargeSegmentLands` reduced to the non-confined configuration.**  The
three confined ones are discharged: the overhang configuration cannot occur
under the large-segment hypothesis, and the buried and meeting ones land at
offset `0` and `|v|` respectively.

`hR` and `hRne` are spent only on normalizing the second factor and on the
nonemptiness of `t'`; `0 < λ` only on the buried offset; `λ ≤ 1/6` only on
reaching `swallow_bound_of_minimal'`. -/
theorem largeSegmentLands_of_nonConfined [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hnc : NonConfinedBlockLands R lam) :
    LargeSegmentLands R lam := by
  intro c t E M P' B' e g hmin ht hredp heq htail hlow hhigh hM _hMinv hEt
    hEpos _hsite hlarge
  have hmetric6 : MetricSmallCancellation R (1 / 6) :=
    metricSmallCancellation_of_le hlam hmetric
  cases e with
  | nil =>
      exfalso
      have h0 : (conjEval ([] : List (FreeGroup α × List (α × Bool)))).toWord
          = [] := by
        rw [conjEval_nil]
        exact FreeGroup.toWord_eq_nil_iff.mpr rfl
      rw [h0] at htail
      have hlen := congrArg List.length htail
      simp only [List.length_nil, List.length_append,
        FreeGroup.invRev_length] at hlen
      omega
  | cons x f =>
      obtain ⟨x', s'⟩ := x
      obtain ⟨c', t', ht', hredp', hmin₂⟩ := exists_palindromic_snd hR hRne hmin
      have htaileq : conjEval ((FreeGroup.mk c', t') :: f)
          = conjEval ((x', s') :: f) := by
        have h1 := hmin₂.2.1
        have h2 := hmin.2.1
        rw [conjEval_cons] at h1 h2
        exact mul_left_cancel (h1.trans h2.symm)
      rw [← htaileq] at htail ⊢
      have ht'pos : 0 < t'.length :=
        List.length_pos_iff.mpr (ne_nil_of_mem_symmetrization hRne ht')
      have hElen : M.length = E.length + c.length := by
        rw [hM, List.length_append, FreeGroup.invRev_length]
      have hminf : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: f)
          (conjEval ((FreeGroup.mk c', t') :: f)) := hmin₂.tail
      have hm : f.length < ((x', s') :: f).length := by
        simp only [List.length_cons]
        omega
      by_cases hconf : FreeGroup.invRev M <+: palindrome c' t'
      · obtain ⟨B'', heq'⟩ := hconf
        have hb2 : M.length ≤ c'.length + t'.length :=
          swallow_bound_of_minimal' hRne hmetric6 hmin₂.leadingPair ht ht'
            hredp hredp' heq heq'.symm
        have hcoin := mk_palindrome_mul_ne_one_of_minimal hmin₂
        rcases le_or_gt c'.length c.length with hle | hgt
        · -- the overhang configuration cannot occur at a large segment
          exfalso
          obtain ⟨E₀, q, hE₀t, hcq, hqt, hE₀len, hE₀pre⟩ :=
            exists_overlap_of_cancellation heq ⟨B'', heq'⟩
              (by rw [FreeGroup.invRev_length]; omega)
              (by rw [FreeGroup.invRev_length]; omega) hle (by omega)
          have hne : FreeGroup.invRev t ≠ t'.rotate q.length := by
            intro hcon
            exact hcoin (mk_palindrome_mul_eq_one_of_coincidence hcq hqt hcon)
          have hbnd := length_lt_of_eaten hmetric ht hE₀t
            (isPiece_of_overlap ht ht' hE₀t hE₀pre hne)
          rw [FreeGroup.invRev_length] at hE₀len
          have hcast : (E.length : ℚ) ≤ (E₀.length : ℚ) := by
            have hEle : E.length ≤ E₀.length := by omega
            exact_mod_cast hEle
          linarith
        · have hP2 : palindrome c' t' = c' ++ (t' ++ FreeGroup.invRev c') := by
            unfold palindrome
            rw [List.append_assoc]
          have hc'pre : c' <+: palindrome c' t' := by
            rw [hP2]
            exact ⟨t' ++ FreeGroup.invRev c', rfl⟩
          have hEpre : c ++ FreeGroup.invRev E <+: palindrome c' t' := by
            rw [← invRev_eaten_block hM]
            exact ⟨B'', heq'⟩
          have hcpre : c <+: palindrome c' t' :=
            (show c <+: c ++ FreeGroup.invRev E from ⟨_, rfl⟩).trans hEpre
          obtain ⟨y, hy⟩ := List.prefix_of_prefix_length_le hcpre hc'pre hgt.le
          have hylen : c'.length = c.length + y.length := by
            rw [← hy, List.length_append]
          rcases le_or_gt M.length c'.length with hin | hout
          · -- buried in the next conjugator
            exact landsInSharp_of_confined (i := 0) ht' hredp' hminf
              (cast_zero_lt_lam_mul hlam0 ht'pos) (by omega) hm
          · -- meeting the next rotation
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
            · have hvbnd : (v.length : ℚ) < lam * (t'.length : ℚ) :=
                hmetric v (isPiece_of_prefix_two ht' hrotmem hsame hvt' hvrot)
                  t' ht' hvt'
              exact landsInSharp_of_confined (i := v.length) ht' hredp' hminf
                hvbnd (by omega) hm
      · simp only [List.length_cons]
        exact hnc c t c' t' E M P' B' f g hmin₂ ht ht' hredp hredp' heq htail
          hlow hhigh hM hEt hEpos hlarge hconf

/-! ## The gate over the one remaining configuration -/

/-- **The sharp gate from the deep arc and the non-confined configuration.**
Composing with `GreendlingerLandingProd.sharpGreendlingerGate_of_deepArcSharp_of_largeSegmentLands`:
the (β) side of `SharpGreendlingerGate` is now one predicate about one
configuration of one head. -/
theorem sharpGreendlingerGate_of_deepArcSharp_of_nonConfined [DecidableEq α]
    (hdeep : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hnc : ∀ (R : Set (List (α × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → NonConfinedBlockLands R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate α :=
  sharpGreendlingerGate_of_deepArcSharp_of_largeSegmentLands hdeep
    (fun R lam hcyc hRne hlam0 hlam hmetric =>
      largeSegmentLands_of_nonConfined hcyc hRne hlam0 hlam hmetric
        (hnc R lam hcyc hRne hlam0 hlam hmetric))

/-- The same on the router's own alphabet. -/
theorem sharpGreendlingerGate_fin_two_of_deepArcSharp_of_nonConfined
    (hdeep : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → DeepArcSourceSharp R lam)
    (hnc : ∀ (R : Set (List (Fin 2 × Bool))) (lam : ℚ),
      (∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) → (∀ r ∈ R, r ≠ []) →
      0 < lam → lam ≤ 1 / 6 →
      MetricSmallCancellation R lam → NonConfinedBlockLands R lam) :
    GreendlingerFreeGate.SharpGreendlingerGate (Fin 2) :=
  sharpGreendlingerGate_of_deepArcSharp_of_nonConfined hdeep hnc

end SmallCancellationRouter
end GroupApproximation
