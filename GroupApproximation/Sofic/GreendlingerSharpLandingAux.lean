import GroupApproximation.Sofic.GreendlingerLanding
import GroupApproximation.Sofic.GreendlingerLandingConfined

/-!
# The two landing twins the sharp layer was still missing

The landing and cascade machinery is written twice.  `GreendlingerCascade` and
`GreendlingerLanding` carry it pinned at `λ = 1/6`, where every bound is natural
number arithmetic and `omega` closes it; `GreendlingerSharpTwins` §7 and
`GreendlingerLandingProd` §§1–2 carry the `λ`-parameterized twins.  That
twinning is very nearly complete: `LandsInSharp`, `LandsInSharp.of_le`,
`LandsInSharp.mono`, `landsInSharp_of_confined`, `CascadeLandingSharp`,
`GreendlingerAtSharp.transport`, `LandsInSharp.compose`,
`landsInSharp_of_overrun` and the three descent theorems above them are all in
place, and `GreendlingerLandingConfined` is written at a general `λ` from the
start.

Two statements were left behind, and both are supplied here.

## The overlap producer

`GreendlingerThreeFactor.greendlingerAt_of_overlap` is the third of the four
producers of the located conclusion — the one that reads the block against the
*next* palindrome when the leading conjugator is the longer of the two.  Its
three siblings (`greendlingerAt_of_short_cancellation`,
`greendlingerAt_of_bounded_cancellation`, and the two- and three-piece counts)
were all twinned in `GreendlingerSharpTwins` §5; this one was not, because no
sharp consumer had yet needed it.  `greendlingerAtSharp_of_overlap` is it, and
the twinning is mechanical: the overlap `E` the block eats out of the leading
rotation is a piece, so `GreendlingerSharpTwins.length_lt_of_eaten` bounds it by
`λ·|t|` directly instead of `six_mul_length_lt_of_eaten` bounding `6|E|` by
`|t|`, and `greendlingerAtSharp_of_two_pieces` consumes that bound together with
the offset.  Nothing about the geometry is re-examined:
`GreendlingerOverlap.exists_overlap_of_cancellation` and `isPiece_of_overlap`
are `λ`-free and are quoted unchanged.

## The subsumption record

`GreendlingerLanding.cascadeLanding_of_leadingConfinement` proves that
`CascadeLanding` is a *weakening* of `GreendlingerThreeFactor.LeadingConfinement`
— everything the confinement route proves, the cascade route proves — and the
value of that statement is exactly that it is one-directional, since
`LeadingConfinement` is refuted by the configuration in
`GreendlingerThreeFactor`'s header while `CascadeLanding` survives it.
`cascadeLandingSharp_of_leadingConfinement` is the same record on the sharp
side, so the two towers stay comparable statement for statement.

It is a record and not a route: its hypothesis is the refuted one, so it cannot
be used to discharge `GreendlingerSharpResidualWiring.SharpResiduals`.  The
route that can is `GreendlingerLandingConfined.largeSegmentLands_of_nonConfined`,
which replays the same four-case split against `NonConfinedBlockLands` — the
question *inside* the configuration confinement asserts away — rather than
against confinement itself.

## Where the constants are spent

`LeadingConfinement` names no constant, so the twinning cost is only in the
arithmetic:

* `λ ≤ 1/6` twice.  Once through
  `GreendlingerDeepVacuitySharp.metricSmallCancellation_of_le`, to reach
  `GreendlingerRegime.swallow_bound_of_minimal` and `swallow_bound_of_minimal'`,
  which are stated at the half constant; and once through
  `GreendlingerDeepVacuitySharp.six_mul_lt_of_lam_lt`, which turns the sharp
  offset hypothesis back into the `λ`-free file's `6j < |t|` so that every
  `omega` in the descent is discharged by the identical certificate.
* `0 < λ` once, in the buried configuration, where the landing offset is `0` and
  `GreendlingerLandingProd.cast_zero_lt_lam_mul` is what makes it admissible.
  The `λ`-free file spends nothing there, because `6·0 < |t'|` is `0 < |t'|`.
* The meeting configuration's own piece bound is read at `λ` directly and needs
  no conversion: `hmetric` applied to the meeting segment is already the offset
  field `landsInSharp_of_confined` asks for.

Separate module so that neither of these can take a live route down with it.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The overlap producer, at the sharp constant -/

/-- **The overlap case, located and with slack, at the sharp constant.**  The
`λ`-twin of `GreendlingerThreeFactor.greendlingerAt_of_overlap`.

When the leading conjugator is the longer of the two, the overlap the block eats
out of the leading rotation is a piece — were it not, the two factors would
spell mutually inverse elements, which minimality forbids — so `C'(λ)` leaves
more than `(1 − λ)` of that rotation standing, and the offset spends at most
another `λ`.  `greendlingerAtSharp_of_two_pieces` is exactly that budget.

The `λ`-free version clears the denominator and reads the same two bounds as
`6|E| < |t|` and `6j < |t|`; the band `λ ≤ 1/6` is inherited from
`greendlingerAtSharp_of_bounded_cancellation` and is used only to know that the
two losses together stay inside the rotation they are measured against. -/
theorem greendlingerAtSharp_of_overlap {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    {c t c' t' P' M B' : List (α × Bool)} {j : ℕ}
    (ht : t ∈ symmetrization R) (ht' : t' ∈ symmetrization R)
    (heq : palindrome c t = P' ++ M)
    (hpre : FreeGroup.invRev M <+: palindrome c' t')
    (hhigh : M.length ≤ (FreeGroup.invRev c).length + t.length)
    (hle : c'.length ≤ c.length)
    (hfit : c.length - c'.length + M.length ≤ c.length + t'.length)
    (hcoin : FreeGroup.mk (palindrome c t) * FreeGroup.mk (palindrome c' t') ≠ 1)
    (hj : (j : ℚ) < lam * (t.length : ℚ)) :
    GreendlingerAtSharp R lam (c.length + j) (P' ++ B') := by
  rcases le_or_gt M.length (FreeGroup.invRev c).length with hshort | hlong
  · exact greendlingerAtSharp_of_short_cancellation hlam ht heq hshort hj
  · obtain ⟨E, q, hEt, hcq, hqt, hElen, hEpre⟩ :=
      exists_overlap_of_cancellation heq hpre hlong.le hhigh hle hfit
    have hne : FreeGroup.invRev t ≠ t'.rotate q.length := by
      intro hcon
      exact hcoin (mk_palindrome_mul_eq_one_of_coincidence hcq hqt hcon)
    have hpiece : IsPiece (symmetrization R) (FreeGroup.invRev E) :=
      isPiece_of_overlap ht ht' hEt hEpre hne
    exact greendlingerAtSharp_of_two_pieces hlam ht heq hElen
      (length_lt_of_eaten hmetric ht hEt hpiece) hj

/-! ## 2.  Confinement is a sharp landing site -/

/-- **The old hypothesis implies the new one, at the sharp constant.**  The
`λ`-twin of `GreendlingerLanding.cascadeLanding_of_leadingConfinement`: every
configuration of `GreendlingerThreeFactor`'s descent produces either the located
conclusion at the sharp bound from the leading factor itself, or a landing site
in the factor immediately next, with nothing dropped and nothing surviving in
front.

The four configurations are unchanged, and so is every geometric step of the
argument.  What moves is only where the constant is read:
`greendlingerAtSharp_of_overlap` in the overhang configuration,
`cast_zero_lt_lam_mul` for the buried one's zero offset, and the metric
condition applied directly to the meeting segment for the meeting one — where
the `λ`-free file called `six_mul_length_lt_of_isPiece` twice, once against each
of the two relators the segment prefixes.

This records that `CascadeLandingSharp` is a weakening of `LeadingConfinement`,
and nothing more: the hypothesis is the refuted one, so the statement is a
comparison between the two towers rather than a step towards discharging the
sharp residual. -/
theorem cascadeLandingSharp_of_leadingConfinement [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hconf : LeadingConfinement R) :
    CascadeLandingSharp R lam := by
  intro c t e g P' M B' j hmin ht hredp heq hgw hlong hj
  have hmetric6 : MetricSmallCancellation R (1 / 6) :=
    metricSmallCancellation_of_le hlam hmetric
  have h6j : 6 * j < t.length := six_mul_lt_of_lam_lt hlam hj
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
        swallow_bound_of_minimal hRne hmetric6 hmin₂ ht ht' hredp hredp' heq
          heq'.symm
      have hb2 : M.length ≤ c'.length + t'.length :=
        swallow_bound_of_minimal' hRne hmetric6 hmin₂.leadingPair ht ht' hredp
          hredp' heq heq'.symm
      have hcoin := mk_palindrome_mul_ne_one_of_minimal hmin₂
      have hminf : IsMinimalConjExpr R ((FreeGroup.mk c', t') :: e'')
          (conjEval ((FreeGroup.mk c', t') :: e'')) := hmin₂.tail
      have hshorter : e''.length < ((x', s') :: e'').length := by
        simp only [List.length_cons]
        omega
      rcases le_or_gt c'.length c.length with hle | hgt
      · exact Or.inl (greendlingerAtSharp_of_overlap hlam hmetric ht ht' heq
          ⟨B'', heq'⟩ (by omega) hle (by omega) hcoin hj)
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
            landsInSharp_of_confined (i := 0) ht' hredp' hminf
              (cast_zero_lt_lam_mul hlam0 ht'pos) (by omega) hshorter⟩
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
            have hvbnd : (v.length : ℚ) < lam * (t'.length : ℚ) :=
              hmetric v hpiece t' ht' hvt'
            have hvt : (v.length : ℚ) < lam * (t.length : ℚ) := by
              have hb := hmetric v hpiece
                ((FreeGroup.invRev t).rotate y.length) hrotmem hvrot
              rwa [List.length_rotate, FreeGroup.invRev_length] at hb
            have h6t : 6 * v.length < t.length := six_mul_lt_of_lam_lt hlam hvt
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
              landsInSharp_of_confined (i := v.length) ht' hredp' hminf hvbnd
                (by omega) hshorter⟩

/-! ## 3.  The sharp gate, along the old route -/

/-- **The sharp cascade route subsumes the sharp confinement route.**  The
`λ`-twin of `GreendlingerLanding.greendlingerConclusion_of_leadingConfinement'`:
anything the confinement route proves at the sharp bound, the cascade route
proves — and the cascade route's hypothesis survives the configuration that
refutes the confinement route's. -/
theorem greendlingerConclusionSharp_of_leadingConfinement [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    (hconf : LeadingConfinement R) :
    GreendlingerConclusionSharp R lam :=
  greendlingerConclusionSharp_of_cascadeLandingSharp hR hRne hlam0 hlam
    (cascadeLandingSharp_of_leadingConfinement hR hRne hlam0 hlam hmetric hconf)

end SmallCancellationRouter
end GroupApproximation
