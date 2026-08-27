import GroupApproximation.Sofic.GreendlingerSharpLandingProduction
import GroupApproximation.Sofic.GreendlingerSharpInduction
import GroupApproximation.Sofic.GreendlingerLandingConfined

/-!
# The antecedent of the deep transfer: a landing for the head's own block

`GreendlingerSharpLandingProduction.landsInSharp_deepComposite_of_head` moved
the deep obligation one junction up:

    a landing site of depth `|M| + (N − |P'|)` in `(conjEval e).toWord`
      ⟹ a landing site of depth `D + (N − |P'|)` in `(conjEval f).toWord`,

factor budget unchanged.  This file measures the antecedent — what exactly has
to be produced at the head's own block — and discharges what it can.

## 1.  The antecedent, unfolded

Written out through `GreendlingerSharpTwins.LandsInSharp`, the antecedent of the
transfer is

    ∃ (c₃ t₃ : List (α × Bool)) (f₃ : List (FreeGroup α × List (α × Bool)))
      (A : List (α × Bool)) (N₃ i₃ : ℕ),
      f₃.length < f.length ∧
      (conjEval e).toWord
        = A ++ (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord.drop N₃ ∧
      t₃ ∈ symmetrization R ∧
      FreeGroup.IsReduced (palindrome c₃ t₃) ∧
      IsMinimalConjExpr R ((FreeGroup.mk c₃, t₃) :: f₃)
        (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)) ∧
      (i₃ : ℚ) < lam * (t₃.length : ℚ) ∧ N₃ ≤ c₃.length + i₃ ∧
      (|M| + (N − |P'|)) + N₃ ≤ |A| + |c₃| + i₃.

The last three fields are the only numeric content: a landing factor whose
rotation is eaten by less than `λ`, a cascade splitting the word in front of it
off as `A`, and a fit saying the block stops no later than `|A| + |c₃| + i₃`.

**The budget field is the sharp one.**  `f₃.length < f.length`, not
`f₃.length < e.length`.  `length_tail_of_junction` below shows
`e.length = f.length + 1` — both `((c,t) :: e)` and `((c,t) :: (c₂,t₂) :: f)`
are minimal for the same `g`, so they have the same length — and therefore the
landing factor may not be the head of `e`.  That is the same fact `hover` says
geometrically: the block has already overrun `palindrome c₂ t₂`, so it cannot
stop there.

Every hypothesis of `GreendlingerDeepInvariant.DeepCompositeLandsSharp` is
available at that point.  Two of them are not in the form the transfer wants,
and §2 converts both:

* `hover : ¬(invRev M <+: palindrome c₂ t₂)` is *not* a field of the predicate.
  It is a consequence of the deep regime through
  `GreendlingerSharpInduction.not_deep_confined_sharp`, which is what
  `GreendlingerDeepInvariant.exists_postJunction_drop` spends to reach this
  configuration.
* `hD : D + |B'| = |(conjEval f).toWord|` is not a field either — the predicate
  carries only `B' = (conjEval f).toWord.drop D`.  The two agree exactly when
  `B' ≠ []`; `length_drop_eq_of_ne_nil` is that step, and
  `GreendlingerSharpLandingProduction.ne_nil_of_deepCompositeLandsSharp` is why
  the `B' = []` corner cannot simply be waved through.

`landsInSharp_deepComposite_of_headLanding` is the transfer with both converted,
stated against the predicate's own hypothesis list plus `B' ≠ []`.

## 2.  Whether the forward constructor reaches it

`GreendlingerDeepInvariant.landsInSharp_of_forward_alignment` is capped at
`b ≤ |M|` (`GreendlingerSharpLandingProduction.le_of_forward_alignment_fields`),
and the antecedent asks for `b = |M| + (N − |P'|)`.  So the constructor is in
range exactly when `N ≤ |P'|`.

**The deep regime does not supply that.**  `survivor_lt_of_deep` reads
`|P'| + |M| = 2|c| + |t|` against `|c| + |t| < |M| + i` and gets
`|P'| < |c| + i`, while the predicate allows every `N ≤ |c| + i`; at the top of
that range, `lt_survivor_of_deep_max`, the side condition fails outright.  So
`N ≤ |P'|` is a genuine extra case and not a consequence.  It is not vacuous
either — `N = 0` is always admissible — and `sub_le_overrun_of_deep` bounds what
the other case costs: `N − |P'| ≤ |M| + i − (|c| + |t|)`, the overrun depth.

There is a second obstruction in that branch, and it is about the budget rather
than the depth.  `landsInSharp_of_forward_alignment` states its conclusion at
the factor budget `|e₁ ++ ((c₃,t₃) :: f₃)|`, which is `e.length`, one too many:
§1 needs `f.length = e.length − 1`.  The proof itself never needs the larger
number — it uses the budget field only to fill `f₃.length < m` — so
`landsInSharp_of_forward_alignment_budget` is that proof with `m` taken as a
parameter, and `e₁ ≠ []` is then what supplies `f₃.length < f.length`.

`landsInSharp_deepComposite_of_forward_alignment` is the resulting branch: under
`N ≤ |P'|`, `B' ≠ []`, `e₁ ≠ []` and a forward alignment of the head's block
against a later factor, the deep composite lands.  The head factor's provenance
`invRev M = c ++ invRev E`, `E <:+ t` enters exactly where
`GreendlingerSharpRigidity.intrusion_lt_of_forward_sharp` needs it, through the
`intrusion_lt_of_forward` call inside the constructor: that is the whole reason
the antecedent was worth moving to `M` in the first place.

What is *not* proved here is the alignment data itself.  Producing
`hcasc`, `hZ` and the two positional fields for the head's block is the same
question `GreendlingerLandingConfined.NonConfinedBlockLands` asks, one budget
tighter — and that predicate remains open.

## 3.  The other branch, and the base case

For `N > |P'|` the forward constructor is out of range by
`le_of_forward_alignment_fields`, and nothing in this file reaches it: the extra
depth `N − |P'|` is precisely the amount by which the block runs past what the
*head* factor keeps, so no alignment placed inside `invRev M` can certify it.
The honest reading is that the deep leaf splits, and that the second half needs
a producer that is not `landsInSharp_of_forward_alignment`.

One configuration of it closes with no alignment at all:
`landsInSharp_deepComposite_of_short` is
`GreendlingerSharpLandingProduction.landsInSharp_of_short_block` read at the
composite block, and discharges every instance in which the composite block
stops inside the next factor's conjugator — at any `N`, in either branch.

Nothing here discharges `DeepCompositeLandsSharp`.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The budget, and the well-posedness of the drop -/

/-- **The junction costs exactly one factor.**  `((c,t) :: e)` and
`((c,t) :: (c₂,t₂) :: f)` are both minimal expressions for the same `g`, so each
bounds the other's length, and `e.length = f.length + 1`.

This is what pins the antecedent's factor budget: the transfer carries the
budget across unchanged, so a landing for the head's block has to be found among
`f.length = e.length − 1` factors — the head of `e` itself is out of range. -/
theorem length_tail_of_junction [DecidableEq α] {R : Set (List (α × Bool))}
    {c t c₂ t₂ : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g) :
    e.length = f.length + 1 := by
  have h1 := hmin.2.2.1
    ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) hmin₂.1 hmin₂.2.1
  have h2 := hmin₂.2.2.1 ((FreeGroup.mk c, t) :: e) hmin.1 hmin.2.1
  simp only [List.length_cons] at h1 h2
  omega

/-- **A nonempty drop is a well-posed one.**  `DeepCompositeLandsSharp` carries
only `B' = W.drop D`, which every `D` past the end of `W` satisfies once `B'` is
empty; as soon as `B'` is nonempty the drop has not run past the end and the
arithmetic `D + |B'| = |W|` — the form
`GreendlingerSharpLandingProduction.exists_junction_split` and the transfer both
consume — comes back. -/
theorem length_drop_eq_of_ne_nil {β : Type*} {W B : List β} {D : ℕ}
    (hD : B = W.drop D) (hne : B ≠ []) : D + B.length = W.length := by
  have h := congrArg List.length hD
  rw [List.length_drop] at h
  have hpos : 0 < B.length := List.length_pos_iff.mpr hne
  omega

/-! ## 2.  The transfer, at the predicate's own interface -/

/-- **The deep obligation from a landing for the head's block**, stated against
exactly the hypotheses `GreendlingerDeepInvariant.DeepCompositeLandsSharp`
supplies, plus `B' ≠ []`.

`GreendlingerSharpLandingProduction.landsInSharp_deepComposite_of_head` takes
the overrun `hover` and the well-posedness `hD` as given; neither is a field of
the predicate.  Here both are derived: `hover` from the deep regime through
`GreendlingerSharpInduction.not_deep_confined_sharp`, and `hD` from `B' ≠ []`
through `length_drop_eq_of_ne_nil`.

The predicate's fields `N ≤ |c| + i` and `f.length < e.length` are not read —
the first is spent by the descent that consumes the conclusion, the second is
recovered sharply by `length_tail_of_junction`. -/
theorem landsInSharp_deepComposite_of_headLanding [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hRne : ∀ r ∈ R, r ≠ []) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {N i D : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length)
    (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i)
    (hD : B' = (conjEval f).toWord.drop D) (hne : B' ≠ [])
    (hhead : LandsInSharp R lam (M.length + (N - P'.length))
      (conjEval e).toWord f.length) :
    LandsInSharp R lam (D + (N - P'.length)) (conjEval f).toWord f.length := by
  have hover : ¬ (FreeGroup.invRev M <+: palindrome c₂ t₂) := by
    intro hpre
    obtain ⟨B'', hB''⟩ := hpre
    exact not_deep_confined_sharp hlam hRne hmetric hmin₂ ht ht₂ hredp hredp₂
      heq hB''.symm hlow hi hgt
  exact landsInSharp_deepComposite_of_head hmin hmin₂ hredp₂ htail hover
    (length_drop_eq_of_ne_nil hD hne) hhead

/-! ## 3.  Which `N` the forward constructor can reach -/

/-- **The head's survivor is shorter than the drop budget allows.**  In the deep
regime the block has eaten past the trailing conjugator, so what the head factor
keeps is under `|c| + i` letters — while `DeepCompositeLandsSharp` admits every
`N ≤ |c| + i`.

This is the measurement that decides §2 of
`GreendlingerSharpLandingProduction`: the extra depth the antecedent asks for,
`N − |P'|`, is not always zero. -/
theorem survivor_lt_of_deep {c t P' M : List (α × Bool)} {i : ℕ}
    (heq : palindrome c t = P' ++ M)
    (hgt : c.length + t.length < M.length + i) :
    P'.length < c.length + i := by
  have hb := congrArg List.length heq
  rw [length_palindrome, List.length_append] at hb
  omega

/-- **At the top of the drop range the side condition fails.**  So `N ≤ |P'|` is
a genuine extra hypothesis on `DeepCompositeLandsSharp`, not a consequence of
the deep regime: the instance `N = |c| + i`, which the predicate admits, always
violates it. -/
theorem lt_survivor_of_deep_max {c t P' M : List (α × Bool)} {i N : ℕ}
    (heq : palindrome c t = P' ++ M)
    (hgt : c.length + t.length < M.length + i)
    (hN : N = c.length + i) : P'.length < N := by
  have h := survivor_lt_of_deep heq hgt
  omega

/-- **What the other branch costs.**  The extra depth the antecedent asks for
past `|M|` is bounded by the overrun — the amount by which the head's block ran
past the whole of its own palindrome.  Zero exactly in the branch §2 can reach,
and at most `|M| + i − (|c| + |t|)` otherwise. -/
theorem sub_le_overrun_of_deep {c t P' M : List (α × Bool)} {i N : ℕ}
    (heq : palindrome c t = P' ++ M)
    (hN : N ≤ c.length + i) :
    N - P'.length ≤ M.length + i - (c.length + t.length) := by
  have hb := congrArg List.length heq
  rw [length_palindrome, List.length_append] at hb
  omega

/-! ## 4.  The forward constructor at a sharp factor budget -/

/-- **`GreendlingerDeepInvariant.landsInSharp_of_forward_alignment` with the
factor budget taken as a parameter.**

The original states its conclusion at the budget
`(e₁ ++ ((c₃,t₃) :: f₃)).length`, which is the length of the whole tail
expression.  Its proof never needs that number: the budget enters only as the
first field of the landing site, `f₃.length < m`.  Taking `m` as a hypothesis is
therefore the same proof, and it is what §5 needs, because the transfer's
antecedent is stated at `f.length = e.length − 1` rather than at `e.length`.

Everything else is quoted from the original, including the two containment
lemmas of `GreendlingerDeepOverrunCount` and the front piece bound
`intrusion_lt_of_forward`, which is where the head factor's provenance
`invRev M = c ++ invRev E`, `E <:+ t` is spent. -/
theorem landsInSharp_of_forward_alignment_budget [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    {c t c₃ t₃ M E A Z : List (α × Bool)}
    {e₁ f₃ : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    {N i b m : ℕ}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))) g)
    (ht : t ∈ symmetrization R)
    (hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃))
    (hcasc : (conjEval (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))).toWord
      = A ++ (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord.drop N)
    (hc₃V : (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord = c₃ ++ Z)
    (hN : N ≤ c₃.length) (hZ : t₃.take i <+: Z)
    (hM : FreeGroup.invRev M = c ++ FreeGroup.invRev E) (hEsuf : E <:+ t)
    (hMW : FreeGroup.invRev M
      <+: (conjEval (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))).toWord)
    (hlow : c.length ≤ A.length + (c₃.length - N))
    (hhigh : A.length + (c₃.length - N) + i ≤ M.length)
    (hNi : N ≤ c₃.length + i)
    (hfit : b + N ≤ A.length + c₃.length + i)
    (hm : f₃.length < m) :
    LandsInSharp R lam b
      (conjEval (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))).toWord m := by
  have ht₃ : t₃ ∈ symmetrization R := hmin.1 (FreeGroup.mk c₃, t₃) (by simp)
  have hdrop : ((FreeGroup.mk c, t)
      :: (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))).drop (e₁.length + 1)
      = (FreeGroup.mk c₃, t₃) :: f₃ := by
    rw [List.drop_succ_cons, List.drop_left]
  have hmin₃ := isMinimalConjExpr_drop (e₁.length + 1)
    ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))) g hmin
  rw [hdrop] at hmin₃
  have hVc : (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord.take N
      = c₃.take N := by
    rw [hc₃V, take_append_of_le N c₃ Z hN]
  have hPQ : FreeGroup.mk
        (conjEval (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))).toWord
      = conjEval e₁
        * FreeGroup.mk (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord := by
    rw [FreeGroup.mk_toWord, FreeGroup.mk_toWord, conjEval_append]
  have hd := mk_effectiveConjugator_of_split hcasc hVc rfl hPQ
  obtain ⟨y, hy, hyE⟩ :=
    exists_forward_containment hcasc hc₃V hN hM hMW hlow (by omega)
  obtain ⟨y', hy', halign⟩ :=
    exists_forward_alignment hcasc hc₃V hN hZ hM hEsuf hMW hlow hhigh
  have hyy : y = y' := List.append_cancel_left (hy.symm.trans hy')
  have halign' : t₃.take i <+: (FreeGroup.invRev t).rotate y.length := by
    rw [hyy]
    exact halign
  have hpiece : (i : ℚ) < lam * (t₃.length : ℚ) :=
    intrusion_lt_of_forward hlam hmetric hmin ht ht₃ hd hy
      (hyE.trans (invRev_prefix_of_suffix hEsuf)) halign'
  exact ⟨c₃, t₃, f₃, A, N, i, hm, hcasc, ht₃, hredp₃, hmin₃,
    hpiece, hNi, hfit⟩

/-! ## 5.  The branch `N ≤ |P'|` -/

/-- **The transfer in the branch the forward constructor can reach.**  When
`N ≤ |P'|` the antecedent collapses to a landing site at the head block's own
depth `|M|` — which is the depth
`GreendlingerDeepInvariant.landsInSharp_of_forward_alignment` is capped at by
`GreendlingerSharpLandingProduction.le_of_forward_alignment_fields` — and the
conclusion to one at depth `D`. -/
theorem landsInSharp_deepComposite_of_headLanding_of_le [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hRne : ∀ r ∈ R, r ≠ []) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    {c t c₂ t₂ P' M B' : List (α × Bool)}
    {e f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α} {N i D : ℕ}
    (hmin : IsMinimalConjExpr R ((FreeGroup.mk c, t) :: e) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval e).toWord = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length)
    (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i)
    (hD : B' = (conjEval f).toWord.drop D) (hne : B' ≠ [])
    (hNP : N ≤ P'.length)
    (hhead : LandsInSharp R lam M.length (conjEval e).toWord f.length) :
    LandsInSharp R lam (D + (N - P'.length)) (conjEval f).toWord f.length := by
  refine landsInSharp_deepComposite_of_headLanding hRne hlam hmetric hmin hmin₂
    ht ht₂ hredp hredp₂ heq htail hlow hi hgt hD hne ?_
  rw [show M.length + (N - P'.length) = M.length from by omega]
  exact hhead

/-- **The branch, discharged from a forward alignment of the head's block.**

Under `N ≤ |P'|`, `B' ≠ []` and `e₁ ≠ []`, a forward alignment of the head's
block `invRev M` against a later factor `(c₃, t₃)` of the tail produces the
antecedent of the transfer at the sharp factor budget, and the deep composite
lands.

`e₁ ≠ []` is what makes the budget work: `length_tail_of_junction` gives
`|e₁| + |f₃| + 1 = |f| + 1`, so the landing factor is inside `f` exactly when
the head of `e` is not the landing factor.  That is the arithmetic form of
`hover`.

The alignment data itself — `hcasc`, `hZ`, and the two positional fields — is
not produced here; supplying it for the head's block is
`GreendlingerLandingConfined.NonConfinedBlockLands` one budget tighter, and that
is open.  What this theorem settles is that once the data is in hand, the depth
and the budget both come out right in this branch. -/
theorem landsInSharp_deepComposite_of_forward_alignment [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hRne : ∀ r ∈ R, r ≠ []) (hlam : lam ≤ 1 / 6)
    (hmetric : MetricSmallCancellation R lam)
    {c t c₂ t₂ c₃ t₃ P' M E A Z B' : List (α × Bool)}
    {e₁ f₃ f : List (FreeGroup α × List (α × Bool))} {g : FreeGroup α}
    {N i N₃ i₃ D : ℕ}
    (hmin : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))) g)
    (hmin₂ : IsMinimalConjExpr R
      ((FreeGroup.mk c, t) :: (FreeGroup.mk c₂, t₂) :: f) g)
    (ht : t ∈ symmetrization R) (ht₂ : t₂ ∈ symmetrization R)
    (hredp : FreeGroup.IsReduced (palindrome c t))
    (hredp₂ : FreeGroup.IsReduced (palindrome c₂ t₂))
    (hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃))
    (heq : palindrome c t = P' ++ M)
    (htail : (conjEval (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))).toWord
      = FreeGroup.invRev M ++ B')
    (hlow : c.length < M.length)
    (hi : (i : ℚ) < lam * (t.length : ℚ))
    (hgt : c.length + t.length < M.length + i)
    (hD : B' = (conjEval f).toWord.drop D) (hne : B' ≠ [])
    (hNP : N ≤ P'.length) (he₁ : e₁ ≠ [])
    (hcasc : (conjEval (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))).toWord
      = A ++ (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord.drop N₃)
    (hc₃V : (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord = c₃ ++ Z)
    (hN₃ : N₃ ≤ c₃.length) (hZ : t₃.take i₃ <+: Z)
    (hM : FreeGroup.invRev M = c ++ FreeGroup.invRev E) (hEsuf : E <:+ t)
    (hAlow : c.length ≤ A.length + (c₃.length - N₃))
    (hAhigh : A.length + (c₃.length - N₃) + i₃ ≤ M.length)
    (hN₃i : N₃ ≤ c₃.length + i₃)
    (hfit : M.length + N₃ ≤ A.length + c₃.length + i₃) :
    LandsInSharp R lam (D + (N - P'.length)) (conjEval f).toWord f.length := by
  have hbud : (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃)).length = f.length + 1 :=
    length_tail_of_junction hmin hmin₂
  have he₁pos : 0 < e₁.length := List.length_pos_iff.mpr he₁
  have hm : f₃.length < f.length := by
    simp only [List.length_append, List.length_cons] at hbud
    omega
  have hMW : FreeGroup.invRev M
      <+: (conjEval (e₁ ++ ((FreeGroup.mk c₃, t₃) :: f₃))).toWord :=
    ⟨B', htail.symm⟩
  have hhead := landsInSharp_of_forward_alignment_budget hlam hmetric hmin ht
    hredp₃ hcasc hc₃V hN₃ hZ hM hEsuf hMW hAlow hAhigh hN₃i hfit hm
  exact landsInSharp_deepComposite_of_headLanding_of_le hRne hlam hmetric hmin
    hmin₂ ht ht₂ hredp hredp₂ heq htail hlow hi hgt hD hne hNP hhead

/-! ## 6.  The base case, at either branch -/

/-- **The composite block that stops inside the next conjugator lands there.**

`GreendlingerSharpLandingProduction.landsInSharp_of_short_block` read at the
depth `D + (N − |P'|)` and the budget `f.length` that
`GreendlingerDeepInvariant.DeepCompositeLandsSharp` asks for, with the tail past
the junction already in palindromic normal form.

No alignment, no piece bound and no branch condition: this discharges every
instance in which the composite block has not reached the next factor's
rotation, whether or not `N ≤ |P'|`. -/
theorem landsInSharp_deepComposite_of_short [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (hRne : ∀ r ∈ R, r ≠ [])
    (hlam0 : 0 < lam)
    {c₃ t₃ : List (α × Bool)} {f₃ : List (FreeGroup α × List (α × Bool))}
    {D k : ℕ}
    (ht₃ : t₃ ∈ symmetrization R)
    (hredp₃ : FreeGroup.IsReduced (palindrome c₃ t₃))
    (hmin₃ : IsMinimalConjExpr R ((FreeGroup.mk c₃, t₃) :: f₃)
      (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)))
    (hshort : D + k ≤ c₃.length) :
    LandsInSharp R lam (D + k)
      (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord
      ((FreeGroup.mk c₃, t₃) :: f₃).length :=
  landsInSharp_of_short_block hRne hlam0 ht₃ hredp₃ hmin₃ hshort
    (by simp only [List.length_cons]; omega)

end SmallCancellationRouter
end GroupApproximation
