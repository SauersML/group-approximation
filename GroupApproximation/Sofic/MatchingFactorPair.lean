import GroupApproximation.Sofic.MatchingSameBlock
import GroupApproximation.Sofic.PalindromicMinimalExpr

/-!
# No matched pair has both ends in one factor — the stems, priced

`MatchingSameBlock.block_ne_of_mem_pairs_labelledWord` proves that no matched
pair of the expression's diagram has both ends in one **block**.  That is not
enough for the stems.  `conj k`, `relator k` and `stem k` are three *different*
blocks of one **factor**, so the configuration that matters most —

    a letter of the conjugator `cₖ` cancelling against a letter of its own
    relator `tₖ`, or against its own mirror copy in `invRev cₖ`

— is permitted by that theorem and has to be excluded separately.
`MatchingStemContraction`'s header names exactly this gap: *"What it does not
say, and what the stem problem needs, is that no pair has both ends in the same
factor … The tool for that strengthening is the factor index in place of the
block itself; nothing here proves it."*  This file proves it.

## What it costs

Exactly one thing, and `PalindromicMinimalExpr` supplies it for free: each
factor's word

    `cₖ ++ (tₖ ++ invRev cₖ)`

is **reduced**.  That is `IsPalindromicExpr`, and
`exists_palindromic_isMinimalConjExpr_all` says every minimal expression can be
respelled to satisfy it without changing the number of factors or raising the
weight.  So the exclusion is available to the curvature count at no charge.

## How

`Block.factor` reads a block's factor index — `some k` for the three blocks of
factor `k`, `none` for the boundary — and the proof is
`MatchingSameBlock.blk_ne_of_mem_pairs` at `blk := Block.factor ∘ Prod.snd`,
whose two hypotheses are discharged here:

* `grouped_map_factor_labelledWord` — the *factors* are intervals of the word.
  This is where the factor reading is cheaper than the block reading: a factor's
  three blocks are adjacent, so merging them merges adjacent groups, and the
  boundary keeps a label of its own (`none`) that no factor shares.
* `factorsReduced_labelledWord` — a stretch of the word carrying one factor
  label lies inside that factor's word, which the palindromic hypothesis makes
  reduced.  Note the constancy hypothesis is never read for a single factor:
  `map_fst_labelledFactor` says the whole factor is `c ++ (t ++ invRev c)`, so
  *every* subword of it is reduced, constant-labelled or not.

## What it says about the picture

The cactus has `n` discs joined to a basepoint by stems, the two sides of the
`k`-th stem being the `conj k` and `stem k` letters.  The theorem says:

* the two sides of a stem never meet each other (`conj_ne_stem_pair`),
* a stem never meets the disc it carries (`conj_ne_relator_pair`), and
* a conjugator letter is therefore always matched into a *different* factor or
  into the boundary (`factor_ne_of_mem_pairs_labelledWord`).

It also re-derives `MatchingBoundaryBlock.not_boundary_pair` — two boundary
letters both have factor `none` — by a different route and at a different price:
that file pays with reducedness of `w` alone, this one with reducedness of every
palindrome.  Neither supersedes the other.

Nothing here counts anything, and nothing here discharges a gate: the degree
bound remains open.  What is closed is the objection that a run of a relator
block might land in its own conjugator.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  The factor of a block -/

/-- **Which factor a block belongs to.**  The three blocks of factor `k` share
the value `some k`; the boundary belongs to no factor and gets `none`, a value
no factor can take.

`MatchingSameBlock.Block.index` sends the boundary to `0`, which collides with
factor `0`; that is harmless there because the value is never read at the
boundary, but a *pair* has two ends and the collision would be read here. -/
def Block.factor : Block → Option ℕ
  | Block.conj k => some k
  | Block.relator k => some k
  | Block.stem k => some k
  | Block.boundary => none

@[simp] theorem Block.factor_conj (k : ℕ) : (Block.conj k).factor = some k := rfl

@[simp] theorem Block.factor_relator (k : ℕ) :
    (Block.relator k).factor = some k := rfl

@[simp] theorem Block.factor_stem (k : ℕ) : (Block.stem k).factor = some k := rfl

@[simp] theorem Block.factor_boundary : Block.boundary.factor = none := rfl

/-- Away from the boundary, the factor is the index. -/
theorem Block.factor_eq_some_index {b : Block} (h : b ≠ Block.boundary) :
    b.factor = some b.index := by
  cases b with
  | conj k => rfl
  | relator k => rfl
  | stem k => rfl
  | boundary => exact absurd rfl h

/-! ## 2.  The factors are intervals -/

/-- A list all of whose entries agree is grouped: there is nothing between two
occurrences of a label that is not that label. -/
theorem grouped_of_const {γ : Type*} {l : List γ}
    (h : ∀ x ∈ l, ∀ y ∈ l, x = y) : Grouped l := by
  intro p m s b hEq c hc
  refine h c ?_ b ?_
  · rw [hEq]
    exact List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_append_left _ hc))
  · rw [hEq]
    exact List.mem_append_right _ List.mem_cons_self

/-- **One factor is one label.**  This is the whole reason the factor reading is
cheaper than the block reading: `labelledFactor` emits three *adjacent* runs,
and the three collapse to a single constant run under `Block.factor`. -/
theorem factor_eq_of_mem_map_labelledFactor {k : ℕ} {c s : List (α × Bool)}
    {v : Option ℕ}
    (h : v ∈ (labelledFactor k c s).map (fun z => (z.2).factor)) : v = some k := by
  obtain ⟨z, hz, hv⟩ := List.mem_map.mp h
  rw [← hv]
  rcases mem_map_snd_labelledFactor (List.mem_map_of_mem hz) with h' | h' | h' <;>
    rw [h'] <;> rfl

theorem grouped_map_factor_labelledFactor (k : ℕ) (c s : List (α × Bool)) :
    Grouped ((labelledFactor k c s).map (fun z => (z.2).factor)) :=
  grouped_of_const fun _ hx _ hy => by
    rw [factor_eq_of_mem_map_labelledFactor hx,
      factor_eq_of_mem_map_labelledFactor hy]

/-- Every label of a labelled expression names a factor of index at least the
starting one — and never the boundary. -/
theorem factor_mem_of_mem_map_labelledExpr [DecidableEq α]
    (k : ℕ) (e : List (FreeGroup α × List (α × Bool))) (v : Option ℕ)
    (h : v ∈ (labelledExpr k e).map (fun z => (z.2).factor)) :
    ∃ j, k ≤ j ∧ v = some j := by
  obtain ⟨z, hz, hv⟩ := List.mem_map.mp h
  obtain ⟨h1, h2⟩ := mem_map_snd_labelledExpr k e z.2 (List.mem_map_of_mem hz)
  exact ⟨(z.2).index, h1, by rw [← hv]; exact Block.factor_eq_some_index h2⟩

/-- A labelled expression is grouped by factor: one factor's run, then the rest,
with the factor indices separating them. -/
theorem grouped_map_factor_labelledExpr [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))),
      Grouped ((labelledExpr k e).map (fun z => (z.2).factor)) := by
  intro k e
  induction e generalizing k with
  | nil =>
      rw [labelledExpr_nil, List.map_nil]
      exact grouped_nil
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      rw [labelledExpr_cons, List.map_append]
      refine grouped_append (grouped_map_factor_labelledFactor _ _ _) (ih (k + 1)) ?_
      intro y hy z hz
      obtain ⟨j, hj, hzj⟩ := factor_mem_of_mem_map_labelledExpr (k + 1) e z hz
      rw [factor_eq_of_mem_map_labelledFactor hy, hzj]
      intro hEq
      have hkj : k = j := Option.some.inj hEq
      omega

/-- Every boundary label has no factor. -/
theorem factor_eq_none_of_mem_map_tag_boundary {l : List (α × Bool)} {v : Option ℕ}
    (h : v ∈ (tag Block.boundary l).map (fun z => (z.2).factor)) : v = none := by
  obtain ⟨z, hz, hv⟩ := List.mem_map.mp h
  rw [← hv, snd_eq_of_mem_tag hz]
  rfl

/-- **The labelled word is grouped by factor.**  The expression part is grouped,
the boundary part is a constant run of `none`, and no factor takes the value
`none`. -/
theorem grouped_map_factor_labelledWord [DecidableEq α]
    (e : List (FreeGroup α × List (α × Bool))) (w : List (α × Bool)) :
    Grouped ((labelledWord e w).map (fun z => (z.2).factor)) := by
  rw [labelledWord, List.map_append]
  refine grouped_append (grouped_map_factor_labelledExpr 0 e)
    (grouped_of_const fun _ hx _ hy => by
      rw [factor_eq_none_of_mem_map_tag_boundary hx,
        factor_eq_none_of_mem_map_tag_boundary hy]) ?_
  intro x hx y hy
  obtain ⟨j, -, hxj⟩ := factor_mem_of_mem_map_labelledExpr 0 e x hx
  rw [hxj, factor_eq_none_of_mem_map_tag_boundary hy]
  exact Option.some_ne_none j

/-! ## 3.  Each factor is spelled by a reduced word -/

/-- **Every constant-factor subword maps to a reduced word.**  The factor
analogue of `MatchingSameBlock.BlocksReduced`. -/
def FactorsReduced (l : List ((α × Bool) × Block)) : Prop :=
  ∀ M : List ((α × Bool) × Block), M <:+: l →
    (∀ x ∈ M, ∀ y ∈ M, (x.2).factor = (y.2).factor) →
      FreeGroup.IsReduced (M.map Prod.fst)

/-- A tagged segment of a reduced word has reduced factors. -/
theorem factorsReduced_tag (b : Block) {l : List (α × Bool)}
    (h : FreeGroup.IsReduced l) : FactorsReduced (tag b l) := by
  intro M hM _
  refine isReduced_of_infix ?_ h
  rw [← map_fst_tag b l]
  exact infix_map_of_infix Prod.fst hM

/-- **One labelled factor has reduced factors**, and the constancy hypothesis is
never read: the factor's whole word is `c ++ (t ++ invRev c)`, so *every* subword
of it is reduced as soon as that is.  This is where the palindromic hypothesis is
spent, and it is spent once. -/
theorem factorsReduced_labelledFactor (k : ℕ) {c s : List (α × Bool)}
    (h : FreeGroup.IsReduced (c ++ (s ++ FreeGroup.invRev c))) :
    FactorsReduced (labelledFactor k c s) := by
  intro M hM _
  refine isReduced_of_infix ?_ h
  rw [← map_fst_labelledFactor k c s]
  exact infix_map_of_infix Prod.fst hM

/-- Concatenating with disjoint factor sets preserves it: a constant-factor
subword of the join cannot meet both sides. -/
theorem factorsReduced_append {l₁ l₂ : List ((α × Bool) × Block)}
    (h₁ : FactorsReduced l₁) (h₂ : FactorsReduced l₂)
    (hdisj : ∀ x ∈ l₁, ∀ y ∈ l₂, (x.2).factor ≠ (y.2).factor) :
    FactorsReduced (l₁ ++ l₂) := by
  intro M hM hconst
  rcases M with _ | ⟨z, M'⟩
  · rw [List.map_nil]
    exact FreeGroup.IsReduced.nil
  · have hMP : ∀ u ∈ z :: M', (u.2).factor = (z.2).factor := fun u hu =>
      hconst u hu z List.mem_cons_self
    by_cases hb : ∃ y ∈ l₁, (y.2).factor = (z.2).factor
    · obtain ⟨y, hy, hyz⟩ := hb
      have h₂' : ∀ u ∈ l₂, ¬ ((u.2).factor = (z.2).factor) := by
        intro u hu huz
        exact hdisj y hy u hu (by rw [hyz, huz])
      exact h₁ _ (infix_left_of_infix_append hM hMP h₂') hconst
    · have h₁' : ∀ u ∈ l₁, ¬ ((u.2).factor = (z.2).factor) := by
        intro u hu huz
        exact hb ⟨u, hu, huz⟩
      exact h₂ _ (infix_right_of_infix_append hM hMP h₁') hconst

/-- A labelled expression has reduced factors, given a palindromic expression. -/
theorem factorsReduced_labelledExpr [DecidableEq α] :
    ∀ (k : ℕ) (e : List (FreeGroup α × List (α × Bool))),
      (∀ q ∈ e, FreeGroup.IsReduced
        (q.1.toWord ++ (q.2 ++ FreeGroup.invRev q.1.toWord))) →
        FactorsReduced (labelledExpr k e) := by
  intro k e
  induction e generalizing k with
  | nil =>
      intro _
      rw [labelledExpr_nil]
      intro M hM _
      have hMnil : M = [] := by
        have hle := hM.length_le
        rw [List.length_nil] at hle
        exact List.length_eq_zero_iff.mp (by omega)
      rw [hMnil, List.map_nil]
      exact FreeGroup.IsReduced.nil
  | cons xs e ih =>
      obtain ⟨x, s⟩ := xs
      intro hred
      rw [labelledExpr_cons]
      refine factorsReduced_append
        (factorsReduced_labelledFactor k (hred (x, s) List.mem_cons_self))
        (ih (k + 1) fun q hq => hred q (List.mem_cons_of_mem _ hq)) ?_
      intro y hy z hz
      obtain ⟨j, hj, hzj⟩ := factor_mem_of_mem_map_labelledExpr (k + 1) e
        ((z.2).factor) (List.mem_map_of_mem hz)
      rw [factor_eq_of_mem_map_labelledFactor (List.mem_map_of_mem hy), hzj]
      intro hEq
      have hkj : k = j := Option.some.inj hEq
      omega

/-- **The labelled word has reduced factors.**  Only the palindromic hypothesis
on the expression and reducedness of the target word are read. -/
theorem factorsReduced_labelledWord [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hred : ∀ q ∈ e, FreeGroup.IsReduced
      (q.1.toWord ++ (q.2 ++ FreeGroup.invRev q.1.toWord)))
    (hw : FreeGroup.IsReduced w) : FactorsReduced (labelledWord e w) := by
  rw [labelledWord]
  refine factorsReduced_append (factorsReduced_labelledExpr 0 e hred)
    (factorsReduced_tag _ (isReduced_invRev_iff.mpr hw)) ?_
  intro x hx y hy
  obtain ⟨j, -, hxj⟩ := factor_mem_of_mem_map_labelledExpr 0 e ((x.2).factor)
    (List.mem_map_of_mem hx)
  rw [hxj, factor_eq_none_of_mem_map_tag_boundary (List.mem_map_of_mem hy)]
  exact Option.some_ne_none j

/-! ## 4.  The theorem -/

/-- **No matched pair has both ends in one factor.**

The two ends of a matched pair never carry the same factor index, and never both
carry the boundary.  Read on the cactus: no stem cancels against itself, against
the disc it carries, or against its own mirror copy.

The only inputs are that each factor is a reduced palindrome and that `w` is
reduced.  No small cancellation, no metric condition, no minimality. -/
theorem factor_ne_of_mem_pairs_labelledWord [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hred : ∀ q ∈ e, FreeGroup.IsReduced
      (q.1.toWord ++ (q.2 ++ FreeGroup.invRev q.1.toWord)))
    (hw : FreeGroup.IsReduced w)
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, ((p.1).2).factor ≠ ((p.2).2).factor := by
  refine blk_ne_of_mem_pairs (ℓ := Prod.fst) (blk := fun z => (z.2).factor) T
    hmatch ?_ ?_
  · rw [hT]
    exact grouped_map_factor_labelledWord e w
  · intro M hM hconst
    rw [hT] at hM
    exact factorsReduced_labelledWord hred hw M hM hconst

/-- The same, read off `PalindromicMinimalExpr.IsPalindromicExpr` — which
`exists_palindromic_isMinimalConjExpr_all` makes free for a minimal
expression. -/
theorem factor_ne_of_isPalindromicExpr [DecidableEq α]
    {e : List (FreeGroup α × List (α × Bool))} {w : List (α × Bool)}
    (hpal : IsPalindromicExpr e) (hw : FreeGroup.IsReduced w)
    {T : DTree ((α × Bool) × Block)} (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, ((p.1).2).factor ≠ ((p.2).2).factor :=
  factor_ne_of_mem_pairs_labelledWord
    (fun _ hq => isReduced_factorWord_of_isPalindromicExpr hpal hq) hw hT hmatch

/-! ## 5.  What it says about the stems -/

section Consequences

variable [DecidableEq α] {e : List (FreeGroup α × List (α × Bool))}
  {w : List (α × Bool)} {T : DTree ((α × Bool) × Block)}

/-- **The two sides of a stem never meet.**  A letter of `cₖ` is never matched to
its mirror in `invRev cₖ`, in either orientation. -/
theorem conj_ne_stem_pair (hpal : IsPalindromicExpr e) (hw : FreeGroup.IsReduced w)
    (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, ∀ k : ℕ,
      ¬ ((p.1).2 = Block.conj k ∧ (p.2).2 = Block.stem k) := by
  intro p hp k ⟨h1, h2⟩
  exact factor_ne_of_isPalindromicExpr hpal hw hT hmatch p hp (by rw [h1, h2]; rfl)

/-- **A stem never meets the disc it carries.**  A letter of `cₖ` is never
matched to a letter of `tₖ`. -/
theorem conj_ne_relator_pair (hpal : IsPalindromicExpr e)
    (hw : FreeGroup.IsReduced w) (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, ∀ k : ℕ,
      ¬ ((p.1).2 = Block.conj k ∧ (p.2).2 = Block.relator k) := by
  intro p hp k ⟨h1, h2⟩
  exact factor_ne_of_isPalindromicExpr hpal hw hT hmatch p hp (by rw [h1, h2]; rfl)

/-- **A disc never meets the mirror of its own stem.** -/
theorem relator_ne_stem_pair (hpal : IsPalindromicExpr e)
    (hw : FreeGroup.IsReduced w) (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, ∀ k : ℕ,
      ¬ ((p.1).2 = Block.relator k ∧ (p.2).2 = Block.stem k) := by
  intro p hp k ⟨h1, h2⟩
  exact factor_ne_of_isPalindromicExpr hpal hw hT hmatch p hp (by rw [h1, h2]; rfl)

/-- **The boundary block still does not cancel against itself**, now by the
factor route: two boundary letters both carry `none`.

`MatchingBoundaryBlock.not_boundary_pair` proves the same at a different price —
reducedness of `w` alone, with nothing asked of the expression. -/
theorem not_boundary_pair_of_isPalindromicExpr (hpal : IsPalindromicExpr e)
    (hw : FreeGroup.IsReduced w) (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, ¬ ((p.1).2 = Block.boundary ∧ (p.2).2 = Block.boundary) := by
  intro p hp ⟨h1, h2⟩
  exact factor_ne_of_isPalindromicExpr hpal hw hT hmatch p hp (by rw [h1, h2])

/-- **A conjugator letter is matched outside its own factor.**  Stated as the
count consumes it: whichever block the far end carries, its factor index is not
`k`. -/
theorem factor_ne_some_of_mem_pairs (hpal : IsPalindromicExpr e)
    (hw : FreeGroup.IsReduced w) (hT : T.word = labelledWord e w)
    (hmatch : ∀ p ∈ T.pairs, (p.2).1 = invLetter ((p.1).1)) :
    ∀ p ∈ T.pairs, ∀ k : ℕ,
      ((p.1).2).factor = some k → ((p.2).2).factor ≠ some k := by
  intro p hp k h1 h2
  exact factor_ne_of_isPalindromicExpr hpal hw hT hmatch p hp (by rw [h1, h2])

end Consequences

end SmallCancellationRouter
end GroupApproximation
