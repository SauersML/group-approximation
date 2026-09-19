import GroupApproximation.Sofic.GreendlingerDehnSwap

/-!
# The residual overlap, measured and restated

`GreendlingerDehnSwap` leaves the whole Dehn-rewriting route resting on one
configuration, `PieceOverlapRight`: a swap destroying `u = γ ++ σ` along
`r = (γ ++ σ) ++ v`, a first Dehn step destroying `u₂ = σ ++ τ` along
`r₂ = (σ ++ τ) ++ v₂`, the two overlapping in a piece `σ`, and the stall
`2|τ| ≤ |r₂|`.  This file takes that configuration apart with the tools the
rewriting system already has, and reports what is and is not reachable that way.

## What is proved outright

* `pieceOverlap_regime` --- **the stall pins the three arms of `r₂`.**  The piece
  bound, the step's own length condition and `2|τ| ≤ |r₂|` together force
  `σ ≠ []`, `2|σ| < |τ|`, `2|σ| < |v₂|`, and both `|r₂| < 3|τ|` and
  `|r₂| < 3|v₂|`.  So the far arm and the tail of the step's relator each occupy
  strictly between a third and a half of it, and the overlap strictly less than a
  sixth --- the crossing the module header of `GreendlingerDehnCritical`
  describes, here as five `ℕ` inequalities inside `omega`'s reach.
* `dehnStep_to_stepOutput`, `dehnSwap_to_swapOutput` --- the two moves out of the
  word `W = A ++ (γ ++ σ) ++ (τ ++ B)` both configurations come from, rebuilt
  from the configuration's own data.
* `dehnReducible_source_of_stepOutput` --- **the hypothesis upgrades for free.**
  The step's output reaches `W` by a *lengthening* swap, because the step's own
  length condition `|v₂| < |σ ++ τ|` says exactly that the swap back is a Dehn
  step; so reducibility of the step's output already carries reducibility of `W`.
  The `r₂` data of the configuration is spent by this one lemma and buys nothing
  else.
* `dehnReducible_middle_of_stepOutput` --- the word
  `Y = A ++ invRev v ++ invRev (v₂ ++ σ) ++ B` through which both routes run is
  reducible whenever `|γ| < |σ ++ v|`, again because the swap onto it lengthens.
* `dehnStep_of_shared_first_letter` --- the one first move the swapped word can
  carry on its own: if `v` and `τ` begin with the same letter, so that the
  overlap was not maximal, the junction of the swapped word cancels.

## What the swapped word does not have

`no_dehn_step_at_far_arm` and `no_dehn_step_at_replacement` are the two halves of
the stall, stated as what they are: in this regime *neither* occurrence visible
in the swapped word `G = A ++ invRev v ++ τ ++ B` carries a Dehn step.  The far
arm `τ` fails by `2|τ| ≤ |r₂|`, which is the residual's own hypothesis, and the
inserted block `invRev v` fails by `|v| ≤ |γ ++ σ|`, which is the hypothesis that
the swap does not lengthen.  Having `Y` reducible does not help either, since the
move from `G` to `Y` lengthens in exactly this regime; that is the stall.

`PieceOverlapFirstStep` is the residual restated as precisely what is missing ---
a first move for `G` --- and `pieceOverlapRight_iff_firstStep` shows the
restatement is faithful, the far arm being nonempty by `pieceOverlap_regime`.

## What the residual weighs

`pieceOverlapRight_of_dehnSwapClosed` runs the free upgrade once more and lands
`PieceOverlapRight` from swap closure; with `dehnSwapClosed_of_pieceOverlap` in
the other direction this gives `pieceOverlapRight_iff_dehnSwapClosed`:

  **for a `C'(1/6)` family of cyclically reduced relators, the residual overlap
  is equivalent to full swap closure.**

So the critical-pair analysis of `GreendlingerDehnCritical` and
`GreendlingerDehnSwap` is a reduction of the *configuration* --- one overlap of
two distinct relators instead of a whole theorem --- and not a reduction of the
logical strength.  Any proof of `PieceOverlapRight` must supply a first move for
a word that has none locally, which is to say it must reach outside the
configuration, into how the derivation of the step's output meets the context
`A` and `B`.

Unconditional except where `MetricSmallCancellation` is named, and except for the
two closure statements the equivalence quotes.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## The arithmetic of the stalled regime -/

/-- **The stall, in `ℕ`.**  Writing `s`, `t`, `c` for the lengths of the overlap,
the far arm and the tail of the step's relator, the piece bound `6s < s + t + c`,
the step's length condition `c < s + t` and the stall `2t ≤ s + t + c` force the
overlap to be nonempty and each of the other two arms to exceed twice it, and
they pin both arms strictly between a third and a half of the relator. -/
theorem stalled_regime {s t c : ℕ} (h6 : 6 * s < s + t + c) (hstep : c < s + t)
    (hstall : 2 * t ≤ s + t + c) :
    0 < s ∧ 2 * s < t ∧ 2 * s < c ∧ s + t + c < 3 * t ∧ s + t + c < 3 * c := by
  omega

/-- **The stall, on the words of the configuration.**  `stalled_regime` read off
the three length hypotheses `PieceOverlapRight` carries. -/
theorem pieceOverlap_regime {σ τ v₂ : List (α × Bool)}
    (h6 : 6 * σ.length < ((σ ++ τ) ++ v₂).length)
    (hv₂ : v₂.length < (σ ++ τ).length)
    (hstall : 2 * τ.length ≤ ((σ ++ τ) ++ v₂).length) :
    0 < σ.length ∧ 2 * σ.length < τ.length ∧ 2 * σ.length < v₂.length ∧
      ((σ ++ τ) ++ v₂).length < 3 * τ.length ∧
      ((σ ++ τ) ++ v₂).length < 3 * v₂.length := by
  simp only [List.length_append] at h6 hv₂ hstall ⊢
  omega

/-- The overlap of the residual configuration is nonempty.  `occurrence_cases`
supplies this at the call site and the residual statement drops it; the length
conditions give it back. -/
theorem pieceOverlap_overlap_ne_nil {σ τ v₂ : List (α × Bool)}
    (h6 : 6 * σ.length < ((σ ++ τ) ++ v₂).length)
    (hv₂ : v₂.length < (σ ++ τ).length)
    (hstall : 2 * τ.length ≤ ((σ ++ τ) ++ v₂).length) : σ ≠ [] := by
  intro hnil
  have hpos := (pieceOverlap_regime h6 hv₂ hstall).1
  rw [hnil, List.length_nil] at hpos
  omega

/-- The far arm of the residual configuration is nonempty --- it is more than
twice the overlap, which is itself nonempty.  This is what makes the swapped word
of the configuration nonempty, and so what makes `PieceOverlapFirstStep` a
faithful restatement. -/
theorem pieceOverlap_far_arm_ne_nil {σ τ v₂ : List (α × Bool)}
    (h6 : 6 * σ.length < ((σ ++ τ) ++ v₂).length)
    (hv₂ : v₂.length < (σ ++ τ).length)
    (hstall : 2 * τ.length ≤ ((σ ++ τ) ++ v₂).length) : τ ≠ [] := by
  intro hnil
  have hb := (pieceOverlap_regime h6 hv₂ hstall).2.1
  rw [hnil, List.length_nil] at hb
  omega

/-- The tail of the step's relator is nonempty, for the same reason. -/
theorem pieceOverlap_tail_ne_nil {σ τ v₂ : List (α × Bool)}
    (h6 : 6 * σ.length < ((σ ++ τ) ++ v₂).length)
    (hv₂ : v₂.length < (σ ++ τ).length)
    (hstall : 2 * τ.length ≤ ((σ ++ τ) ++ v₂).length) : v₂ ≠ [] := by
  intro hnil
  have hb := (pieceOverlap_regime h6 hv₂ hstall).2.2.1
  rw [hnil, List.length_nil] at hb
  omega

/-! ## The two moves out of the word both configurations come from -/

/-- **The step of the configuration.**  The word `W = A ++ (γ ++ σ) ++ (τ ++ B)`
takes the Dehn step that destroys `σ ++ τ`; its output is the word the residual
assumes reducible. -/
theorem dehnStep_to_stepOutput {R : Set (List (α × Bool))}
    {σ τ v₂ : List (α × Bool)} (hr₂ : (σ ++ τ) ++ v₂ ∈ symmetrization R)
    (hv₂ : v₂.length < (σ ++ τ).length) (A γ B : List (α × Bool)) :
    DehnStep R (A ++ ((γ ++ σ) ++ (τ ++ B)))
      ((A ++ γ) ++ (FreeGroup.invRev v₂ ++ B)) := by
  have hlong : ((σ ++ τ) ++ v₂).length < 2 * (σ ++ τ).length := by
    simp only [List.length_append] at hv₂ ⊢
    omega
  have hb := DehnStep.dehn (A ++ γ) B (σ ++ τ) v₂ ((σ ++ τ) ++ v₂) hr₂ rfl hlong
  simpa only [List.append_assoc] using hb

/-- **The swap of the configuration.**  The same word takes the swap that
destroys `γ ++ σ`; its output is the word the residual has to reach. -/
theorem dehnSwap_to_swapOutput {R : Set (List (α × Bool))}
    {γ σ v : List (α × Bool)} (hr : (γ ++ σ) ++ v ∈ symmetrization R)
    (A τ B : List (α × Bool)) :
    DehnSwap R (A ++ ((γ ++ σ) ++ (τ ++ B)))
      (A ++ (FreeGroup.invRev v ++ (τ ++ B))) :=
  ⟨A, τ ++ B, γ ++ σ, v, (γ ++ σ) ++ v, hr, rfl, rfl, rfl⟩

/-! ## What the step's output already gives -/

/-- **The residual's hypothesis upgrades for free.**  The step's length condition
`|v₂| < |σ ++ τ|` says exactly that the swap carrying the step's output back to
`W` lengthens, so that swap is a Dehn step read forwards and reducibility of the
step's output carries reducibility of `W`.

This is the whole content the `r₂` data of the configuration has: the residual is
not a statement about a step and a swap meeting, but a statement about the swap
alone, at a word already known reducible. -/
theorem dehnReducible_source_of_stepOutput {R : Set (List (α × Bool))}
    {σ τ v₂ : List (α × Bool)} (hr₂ : (σ ++ τ) ++ v₂ ∈ symmetrization R)
    (hv₂ : v₂.length < (σ ++ τ).length) (A γ B : List (α × Bool))
    (hW : DehnReducible R ((A ++ γ) ++ (FreeGroup.invRev v₂ ++ B))) :
    DehnReducible R (A ++ ((γ ++ σ) ++ (τ ++ B))) :=
  Relation.ReflTransGen.head (dehnStep_to_stepOutput hr₂ hv₂ A γ B) hW

/-- The two spellings of the word both routes out of the configuration run
through. -/
theorem middleWord_shape (A v σ v₂ B : List (α × Bool)) :
    A ++ (FreeGroup.invRev (σ ++ v) ++ (FreeGroup.invRev v₂ ++ B))
      = A ++ (FreeGroup.invRev v ++ (FreeGroup.invRev (v₂ ++ σ) ++ B)) := by
  rw [FreeGroup.invRev_append, FreeGroup.invRev_append]
  simp only [List.append_assoc]

/-- **The middle word is reducible when the front arm is short.**  The swap
`dehnSwap_of_middle_step` carries the step's output onto
`Y = A ++ invRev v ++ invRev (v₂ ++ σ) ++ B`; if `|γ| < |σ ++ v|` that swap
lengthens, so `Y` inherits reducibility with no closure hypothesis at all.

It does not close the residual: reaching the swapped word from `Y` asks for a
Dehn step at the far arm, and `no_dehn_step_at_far_arm` says the stall is exactly
the failure of that step. -/
theorem dehnReducible_middle_of_stepOutput {R : Set (List (α × Bool))}
    {γ σ v : List (α × Bool)} (hr : (γ ++ σ) ++ v ∈ symmetrization R)
    (hshort : γ.length < (σ ++ v).length) (A v₂ B : List (α × Bool))
    (hW : DehnReducible R ((A ++ γ) ++ (FreeGroup.invRev v₂ ++ B))) :
    DehnReducible R
      (A ++ (FreeGroup.invRev v ++ (FreeGroup.invRev (v₂ ++ σ) ++ B))) := by
  have hmem : γ ++ (σ ++ v) ∈ symmetrization R := by
    rwa [List.append_assoc] at hr
  have hsplit : γ ++ (σ ++ v) = γ ++ (σ ++ v) := rfl
  have hW' : DehnReducible R (A ++ (γ ++ (FreeGroup.invRev v₂ ++ B))) := by
    simpa only [List.append_assoc] using hW
  have hb := dehnReducible_of_swap_of_lt hmem hsplit hshort hW'
  rwa [middleWord_shape] at hb

/-! ## What the swapped word does not have -/

/-- **The far arm carries no step.**  The stall `2|τ| ≤ |r₂|` is precisely the
failure of the Dehn condition at the occurrence of `τ` in the swapped word. -/
theorem no_dehn_step_at_far_arm {σ τ v₂ : List (α × Bool)}
    (hstall : 2 * τ.length ≤ ((σ ++ τ) ++ v₂).length) :
    ¬ ((σ ++ τ) ++ v₂).length < 2 * τ.length := by
  simp only [List.length_append] at hstall ⊢
  omega

/-- **The inserted block carries no step either.**  A swap that does not lengthen
inserts at most half of its own relator, so the block it inserts never satisfies
the Dehn condition.  With `no_dehn_step_at_far_arm` this is the stall: the two
occurrences the residual configuration puts in the swapped word are the only ones
it knows about, and neither moves. -/
theorem no_dehn_step_at_replacement {γ σ v : List (α × Bool)}
    (hle : v.length ≤ (γ ++ σ).length) :
    ¬ ((γ ++ σ) ++ v).length < 2 * (FreeGroup.invRev v).length := by
  simp only [List.length_append, FreeGroup.invRev_length] at hle ⊢
  omega

/-- **The one first move the configuration can supply on its own.**  If the
overlap was not maximal to the right --- the arm `v` of the swap's relator and the
arm `τ` of the step's begin with the same letter --- the swapped word carries a
cancelling pair across the junction and takes a free step.

The enlarged overlap need not stay under the piece bound, so this does not
recurse into the residual; it is recorded because it is the only move the
configuration itself provides. -/
theorem dehnStep_of_shared_first_letter {R : Set (List (α × Bool))}
    (A v' τ' B : List (α × Bool)) (x : α × Bool) :
    DehnStep R (A ++ (FreeGroup.invRev (x :: v') ++ ((x :: τ') ++ B)))
      (A ++ (FreeGroup.invRev v' ++ (τ' ++ B))) := by
  have hb := DehnStep.free (R := R) (A ++ FreeGroup.invRev v') (τ' ++ B)
    (invLetter x)
  rw [invLetter_invLetter] at hb
  have hleft : A ++ (FreeGroup.invRev (x :: v') ++ ((x :: τ') ++ B))
      = (A ++ FreeGroup.invRev v') ++ (invLetter x :: x :: (τ' ++ B)) := by
    rw [invRev_cons]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hright : A ++ (FreeGroup.invRev v' ++ (τ' ++ B))
      = (A ++ FreeGroup.invRev v') ++ (τ' ++ B) := by
    simp only [List.append_assoc]
  rw [hleft, hright]
  exact hb

/-! ## The residual, restated as the move it lacks -/

/-- **The residual overlap, as a first move.**  Identical to `PieceOverlapRight`
except that the conclusion asks only for one Dehn step out of the swapped word
onto a reducible word, rather than for a whole derivation.

The two are the same statement --- `pieceOverlapRight_iff_firstStep` --- because
the far arm of the configuration is nonempty, so the swapped word is nonempty and
a derivation out of it has a first step.  Stating it this way names what the
configuration is missing: `no_dehn_step_at_far_arm` and
`no_dehn_step_at_replacement` say that neither occurrence the configuration knows
about supplies that step. -/
def PieceOverlapFirstStep (R : Set (List (α × Bool))) : Prop :=
  MetricSmallCancellation R (1 / 6) →
  ∀ A γ σ τ v v₂ B : List (α × Bool),
    (γ ++ σ) ++ v ∈ symmetrization R →
    (σ ++ τ) ++ v₂ ∈ symmetrization R →
    6 * σ.length < ((σ ++ τ) ++ v₂).length →
    v.length ≤ (γ ++ σ).length →
    v₂.length < (σ ++ τ).length →
    2 * τ.length ≤ ((σ ++ τ) ++ v₂).length →
    DehnReducible R ((A ++ γ) ++ (FreeGroup.invRev v₂ ++ B)) →
    ∃ Z : List (α × Bool),
      DehnStep R (A ++ (FreeGroup.invRev v ++ (τ ++ B))) Z ∧ DehnReducible R Z

/-- One move and a derivation is a derivation. -/
theorem pieceOverlapRight_of_firstStep {R : Set (List (α × Bool))}
    (h : PieceOverlapFirstStep R) : PieceOverlapRight R := by
  intro hmetric A γ σ τ v v₂ B hr hr₂ h6 hle hv₂ hstall hW
  obtain ⟨Z, hstep, hZ⟩ :=
    h hmetric A γ σ τ v v₂ B hr hr₂ h6 hle hv₂ hstall hW
  exact Relation.ReflTransGen.head hstep hZ

/-- Conversely: the swapped word of the configuration is nonempty, because the
far arm is, so a derivation out of it begins with a step. -/
theorem pieceOverlapFirstStep_of_right {R : Set (List (α × Bool))}
    (h : PieceOverlapRight R) : PieceOverlapFirstStep R := by
  intro hmetric A γ σ τ v v₂ B hr hr₂ h6 hle hv₂ hstall hW
  have hG := h hmetric A γ σ τ v v₂ B hr hr₂ h6 hle hv₂ hstall hW
  rcases Relation.ReflTransGen.cases_head hG with hnil | ⟨Z, hstep, hZ⟩
  · exfalso
    have hpos := (pieceOverlap_regime h6 hv₂ hstall).2.1
    have hlen := congrArg List.length hnil
    simp only [List.length_append, List.length_nil,
      FreeGroup.invRev_length] at hlen
    omega
  · exact ⟨Z, hstep, hZ⟩

/-- **The restatement is faithful.** -/
theorem pieceOverlapRight_iff_firstStep {R : Set (List (α × Bool))} :
    PieceOverlapRight R ↔ PieceOverlapFirstStep R :=
  ⟨pieceOverlapFirstStep_of_right, pieceOverlapRight_of_firstStep⟩

/-- **The gate, from the restated residual.** -/
theorem greendlingerConclusion_of_firstStep [DecidableEq α]
    {R : Set (List (α × Bool))} (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hRne : ∀ r ∈ R, r ≠ []) (hmetric : MetricSmallCancellation R (1 / 6))
    (h : PieceOverlapFirstStep R) : GreendlingerConclusion R :=
  greendlingerConclusion_of_pieceOverlap hR hRne hmetric
    (pieceOverlapRight_of_firstStep h)

/-! ## What the residual weighs -/

/-- **Swap closure gives the residual back.**  Reducibility of the step's output
carries reducibility of the word both moves come from
(`dehnReducible_source_of_stepOutput`), and the swap out of that word is the one
the configuration names, so swap closure applies to it directly. -/
theorem pieceOverlapRight_of_dehnSwapClosed {R : Set (List (α × Bool))}
    (hswap : DehnSwapClosed R) : PieceOverlapRight R := by
  intro _ A γ σ τ v v₂ B hr hr₂ _ _ hv₂ _ hW
  exact hswap _ _ (dehnReducible_source_of_stepOutput hr₂ hv₂ A γ B hW)
    (dehnSwap_to_swapOutput hr A τ B)

/-- The mirror configuration, likewise. -/
theorem pieceOverlapLeft_of_dehnSwapClosed {R : Set (List (α × Bool))}
    (hswap : DehnSwapClosed R) : PieceOverlapLeft R :=
  pieceOverlapLeft_of_right (pieceOverlapRight_of_dehnSwapClosed hswap)

/-- **The residual overlap is exactly swap closure.**  For a `C'(1/6)` family of
cyclically reduced relators the two implications close a circle:
`dehnSwapClosed_of_pieceOverlap` is the critical-pair analysis of
`GreendlingerDehnCritical` and `GreendlingerDehnSwap`, and
`pieceOverlapRight_of_dehnSwapClosed` is one free upgrade.

So that analysis reduces the *configuration* the statement speaks about --- one
overlap of two distinct relators, in one regime, instead of every pair of moves
--- and not its strength.  A proof of the residual has to supply a first move for
a word which, by `no_dehn_step_at_far_arm` and `no_dehn_step_at_replacement`, has
none at either occurrence the configuration names; the move can only come from
how the derivation of the step's output meets the surrounding context.

The circle closes at the swap half only.  `dehnFreeClosed_of_pieceOverlap` sends
the residual to free closure, but nothing here sends free closure back: no
upgrade in the system carries a free reduction into a swap, and
`dehnFreeClosed_of_dehnSwapClosed` runs the other way. -/
theorem pieceOverlapRight_iff_dehnSwapClosed [DecidableEq α]
    {R : Set (List (α × Bool))} (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r)
    (hmetric : MetricSmallCancellation R (1 / 6)) :
    PieceOverlapRight R ↔ DehnSwapClosed R :=
  ⟨fun h => dehnSwapClosed_of_pieceOverlap hR hmetric h,
    pieceOverlapRight_of_dehnSwapClosed⟩

end SmallCancellationRouter
end GroupApproximation
