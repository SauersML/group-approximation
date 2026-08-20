import GroupApproximation.Sofic.GreendlingerDehn

/-!
# The critical pairs of Dehn's algorithm

`GreendlingerDehn` reduces the gate to one statement, `DehnReduceClosed`:
Dehn-reducibility survives free reduction.  This file takes that statement apart
by the standard critical-pair method and discharges every configuration it
splits into except one, so that what small cancellation still has to buy is a
single overlap of two *distinct* relators rather than a whole theorem.

## The two closure statements

Reducibility is asked to survive two elementary moves.

* `DehnFreeClosed` --- a free reduction.  `dehnReduceClosed_of_dehnFreeClosed`
  shows this is exactly `DehnReduceClosed`.
* `DehnSwapClosed` --- a `DehnSwap`: an occurrence of `u` inside the word is
  replaced by `invRev v`, where `r = u ++ v` is *any* split of a symmetrized
  relator.  Unlike a `DehnStep`, a swap carries **no length condition**, so the
  relation is symmetric (`DehnSwap.symm`); it is the move that generates the
  quotient.

The two are entangled: the free statement needs the swap statement (a Dehn step
straddling a cancelling pair becomes a swap of the shortened word), and the swap
statement needs the free one (a Dehn step buried inside a swap's occurrence
produces a word that only *freely* reduces to the swap's output).  Both
recursions descend in word length, because every step of the system shortens its
word, so the two are established together by induction on length --- which is
what `FreeClosedBelow` and `SwapClosedBelow` are for.

## What this file proves

Structural, and unconditional:

* `dehnStep_of_swap_of_lt` and `dehnReducible_of_swap_of_lt` --- **a lengthening
  swap is free.**  If `|u| < |v|` the swap is a Dehn step read backwards, so the
  swapped word reduces to the original in one step and inherits its derivation.
  Every configuration below therefore only has to be settled for swaps with
  `|v| ≤ |u|`, and that is where all the arithmetic lives.
* `DehnStep.invRev`, `DehnReducible.invRev` --- **the system is mirror-
  symmetric.**  Reading a word backwards and inverting every letter carries steps
  to steps: a Dehn step because `symmetrization` is closed under rotation and
  formal inversion, a free step because a cancelling pair inverts to a cancelling
  pair.  This halves every case analysis, since the two ways a configuration can
  straddle an occurrence are mirror images.
* `redStep_of_pair`, `dehnStep_of_redStep`, `dehnRed_of_red` --- the free rule of
  this system *is* Mathlib's reduction step, in both directions.
* `red_cancel_block`, `red_conjugate_cancel` --- the free reductions the buried
  cases produce.
* `DehnReducible.conj` --- reducibility survives conjugation by a word.

Discharged configurations, each a lemma that consumes exactly the data the
critical pair provides:

* `dehnSwap_of_straddle_right`, `dehnSwap_of_straddle_left` --- **a free step at
  the edge of a swap's occurrence is again a swap.**  The pair deletes the last
  letter of `u`; putting that letter at the front of `v` is the same relator
  split one place earlier (right), or the relator rotated by one letter (left).
  No hypothesis, and no length condition --- which is the reason the swap
  relation was defined without one: for a *step* this passage fails by exactly
  the two letters that the boundary case of the naive analysis stalls on.
* `dehnReducible_of_outer_step` --- **a Dehn step whose occurrence swallows the
  swap's is the swap's own relator.**  `C'(1/6)` forces it
  (`eq_rotate_of_occurrence`), the complement is read off
  (`tail_eq_of_eq_rotate`), and then the swapped word reduces to the step's
  output by free cancellation alone.  This case closes outright, with no appeal
  to any induction hypothesis.
* `red_of_inner_step` --- **a Dehn step buried inside the swap's occurrence is
  again the swap's own relator**, and there the step's output *freely* reduces to
  the swap's output.  This is the case that needs `FreeClosedBelow`, and nothing
  else.
* `dehnStep_of_middle_occurrence` and `dehnSwap_of_middle_step` --- the partial
  overlap, in the regime where the part of the step's occurrence lying beyond the
  swap's is more than half of the step's relator.  There the swapped word takes a
  Dehn step of its own onto the swap of the step's output, so the case closes
  from `SwapClosedBelow`.

## What is left, stated exactly

`PieceOverlapRight`: the swap's occurrence `u = γ ++ σ` and the step's
occurrence `u₂ = σ ++ τ` overlap in `σ`, the two relators are distinct, so `σ` is
a piece and `C'(1/6)` bounds it by a sixth --- and `2|τ| ≤ |r₂|`.  Both routes out
of it run through the word

  `Y = A ++ invRev v ++ invRev σ ++ invRev v₂ ++ B₁`,

which is at once the swap of the step's output and the step of the swap's output;
but `|Y| - |W| = 2|σ| - (|u| - |v|) - (|u₂| - |v₂|)`, and in this regime the two
deficits together are at most `2|σ|`, so `Y` is not shorter than `W` and the
descent on length stalls.  That is the same crossing --- five twelfths kept
against seven twelfths eaten --- that `Sofic/GreendlingerThreeFactor` records for
the descent, reached here with no palindromes, no minimal expressions and no
weight.

The mirror configuration, `PieceOverlapLeft`, is not a second residual:
`pieceOverlapLeft_of_right` derives it, because reducibility is mirror-symmetric
and the six length conditions are symmetric in the two arms of the overlap.  So
one statement is what the gate rests on.

Unconditional except where `MetricSmallCancellation` is named.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## Swaps: the Dehn move with its length condition dropped -/

/-- **A relator swap.**  An occurrence of `u` is replaced by `invRev v`, where
`r = u ++ v` is any split of a symmetrized relator.  A `DehnStep` is the special
case `|v| < |u|`; dropping the condition makes the relation symmetric, and the
symmetry is what the critical-pair analysis spends. -/
def DehnSwap (R : Set (List (α × Bool))) (W G : List (α × Bool)) : Prop :=
  ∃ A B u v r : List (α × Bool), r ∈ symmetrization R ∧ r = u ++ v ∧
    W = A ++ (u ++ B) ∧ G = A ++ (FreeGroup.invRev v ++ B)

/-- **Swapping is symmetric.**  Reading the split backwards inverts the relator,
and `symmetrization` is closed under formal inversion. -/
theorem DehnSwap.symm {R : Set (List (α × Bool))} {W G : List (α × Bool)}
    (h : DehnSwap R W G) : DehnSwap R G W := by
  obtain ⟨A, B, u, v, r, hr, hsplit, hW, hG⟩ := h
  refine ⟨A, B, FreeGroup.invRev v, FreeGroup.invRev u, FreeGroup.invRev r,
    invRev_mem_symmetrization hr, ?_, hG, ?_⟩
  · rw [hsplit, FreeGroup.invRev_append]
  · rw [FreeGroup.invRev_invRev, hW]

/-- **A lengthening swap is a step backwards.**  If the destroyed block is
shorter than what replaces it, the inverse relator rewrites the replacement back
to the block, and that rewriting *is* a Dehn step. -/
theorem dehnStep_of_swap_of_lt {R : Set (List (α × Bool))}
    {A B u v r : List (α × Bool)} (hr : r ∈ symmetrization R) (hsplit : r = u ++ v)
    (hshort : u.length < v.length) :
    DehnStep R (A ++ (FreeGroup.invRev v ++ B)) (A ++ (u ++ B)) := by
  have hinv : FreeGroup.invRev r = FreeGroup.invRev v ++ FreeGroup.invRev u := by
    rw [hsplit, FreeGroup.invRev_append]
  have hmem : FreeGroup.invRev r ∈ symmetrization R := invRev_mem_symmetrization hr
  have hlen : (FreeGroup.invRev r).length < 2 * (FreeGroup.invRev v).length := by
    rw [FreeGroup.invRev_length, FreeGroup.invRev_length, hsplit, List.length_append]
    omega
  have hstep := DehnStep.dehn A B (FreeGroup.invRev v) (FreeGroup.invRev u)
    (FreeGroup.invRev r) hmem hinv hlen
  rwa [FreeGroup.invRev_invRev] at hstep

/-- **The trivial half of the swap closure.**  A swap that lengthens carries
reducibility for free: the swapped word reaches the original in one step. -/
theorem dehnReducible_of_swap_of_lt {R : Set (List (α × Bool))}
    {A B u v r : List (α × Bool)} (hr : r ∈ symmetrization R) (hsplit : r = u ++ v)
    (hshort : u.length < v.length) (h : DehnReducible R (A ++ (u ++ B))) :
    DehnReducible R (A ++ (FreeGroup.invRev v ++ B)) :=
  Relation.ReflTransGen.head (dehnStep_of_swap_of_lt hr hsplit hshort) h

/-! ## The free rule is Mathlib's reduction step -/

/-- Deleting a cancelling pair is Mathlib's reduction step, so the diamond lemma
for free reduction applies to the free rule of this system. -/
theorem redStep_of_pair (A B : List (α × Bool)) (x : α × Bool) :
    FreeGroup.Red.Step (A ++ (x :: invLetter x :: B)) (A ++ B) := by
  obtain ⟨x₁, xb⟩ := x
  exact FreeGroup.Red.Step.not

/-- Conversely, Mathlib's reduction step is a step of this system. -/
theorem dehnStep_of_redStep {R : Set (List (α × Bool))} {W W' : List (α × Bool)}
    (h : FreeGroup.Red.Step W W') : DehnStep R W W' := by
  cases h with
  | @not L₁ L₂ z zb => exact DehnStep.free L₁ L₂ (z, zb)

/-- A free reduction is a derivation of the system. -/
theorem dehnRed_of_red {R : Set (List (α × Bool))} {W V : List (α × Bool)}
    (h : FreeGroup.Red W V) : Relation.ReflTransGen (DehnStep R) W V := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (dehnStep_of_redStep hbc)

/-! ## The system is mirror-symmetric -/

/-- **A step, read backwards.**  Inverting a cancelling pair gives a cancelling
pair, and inverting a relator occurrence gives an occurrence of the inverted
relator rotated --- both members of the symmetrization. -/
theorem DehnStep.invRev {R : Set (List (α × Bool))} {W W' : List (α × Bool)}
    (h : DehnStep R W W') :
    DehnStep R (FreeGroup.invRev W) (FreeGroup.invRev W') := by
  cases h with
  | free A B x =>
      have hleft : FreeGroup.invRev (A ++ (x :: invLetter x :: B))
          = FreeGroup.invRev B ++ (x :: invLetter x :: FreeGroup.invRev A) := by
        rw [FreeGroup.invRev_append, invRev_cons, invRev_cons, invLetter_invLetter]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have hright : FreeGroup.invRev (A ++ B)
          = FreeGroup.invRev B ++ FreeGroup.invRev A := FreeGroup.invRev_append
      rw [hleft, hright]
      exact DehnStep.free (FreeGroup.invRev B) (FreeGroup.invRev A) x
  | dehn A B u v r hr hsplit hlong =>
      have hrot : v ++ u ∈ symmetrization R := by
        rw [hsplit] at hr
        exact append_swap_mem_symmetrization hr
      have hmem : FreeGroup.invRev u ++ FreeGroup.invRev v ∈ symmetrization R := by
        have hb := invRev_mem_symmetrization hrot
        rwa [FreeGroup.invRev_append] at hb
      have hlen : (FreeGroup.invRev u ++ FreeGroup.invRev v).length
          < 2 * (FreeGroup.invRev u).length := by
        rw [List.length_append, FreeGroup.invRev_length, FreeGroup.invRev_length]
        rw [hsplit, List.length_append] at hlong
        omega
      have hstep := DehnStep.dehn (FreeGroup.invRev B) (FreeGroup.invRev A)
        (FreeGroup.invRev u) (FreeGroup.invRev v)
        (FreeGroup.invRev u ++ FreeGroup.invRev v) hmem rfl hlen
      rw [FreeGroup.invRev_invRev] at hstep
      have hleft : FreeGroup.invRev (A ++ (u ++ B))
          = FreeGroup.invRev B ++ (FreeGroup.invRev u ++ FreeGroup.invRev A) := by
        rw [FreeGroup.invRev_append, FreeGroup.invRev_append]
        simp only [List.append_assoc]
      have hright : FreeGroup.invRev (A ++ (FreeGroup.invRev v ++ B))
          = FreeGroup.invRev B ++ (v ++ FreeGroup.invRev A) := by
        rw [FreeGroup.invRev_append, FreeGroup.invRev_append, FreeGroup.invRev_invRev]
        simp only [List.append_assoc]
      rw [hleft, hright]
      exact hstep

/-- A whole derivation, read backwards. -/
theorem dehnRed_invRev {R : Set (List (α × Bool))} :
    ∀ {W V : List (α × Bool)}, Relation.ReflTransGen (DehnStep R) W V →
      Relation.ReflTransGen (DehnStep R) (FreeGroup.invRev W) (FreeGroup.invRev V) := by
  intro W V h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail hbc.invRev

/-- **Reducibility is mirror-symmetric.**  Every configuration below therefore
has to be settled on one side of the occurrence only. -/
theorem DehnReducible.invRev {R : Set (List (α × Bool))} {W : List (α × Bool)}
    (h : DehnReducible R W) : DehnReducible R (FreeGroup.invRev W) := by
  have hb := dehnRed_invRev h
  rwa [invRev_nil] at hb

/-- The mirror read backwards: formal inversion is an involution on words, so it
carries reducibility both ways. -/
theorem DehnReducible.of_invRev {R : Set (List (α × Bool))} {W : List (α × Bool)}
    (h : DehnReducible R (FreeGroup.invRev W)) : DehnReducible R W := by
  have hb := h.invRev
  rwa [FreeGroup.invRev_invRev] at hb

/-! ## The free reductions the buried cases produce -/

/-- Deleting a block against its own inverse, as a free reduction, in any
context. -/
theorem red_cancel_block : ∀ Y X Z : List (α × Bool),
    FreeGroup.Red (X ++ (Y ++ FreeGroup.invRev Y) ++ Z) (X ++ Z) := by
  intro Y
  induction Y with
  | nil =>
      intro X Z
      have hnil : X ++ (([] : List (α × Bool)) ++ FreeGroup.invRev
          ([] : List (α × Bool))) ++ Z = X ++ Z := by
        simp
      rw [hnil]
  | cons w Y' ih =>
      intro X Z
      have hshape : X ++ ((w :: Y') ++ FreeGroup.invRev (w :: Y')) ++ Z
          = (X ++ [w]) ++ (Y' ++ FreeGroup.invRev Y') ++ ([invLetter w] ++ Z) := by
        rw [invRev_cons]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have hshape2 : (X ++ [w]) ++ ([invLetter w] ++ Z)
          = X ++ (w :: invLetter w :: Z) := by
        simp only [List.append_assoc, List.singleton_append]
      rw [hshape]
      refine (ih (X ++ [w]) ([invLetter w] ++ Z)).trans ?_
      rw [hshape2]
      exact (redStep_of_pair X Z w).to_red

/-- The same, with the inverse in front. -/
theorem red_cancel_block' (Y X Z : List (α × Bool)) :
    FreeGroup.Red (X ++ (FreeGroup.invRev Y ++ Y) ++ Z) (X ++ Z) := by
  have hb := red_cancel_block (FreeGroup.invRev Y) X Z
  rwa [FreeGroup.invRev_invRev] at hb

/-- **The cancellation a same-relator overlap leaves behind.**  When a Dehn step
and a swap rewrite along one and the same relator, the two outputs differ by a
stem against its inverse on each side, and free reduction alone closes the gap.

Both buried configurations --- the step inside the swap's occurrence and the swap
inside the step's --- produce exactly this word, with the roles of the two stems
exchanged, so one identity settles both. -/
theorem red_conjugate_cancel (X Y m Z W : List (α × Bool)) :
    FreeGroup.Red (X ++ (Y ++ (FreeGroup.invRev (Z ++ (m ++ Y)) ++ (Z ++ W))))
      (X ++ (FreeGroup.invRev m ++ W)) := by
  have hexp : X ++ (Y ++ (FreeGroup.invRev (Z ++ (m ++ Y)) ++ (Z ++ W)))
      = X ++ (Y ++ FreeGroup.invRev Y)
          ++ (FreeGroup.invRev m ++ (FreeGroup.invRev Z ++ (Z ++ W))) := by
    rw [FreeGroup.invRev_append, FreeGroup.invRev_append]
    simp only [List.append_assoc]
  have hmid : X ++ (FreeGroup.invRev m ++ (FreeGroup.invRev Z ++ (Z ++ W)))
      = X ++ FreeGroup.invRev m ++ (FreeGroup.invRev Z ++ Z) ++ W := by
    simp only [List.append_assoc]
  have hend : X ++ FreeGroup.invRev m ++ W = X ++ (FreeGroup.invRev m ++ W) := by
    simp only [List.append_assoc]
  rw [hexp]
  refine (red_cancel_block Y X
    (FreeGroup.invRev m ++ (FreeGroup.invRev Z ++ (Z ++ W)))).trans ?_
  rw [hmid, ← hend]
  exact red_cancel_block' Z (X ++ FreeGroup.invRev m) W

/-- The same cancellation, read as a derivation of the system. -/
theorem dehnRed_cancel_block (R : Set (List (α × Bool))) (X Y Z : List (α × Bool)) :
    Relation.ReflTransGen (DehnStep R) (X ++ (Y ++ FreeGroup.invRev Y) ++ Z)
      (X ++ Z) :=
  dehnRed_of_red (red_cancel_block Y X Z)

/-- Reducibility survives conjugation by a word: the stem cancels itself. -/
theorem DehnReducible.conj {R : Set (List (α × Bool))} {W : List (α × Bool)}
    (h : DehnReducible R W) (c : List (α × Bool)) :
    DehnReducible R (c ++ W ++ FreeGroup.invRev c) := by
  refine (dehnDerivation_context h c (FreeGroup.invRev c)).trans ?_
  rw [List.append_nil]
  exact dehnReducible_append_invRev R c

/-! ## A free step at the edge of a swap's occurrence -/

/-- Moving the last letter of the destroyed block to the front of what replaces
it is the same relator, split one place earlier. -/
theorem mem_symmetrization_shift_right {R : Set (List (α × Bool))} {y : α × Bool}
    {u v : List (α × Bool)} (h : (u ++ [y]) ++ v ∈ symmetrization R) :
    u ++ (y :: v) ∈ symmetrization R := by
  rwa [List.append_assoc, List.singleton_append] at h

/-- Moving the first letter of the destroyed block to the end of what replaces
it is the same relator, rotated by one letter. -/
theorem mem_symmetrization_shift_left {R : Set (List (α × Bool))} {y : α × Bool}
    {u v : List (α × Bool)} (h : (y :: u) ++ v ∈ symmetrization R) :
    u ++ (v ++ [y]) ∈ symmetrization R := by
  have h1 : [y] ++ (u ++ v) ∈ symmetrization R := by
    rw [List.singleton_append, ← List.cons_append]
    exact h
  have h2 := append_swap_mem_symmetrization h1
  rwa [List.append_assoc] at h2

/-- **A free step at the right edge of a swap's occurrence is again a swap.**
The cancelling pair takes the last letter of the destroyed block with it; the
shortened word swaps to the very same result, along the same relator split one
letter earlier. -/
theorem dehnSwap_of_straddle_right {R : Set (List (α × Bool))}
    {A u v B : List (α × Bool)} {y : α × Bool}
    (hr : (u ++ [y]) ++ v ∈ symmetrization R) :
    DehnSwap R (A ++ (u ++ B))
      (A ++ (FreeGroup.invRev v ++ (invLetter y :: B))) := by
  refine ⟨A, B, u, y :: v, u ++ (y :: v), mem_symmetrization_shift_right hr, rfl,
    rfl, ?_⟩
  rw [invRev_cons]
  simp only [List.append_assoc, List.singleton_append]

/-- **A free step at the left edge of a swap's occurrence is again a swap**, along
the relator rotated by the letter the pair removed. -/
theorem dehnSwap_of_straddle_left {R : Set (List (α × Bool))}
    {A u v B : List (α × Bool)} {y : α × Bool}
    (hr : (y :: u) ++ v ∈ symmetrization R) :
    DehnSwap R (A ++ (u ++ B))
      (A ++ (invLetter y :: (FreeGroup.invRev v ++ B))) := by
  refine ⟨A, B, u, v ++ [y], u ++ (v ++ [y]), mem_symmetrization_shift_left hr, rfl,
    rfl, ?_⟩
  rw [FreeGroup.invRev_append, invRev_singleton]
  simp only [List.cons_append, List.nil_append]

/-! ## Two occurrences of relators, one inside the other -/

/-- **An occurrence long enough to be no piece names its own relator.**  If `p`
occurs inside the symmetrized relator `r` at position `|a|`, is a prefix of the
symmetrized relator `r₂`, and `r₂` is at most six times as long as `p`, then
`C'(1/6)` leaves no room for `p` to be a piece: `r₂` is `r` rotated to that
position. -/
theorem eq_rotate_of_occurrence {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {r r₂ p a b : List (α × Bool)} (hr : r ∈ symmetrization R)
    (hr₂ : r₂ ∈ symmetrization R) (hocc : r = a ++ (p ++ b)) (hpre : p <+: r₂)
    (hbig : r₂.length ≤ 6 * p.length) :
    r₂ = r.rotate a.length := by
  by_contra hne
  have hap : a ++ p <+: r := ⟨b, by rw [hocc, List.append_assoc]⟩
  have hp2 : p <+: r.rotate a.length := prefix_rotate_of_append_prefix hap
  have hrot : r.rotate a.length ∈ symmetrization R :=
    rotate_mem_symmetrization hr a.length
  have hpiece : IsPiece (symmetrization R) p :=
    isPiece_of_prefix_two hr₂ hrot hne hpre hp2
  have h6 := six_mul_length_lt_of_isPiece hmetric hpiece hr₂ hpre
  omega

/-- Once the two relators are known to be the same word rotated, the complement
of the inner occurrence is read off: it is the rest of the host, wrapped. -/
theorem tail_eq_of_eq_rotate {r r₂ p a b v₂ : List (α × Bool)}
    (hocc : r = a ++ (p ++ b)) (hrot : r₂ = r.rotate a.length)
    (hsplit : r₂ = p ++ v₂) : v₂ = b ++ a := by
  have h1 : r.rotate a.length = (p ++ b) ++ a := by
    rw [hocc, rotate_append]
  have h2 : p ++ v₂ = p ++ (b ++ a) := by
    rw [← hsplit, hrot, h1, List.append_assoc]
  exact List.append_cancel_left h2

/-- **The step buried inside the swap's occurrence.**  A Dehn step whose
occurrence `p` lies inside the block `a ++ p ++ b` a swap destroys rewrites along
the swap's own relator, and its output then *freely* reduces to the swap's
output.

This is the configuration that asks for `FreeClosedBelow`, at the step's output,
which is strictly shorter than the word both came from. -/
theorem red_of_inner_step {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {r r₂ a p b v v₂ A B : List (α × Bool)} (hr : r ∈ symmetrization R)
    (hr₂ : r₂ ∈ symmetrization R) (hsplit : r = (a ++ (p ++ b)) ++ v)
    (hsplit₂ : r₂ = p ++ v₂) (hlong : r₂.length < 2 * p.length) :
    FreeGroup.Red ((A ++ a) ++ (FreeGroup.invRev v₂ ++ (b ++ B)))
      (A ++ (FreeGroup.invRev v ++ B)) := by
  have hocc : r = a ++ (p ++ (b ++ v)) := by
    rw [hsplit]
    simp only [List.append_assoc]
  have hpre : p <+: r₂ := ⟨v₂, hsplit₂.symm⟩
  have hrot : r₂ = r.rotate a.length :=
    eq_rotate_of_occurrence hmetric hr hr₂ hocc hpre (by omega)
  have hv₂ : v₂ = (b ++ v) ++ a := tail_eq_of_eq_rotate hocc hrot hsplit₂
  have hv₂' : v₂ = b ++ (v ++ a) := by
    rw [hv₂, List.append_assoc]
  have hshape : (A ++ a) ++ (FreeGroup.invRev v₂ ++ (b ++ B))
      = A ++ (a ++ (FreeGroup.invRev (b ++ (v ++ a)) ++ (b ++ B))) := by
    rw [hv₂']
    simp only [List.append_assoc]
  rw [hshape]
  exact red_conjugate_cancel A a v b B

/-- **The step whose occurrence swallows the swap's.**  If the block a swap
destroys sits inside a Dehn step's occurrence and the swap does not lengthen,
then --- again by `C'(1/6)` --- the two rewrite along one relator, and the swapped
word reduces to the step's output by free cancellation.

Unlike every other overlap, this one closes outright: no induction hypothesis is
consumed, only the reducibility of the step's own output. -/
theorem dehnReducible_of_outer_step {R : Set (List (α × Bool))}
    (hmetric : MetricSmallCancellation R (1 / 6))
    {r r₂ γ u δ v v₂ C D : List (α × Bool)} (hr : r ∈ symmetrization R)
    (hr₂ : r₂ ∈ symmetrization R) (hsplit : r = u ++ v)
    (hsplit₂ : r₂ = (γ ++ (u ++ δ)) ++ v₂) (hle : v.length ≤ u.length)
    (hW : DehnReducible R (C ++ (FreeGroup.invRev v₂ ++ D))) :
    DehnReducible R ((C ++ γ) ++ (FreeGroup.invRev v ++ (δ ++ D))) := by
  have hocc₂ : r₂ = γ ++ (u ++ (δ ++ v₂)) := by
    rw [hsplit₂]
    simp only [List.append_assoc]
  have hpre : u <+: r := ⟨v, hsplit.symm⟩
  have hbig : r.length ≤ 6 * u.length := by
    rw [hsplit, List.length_append]
    omega
  have hrot : r = r₂.rotate γ.length :=
    eq_rotate_of_occurrence hmetric hr₂ hr hocc₂ hpre hbig
  have hv : v = (δ ++ v₂) ++ γ := tail_eq_of_eq_rotate hocc₂ hrot hsplit
  have hv' : v = δ ++ (v₂ ++ γ) := by
    rw [hv, List.append_assoc]
  have hshape : (C ++ γ) ++ (FreeGroup.invRev v ++ (δ ++ D))
      = C ++ (γ ++ (FreeGroup.invRev (δ ++ (v₂ ++ γ)) ++ (δ ++ D))) := by
    rw [hv']
    simp only [List.append_assoc]
  rw [hshape]
  exact (dehnRed_of_red (red_conjugate_cancel C γ v₂ δ D)).trans hW

/-! ## The partial overlap -/

/-- A Dehn step at the *far* part of an occurrence: if what a step's occurrence
`σ ++ τ` keeps beyond a swap's block is more than half of the step's relator,
then `τ` alone carries a Dehn step, along the relator rotated past `σ`. -/
theorem dehnStep_of_middle_occurrence {R : Set (List (α × Bool))}
    {σ τ v₂ : List (α × Bool)} (hr₂ : σ ++ (τ ++ v₂) ∈ symmetrization R)
    (hlong : (σ ++ (τ ++ v₂)).length < 2 * τ.length) (A B : List (α × Bool)) :
    DehnStep R (A ++ (τ ++ B)) (A ++ (FreeGroup.invRev (v₂ ++ σ) ++ B)) := by
  have hrot : τ ++ (v₂ ++ σ) ∈ symmetrization R := by
    have h := append_swap_mem_symmetrization hr₂
    rwa [List.append_assoc] at h
  have hlen : (τ ++ (v₂ ++ σ)).length < 2 * τ.length := by
    simp only [List.length_append] at hlong ⊢
    omega
  exact DehnStep.dehn A B τ (v₂ ++ σ) (τ ++ (v₂ ++ σ)) hrot rfl hlen

/-- **The partial overlap, seen from the step's output.**  The word a swap of the
step's output produces --- swap the *front* part `γ` of the destroyed block, the
part the step never touched --- is exactly the word the swapped word steps to in
`dehnStep_of_middle_occurrence`.

So in the regime where that step is available, the overlap closes from
`SwapClosedBelow` at the step's output, which is shorter. -/
theorem dehnSwap_of_middle_step {R : Set (List (α × Bool))}
    {A γ σ v v₂ B₁ : List (α × Bool)} (hr : (γ ++ σ) ++ v ∈ symmetrization R) :
    DehnSwap R ((A ++ γ) ++ (FreeGroup.invRev v₂ ++ B₁))
      (A ++ (FreeGroup.invRev v ++ (FreeGroup.invRev (v₂ ++ σ) ++ B₁))) := by
  refine ⟨A, FreeGroup.invRev v₂ ++ B₁, γ, σ ++ v, γ ++ (σ ++ v), ?_, rfl, ?_, ?_⟩
  · rwa [List.append_assoc] at hr
  · simp only [List.append_assoc]
  · rw [FreeGroup.invRev_append, FreeGroup.invRev_append]
    simp only [List.append_assoc]

/-- The mirror of `dehnStep_of_middle_occurrence`: when the step's occurrence
overlaps the swap's block on the *left*, it is the part `γ` lying before the
overlap that may carry a step of its own, and it needs no rotation --- `γ` is
already a prefix of the step's relator. -/
theorem dehnStep_of_front_occurrence {R : Set (List (α × Bool))}
    {γ σ v₂ : List (α × Bool)} (hr₂ : (γ ++ σ) ++ v₂ ∈ symmetrization R)
    (hlong : ((γ ++ σ) ++ v₂).length < 2 * γ.length) (A B : List (α × Bool)) :
    DehnStep R (A ++ (γ ++ B)) (A ++ (FreeGroup.invRev (σ ++ v₂) ++ B)) := by
  refine DehnStep.dehn A B γ (σ ++ v₂) (γ ++ (σ ++ v₂)) ?_ rfl ?_
  · rwa [List.append_assoc] at hr₂
  · simp only [List.length_append] at hlong ⊢
    omega

/-- The mirror of `dehnSwap_of_middle_step`: the swap of the step's output that
meets it. -/
theorem dehnSwap_of_front_step {R : Set (List (α × Bool))}
    {C σ τ v v₂ B : List (α × Bool)} (hr : (σ ++ τ) ++ v ∈ symmetrization R) :
    DehnSwap R (C ++ (FreeGroup.invRev v₂ ++ (τ ++ B)))
      (C ++ (FreeGroup.invRev v₂ ++ (FreeGroup.invRev (v ++ σ) ++ B))) := by
  refine ⟨C ++ FreeGroup.invRev v₂, B, τ, v ++ σ, τ ++ (v ++ σ), ?_, rfl, ?_, ?_⟩
  · have h1 : σ ++ (τ ++ v) ∈ symmetrization R := by
      rwa [List.append_assoc] at hr
    have h2 := append_swap_mem_symmetrization h1
    rwa [List.append_assoc] at h2
  · simp only [List.append_assoc]
  · simp only [List.append_assoc]

/-! ## The closure statements, and what they buy -/

/-- **Closure under free reduction**, the statement `DehnReduceClosed` needs. -/
def DehnFreeClosed (R : Set (List (α × Bool))) : Prop :=
  ∀ W G : List (α × Bool), DehnReducible R W → FreeGroup.Red W G → DehnReducible R G

/-- **Closure under relator swaps.**  Unlike `DehnFreeClosed` this is not a
statement about free reduction at all: it says the reducible words are closed
under the moves that generate the presented group. -/
def DehnSwapClosed (R : Set (List (α × Bool))) : Prop :=
  ∀ W G : List (α × Bool), DehnReducible R W → DehnSwap R W G → DehnReducible R G

/-- **Free closure, restricted to short words.**  The two closure statements are
entangled --- each is used in the proof of the other --- so they are established
together by induction on word length, and this is the form that induction
consumes. -/
def FreeClosedBelow (R : Set (List (α × Bool))) (n : ℕ) : Prop :=
  ∀ W : List (α × Bool), W.length < n → DehnReducible R W →
    ∀ G : List (α × Bool), FreeGroup.Red W G → DehnReducible R G

/-- **Swap closure, restricted to short words.** -/
def SwapClosedBelow (R : Set (List (α × Bool))) (n : ℕ) : Prop :=
  ∀ W : List (α × Bool), W.length < n → DehnReducible R W →
    ∀ G : List (α × Bool), DehnSwap R W G → DehnReducible R G

/-- Every word is short enough for some stage. -/
theorem dehnFreeClosed_of_below {R : Set (List (α × Bool))}
    (h : ∀ n, FreeClosedBelow R n) : DehnFreeClosed R :=
  fun W G hW hred => h (W.length + 1) W (by omega) hW G hred

/-- The same, for swaps. -/
theorem dehnSwapClosed_of_below {R : Set (List (α × Bool))}
    (h : ∀ n, SwapClosedBelow R n) : DehnSwapClosed R :=
  fun W G hW hsw => h (W.length + 1) W (by omega) hW G hsw

/-- Full closure restricts to every stage. -/
theorem freeClosedBelow_of_dehnFreeClosed {R : Set (List (α × Bool))}
    (h : DehnFreeClosed R) (n : ℕ) : FreeClosedBelow R n :=
  fun W _ hW G hred => h W G hW hred

/-- Full closure restricts to every stage. -/
theorem swapClosedBelow_of_dehnSwapClosed {R : Set (List (α × Bool))}
    (h : DehnSwapClosed R) (n : ℕ) : SwapClosedBelow R n :=
  fun W _ hW G hsw => h W G hW hsw

/-- **The one overlap the analysis does not settle**, stated exactly.

The swap destroys `u = γ ++ σ`; the first step of the derivation rewrites
`u₂ = σ ++ τ`, which overlaps it in `σ`; the two relators are distinct, so `σ` is
a piece and `C'(1/6)` bounds it by a sixth; and `2|τ| ≤ |r₂|`, which is exactly
the regime in which `dehnStep_of_middle_occurrence` is *not* available.

Both routes from the step's output to the swap's output run through
`Y = A ++ invRev v ++ invRev σ ++ invRev v₂ ++ B₁`, which is at once the swap of
the step's output (`dehnSwap_of_middle_step`) and the step of the swap's output;
but `|Y| - |W| = 2|σ| - (|u| - |v|) - (|u₂| - |v₂|)`, and in this regime the two
deficits together are at most `2|σ|`, so `Y` is not shorter than the word both
came from and the descent on length stalls.  The mirror configuration --- the step
overlapping the swap's block on the left --- is carried to this one by
`DehnReducible.invRev`.

This is a statement about one configuration, not a hypothesis package: it names
no structure and quantifies over words.  It carries the metric condition itself,
because swap closure is *false* without it --- the commutator witness in
`GreendlingerDehn` refutes it --- so a residual that did not assume `C'(1/6)`
would be asking for more than the theorem gives; and it carries, separately, the
piece bound the analysis derives for the overlap, which is the only consequence of
`C'(1/6)` the configuration has already spent. -/
def PieceOverlapRight (R : Set (List (α × Bool))) : Prop :=
  MetricSmallCancellation R (1 / 6) →
  ∀ A γ σ τ v v₂ B : List (α × Bool),
    (γ ++ σ) ++ v ∈ symmetrization R →
    (σ ++ τ) ++ v₂ ∈ symmetrization R →
    6 * σ.length < ((σ ++ τ) ++ v₂).length →
    v.length ≤ (γ ++ σ).length →
    v₂.length < (σ ++ τ).length →
    2 * τ.length ≤ ((σ ++ τ) ++ v₂).length →
    DehnReducible R ((A ++ γ) ++ (FreeGroup.invRev v₂ ++ B)) →
    DehnReducible R (A ++ (FreeGroup.invRev v ++ (τ ++ B)))

/-- **The mirror of `PieceOverlapRight`**: the step's occurrence overlaps the
swap's block on the left, and the part `γ` lying before the overlap is at most
half of the step's relator, which is where `dehnStep_of_front_occurrence` runs
out.

The two are mirror images under `DehnReducible.invRev`, and a proof of either
should give the other; that transport is not carried out here, so both are
named. -/
def PieceOverlapLeft (R : Set (List (α × Bool))) : Prop :=
  MetricSmallCancellation R (1 / 6) →
  ∀ C γ σ τ v v₂ B : List (α × Bool),
    (σ ++ τ) ++ v ∈ symmetrization R →
    (γ ++ σ) ++ v₂ ∈ symmetrization R →
    6 * σ.length < ((γ ++ σ) ++ v₂).length →
    v.length ≤ (σ ++ τ).length →
    v₂.length < (γ ++ σ).length →
    2 * γ.length ≤ ((γ ++ σ) ++ v₂).length →
    DehnReducible R (C ++ (FreeGroup.invRev v₂ ++ (τ ++ B))) →
    DehnReducible R ((C ++ γ) ++ (FreeGroup.invRev v ++ B))

/-- **The two residual overlaps are one statement.**  Reading every word backwards
and inverting every letter carries a right overlap to a left one: reducibility is
mirror-symmetric (`DehnReducible.invRev`), `symmetrization` is closed under
rotation and formal inversion, and the six length conditions are symmetric in the
two arms `γ` and `τ` of the overlap.

So the gate rests on `PieceOverlapRight` alone. -/
theorem pieceOverlapLeft_of_right {R : Set (List (α × Bool))}
    (h : PieceOverlapRight R) : PieceOverlapLeft R := by
  intro hmetric C γ σ τ v v₂ B hr hr₂ h6 hle hv₂ hsmall hW
  have hmemR : (FreeGroup.invRev τ ++ FreeGroup.invRev σ) ++ FreeGroup.invRev v
      ∈ symmetrization R := by
    have h1 : v ++ (σ ++ τ) ∈ symmetrization R := append_swap_mem_symmetrization hr
    have h2 := invRev_mem_symmetrization h1
    rwa [FreeGroup.invRev_append, FreeGroup.invRev_append] at h2
  have hmem₂R : (FreeGroup.invRev σ ++ FreeGroup.invRev γ) ++ FreeGroup.invRev v₂
      ∈ symmetrization R := by
    have h1 : v₂ ++ (γ ++ σ) ∈ symmetrization R := append_swap_mem_symmetrization hr₂
    have h2 := invRev_mem_symmetrization h1
    rwa [FreeGroup.invRev_append, FreeGroup.invRev_append] at h2
  have h6R : 6 * (FreeGroup.invRev σ).length
      < ((FreeGroup.invRev σ ++ FreeGroup.invRev γ) ++ FreeGroup.invRev v₂).length := by
    simp only [List.length_append, FreeGroup.invRev_length] at h6 ⊢
    omega
  have hleR : (FreeGroup.invRev v).length
      ≤ (FreeGroup.invRev τ ++ FreeGroup.invRev σ).length := by
    simp only [List.length_append, FreeGroup.invRev_length] at hle ⊢
    omega
  have hv₂R : (FreeGroup.invRev v₂).length
      < (FreeGroup.invRev σ ++ FreeGroup.invRev γ).length := by
    simp only [List.length_append, FreeGroup.invRev_length] at hv₂ ⊢
    omega
  have hsmallR : 2 * (FreeGroup.invRev γ).length
      ≤ ((FreeGroup.invRev σ ++ FreeGroup.invRev γ) ++ FreeGroup.invRev v₂).length := by
    simp only [List.length_append, FreeGroup.invRev_length] at hsmall ⊢
    omega
  have hWR : DehnReducible R ((FreeGroup.invRev B ++ FreeGroup.invRev τ)
      ++ (FreeGroup.invRev (FreeGroup.invRev v₂) ++ FreeGroup.invRev C)) := by
    have hb := hW.invRev
    have hshape : FreeGroup.invRev (C ++ (FreeGroup.invRev v₂ ++ (τ ++ B)))
        = (FreeGroup.invRev B ++ FreeGroup.invRev τ)
            ++ (FreeGroup.invRev (FreeGroup.invRev v₂) ++ FreeGroup.invRev C) := by
      rw [FreeGroup.invRev_append, FreeGroup.invRev_append, FreeGroup.invRev_append]
      simp only [List.append_assoc]
    rwa [hshape] at hb
  have hgoalR := h hmetric (FreeGroup.invRev B) (FreeGroup.invRev τ)
    (FreeGroup.invRev σ)
    (FreeGroup.invRev γ) (FreeGroup.invRev v) (FreeGroup.invRev v₂)
    (FreeGroup.invRev C) hmemR hmem₂R h6R hleR hv₂R hsmallR hWR
  refine DehnReducible.of_invRev ?_
  have hshape2 : FreeGroup.invRev ((C ++ γ) ++ (FreeGroup.invRev v ++ B))
      = FreeGroup.invRev B ++ (FreeGroup.invRev (FreeGroup.invRev v)
          ++ (FreeGroup.invRev γ ++ FreeGroup.invRev C)) := by
    rw [FreeGroup.invRev_append, FreeGroup.invRev_append, FreeGroup.invRev_append]
    simp only [List.append_assoc]
  rw [hshape2]
  exact hgoalR

/-- Free-reduction closure is exactly the gate's remaining statement. -/
theorem dehnReduceClosed_of_dehnFreeClosed [DecidableEq α]
    {R : Set (List (α × Bool))} (h : DehnFreeClosed R) : DehnReduceClosed R :=
  fun W hW => h W (FreeGroup.reduce W) hW FreeGroup.reduce.red

/-- **The gate, from free closure.**  The concatenation of the factors of any
expression is reducible, its free reduction is therefore reducible, and a step
out of a nonempty reduced word is the Greendlinger conclusion. -/
theorem greendlingerConclusion_of_dehnFreeClosed [DecidableEq α]
    {R : Set (List (α × Bool))} (hRne : ∀ r ∈ R, r ≠ [])
    (h : DehnFreeClosed R) : GreendlingerConclusion R :=
  greendlingerConclusion_of_dehnReduceClosed hRne
    (dehnReduceClosed_of_dehnFreeClosed h)

end SmallCancellationRouter
end GroupApproximation
