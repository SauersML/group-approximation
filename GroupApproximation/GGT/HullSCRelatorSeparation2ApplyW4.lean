import GroupApproximation.GGT.HullSCRelatorSeparation2Aligned
import GroupApproximation.GGT.HullSCRelatorSeparation2Core

/-!
# The aligned case's second connector, from (W4)

The design clause that used to force the aligned case's connectors trivial is
gone, and this is what replaces it: Hull's (W4), that the two subgroups meet
only in the identity.

## The mechanism

The polygon's second gap at a matched pair is

    x' = (listVal py · vertex 1 u (d+1))⁻¹ · vertex 1 u' (j+1)

and the rigidity input puts it in `H_b`, `b` the index of the matched
component.  Now match the NEXT component of the piece.  By alternation its
index is `!b`, and its own FIRST gap is

    y = (vertex 1 u' j')⁻¹ · (listVal py · vertex 1 u (d+1))

in `H_{!b}`.  The two share the vertex `listVal py · vertex 1 u (d+1)`, so when
`j' = j + 1` they are inverse, `x'` lies in both subgroups, and (W4) makes it
`1`.  That is `secondGap_eq_one_of_next`, and it is three lines: the content is
`j' = j + 1`.

## Why `j' = j + 1`

The same unique occurrence that gives `e = f`.  Each match pins its far-side
component to the SAME letter of `R` as its near-side one --- that is
`HullSC.position_eq_of_alignedMatch` --- so the two matches pin the far side to
the letters at `P` and `P + 1`, consecutive.  `farSide_succ_of_positions` is
that arithmetic: two congruences modulo `|R|`, cancelled on the left and read
off inside one window.

The window hypothesis `j + 1 < |R|` is what excludes the wrap, and it is the
only boundary the argument has.  A caller with two candidate matches has it at
one of them, because their far-side images are distinct and only one position
of a word is its last.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section W4

variable {G : Type u} [Group G]

/-- **(W4) kills an element of both subgroups**, at either index. -/
theorem eq_one_of_mem_both {D : GGT.RelGenSet G Bool}
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    {b : Bool} {z : G} (hb : z ∈ D.fam b) (hnb : z ∈ D.fam (!b)) : z = 1 := by
  cases b with
  | false => exact hdisj z hb hnb
  | true => exact hdisj z hnb hb

/-- **The next match's far-side component starts where this one's ended.**

Two congruences modulo the relator's length, cancelled on the left; the window
hypothesis is what rules out the wrap. -/
theorem farSide_succ_of_positions {L c c' d j j' : ℕ}
    (h₀ : (c + d) % L = (c' + j) % L)
    (h₁ : (c + (d + 1)) % L = (c' + j') % L)
    (hj : j + 1 < L) (hj' : j' < L) : j' = j + 1 := by
  have hstep : (c + d + 1) % L = (c' + j + 1) % L := by
    rw [Nat.add_mod (c + d) 1 L, Nat.add_mod (c' + j) 1 L, h₀]
  have e1 : c + (d + 1) = c + d + 1 := by omega
  have e2 : c' + (j + 1) = c' + j + 1 := by omega
  have hmod : (c' + j') % L = (c' + (j + 1)) % L := by
    rw [← h₁, e1, e2, hstep]
  have h2 : j' % L = (j + 1) % L := Nat.ModEq.add_left_cancel' c' hmod
  rw [Nat.mod_eq_of_lt hj', Nat.mod_eq_of_lt hj] at h2
  exact h2

/-- **The second gap is trivial, once the next component is matched.**

`A` is the near-side vertex the two matches share and `B` the far-side one; the
first match puts `A⁻¹ * B` in `H_b` and the second puts its inverse in
`H_{!b}`. -/
theorem secondGap_eq_one_of_next {D : GGT.RelGenSet G Bool}
    (hdisj : ∀ x : G, x ∈ D.fam false → x ∈ D.fam true → x = 1)
    {b : Bool} {A B : G} (hx' : A⁻¹ * B ∈ D.fam b)
    (hy : B⁻¹ * A ∈ D.fam (!b)) : A⁻¹ * B = 1 := by
  refine eq_one_of_mem_both hdisj hx' ?_
  have hinv : A⁻¹ * B = (B⁻¹ * A)⁻¹ := by group
  rw [hinv]
  exact inv_mem hy

end W4

end HullSC
end GroupApproximation
