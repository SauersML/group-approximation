import GroupApproximation.GGT.HullSCRelatorSeparation2Locate

/-!
# The alternating relator is aperiodic

This is the last piece of the aligned case of step (c), and it is not geometry.

`GGT/HullSCRelatorSeparation2Centralizer.lean` reduced the aligned branch at
`δ ≠ 0` to a centralizer claim about the piece's own connector, and that claim
is false in general -- the four-gon's closing clause `r = p⁻¹` is equivalent to
it, and is refuted.  What a four-gon with trivial connectors does give is that
its two long sides meet at the matched vertices and that the segment between two
matched blocks on one side spells the same element as the segment between them
on the other.  Against `s = w.rotate δ` that reads: **`w` has a period `δ`** --
and a relator with a nontrivial period is what the design forbids.

The forbidding is one line of the design, `ms.Nodup`, and the mechanism is the
one step (b) already runs on: a block letter occurs at exactly one position of
the relator, so if it occurs again at a shifted position the shift is zero
modulo the length.  Everything here is that observation packaged three ways.

* `shift_mod_eq_zero_of_block_eq` -- the shift, from one block letter seen twice.
* `rotate_period_zero` -- so the relator has no nontrivial period: a rotation
  fixing it is a rotation by a multiple of its length.
* `rotate_mod_eq_of_rotate_eq` -- so distinct rotations are distinct words, which
  is the form the assembly consumes: it turns `w' = w.rotate δ` with `w' ≠ w`
  into `δ % |R| ≠ 0`, and the hand-off's period into `δ % |R| = 0`.

Aperiodicity is exactly where the alternation and the distinct exponents pay
off: over one subgroup the relator's run is a single component and nothing
distinguishes its rotations, which is the same defect
`HullSC.not_quasiGeodesic_relatorWord` records from the metric side.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Aperiodic

variable {G : Type u} [Group G]

/-- **A block letter seen at a shifted position pins the shift.**

`HullSC.blockPosition_unique₂` says a block letter occupies one position of the
relator; reading the same letter at `(δ + P) % |R|` therefore forces that to be
`P`, and `P < |R|` turns it into `δ ≡ 0`. -/
theorem shift_mod_eq_zero_of_block_eq {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then h₁ else h₀) ^ n))
    (hnodup : ms.Nodup) {P δ : ℕ} {b : Bool} {x : G}
    (hP : P < (relatorWord₂ p h₀ h₁ ms).length)
    (h1 : (relatorWord₂ p h₀ h₁ ms)[P]? = some (GGT.RelLetter.comp b x))
    (h2 : (relatorWord₂ p h₀ h₁ ms)[(δ + P) % (relatorWord₂ p h₀ h₁ ms).length]?
      = some (GGT.RelLetter.comp b x)) :
    δ % (relatorWord₂ p h₀ h₁ ms).length = 0 := by
  have heq : (δ + P) % (relatorWord₂ p h₀ h₁ ms).length = P :=
    blockPosition_unique₂ hinj hnodup h2 h1
  have hPmod : P % (relatorWord₂ p h₀ h₁ ms).length = P := Nat.mod_eq_of_lt hP
  have hmod : δ + P ≡ 0 + P [MOD (relatorWord₂ p h₀ h₁ ms).length] := by
    show (δ + P) % _ = (0 + P) % _
    rw [heq, Nat.zero_add, hPmod]
  have hzero := Nat.ModEq.add_right_cancel' P hmod
  have h0 : δ % (relatorWord₂ p h₀ h₁ ms).length
      = 0 % (relatorWord₂ p h₀ h₁ ms).length := hzero
  rwa [Nat.zero_mod] at h0

/-- **The alternating relator has no nontrivial period.**

A rotation fixing the word carries the first block letter to itself, and that
letter names its own position. -/
theorem rotate_period_zero {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then h₁ else h₀) ^ n))
    (hnodup : ms.Nodup) (hms : 0 < ms.length) {δ : ℕ}
    (h : (relatorWord₂ p h₀ h₁ ms).rotate δ = relatorWord₂ p h₀ h₁ ms) :
    δ % (relatorWord₂ p h₀ h₁ ms).length = 0 := by
  have hlen : (relatorWord₂ p h₀ h₁ ms).length = p.length + ms.length :=
    length_relatorWord₂ p h₀ h₁ ms
  obtain ⟨b, x, hb⟩ := blockWord_getElem?_comp h₀ h₁ false ms hms
  have hR : (relatorWord₂ p h₀ h₁ ms)[p.length]?
      = some (GGT.RelLetter.comp b x) := by
    have hblk := relatorWord₂_getElem?_block p h₀ h₁ ms 0
    rw [Nat.add_zero] at hblk
    rw [hblk]
    exact hb
  have hPlt : p.length < (relatorWord₂ p h₀ h₁ ms).length := by omega
  have hrot : ((relatorWord₂ p h₀ h₁ ms).rotate δ)[p.length]?
      = some (GGT.RelLetter.comp b x) := by
    rw [h]
    exact hR
  exact shift_mod_eq_zero_of_block_eq hinj hnodup hPlt hR
    (getElem?_of_rotate hPlt hrot)

/-- **Distinct rotations are distinct words.**

The form the assembly consumes: `w' = w.rotate δ` and `w' ≠ w` give
`δ % |R| ≠ 0`, while the four-gon with trivial connectors gives the period and
so `δ % |R| = 0`. -/
theorem rotate_mod_eq_of_rotate_eq {p : List G} {h₀ h₁ : G} {ms : List ℕ}
    (hinj : ∀ b : Bool,
      Function.Injective (fun n : ℕ => (if b then h₁ else h₀) ^ n))
    (hnodup : ms.Nodup) (hms : 0 < ms.length) {d d' : ℕ}
    (h : (relatorWord₂ p h₀ h₁ ms).rotate d = (relatorWord₂ p h₀ h₁ ms).rotate d') :
    d % (relatorWord₂ p h₀ h₁ ms).length
      = d' % (relatorWord₂ p h₀ h₁ ms).length := by
  rcases Nat.le_total d' d with hle | hle
  · have hsplit : (relatorWord₂ p h₀ h₁ ms).rotate d
        = ((relatorWord₂ p h₀ h₁ ms).rotate (d - d')).rotate d' := by
      rw [List.rotate_rotate, show d - d' + d' = d from by omega]
    have hstep : ((relatorWord₂ p h₀ h₁ ms).rotate (d - d')).rotate d'
        = (relatorWord₂ p h₀ h₁ ms).rotate d' := by
      rw [← hsplit]
      exact h
    have hcancel : (relatorWord₂ p h₀ h₁ ms).rotate (d - d')
        = relatorWord₂ p h₀ h₁ ms := List.rotate_injective d' hstep
    have hzero := rotate_period_zero hinj hnodup hms hcancel
    conv_lhs => rw [show d = d' + (d - d') from by omega]
    rw [Nat.add_mod, hzero, Nat.add_zero]
    exact Nat.mod_mod d' _
  · have hsplit : (relatorWord₂ p h₀ h₁ ms).rotate d'
        = ((relatorWord₂ p h₀ h₁ ms).rotate (d' - d)).rotate d := by
      rw [List.rotate_rotate, show d' - d + d = d' from by omega]
    have hstep : ((relatorWord₂ p h₀ h₁ ms).rotate (d' - d)).rotate d
        = (relatorWord₂ p h₀ h₁ ms).rotate d := by
      rw [← hsplit]
      exact h.symm
    have hcancel : (relatorWord₂ p h₀ h₁ ms).rotate (d' - d)
        = relatorWord₂ p h₀ h₁ ms := List.rotate_injective d hstep
    have hzero := rotate_period_zero hinj hnodup hms hcancel
    conv_rhs => rw [show d' = d + (d' - d) from by omega]
    rw [Nat.add_mod, hzero, Nat.add_zero]
    exact (Nat.mod_mod d _).symm

end Aperiodic

end HullSC
end GroupApproximation
