import GroupApproximation.GGT.OsinTheorem54SepSmul
import GroupApproximation.GGT.OsinTheorem54SepYLetterWord

/-!
# The shallow-letter bound at a translated basepoint

`OsinTheorem54SepYLetterWord.mem_relBall_of_isCompOf_of_sepSet_empty` says that
on a geodesic from `1` to a letter of `Y`, every family letter is shallow --- its
value lies in the `d_lam`-ball of radius `Dc`.  Path surgery does not meet that
form.  It meets a `Y`-letter `y` read at a vertex `g`, and replaces it by a
geodesic from `g` to `g * y`; the letters it then has to weigh sit on *that*
geodesic.

This module is the one-line translation.  The hypothesis stays where the surgery
has it --- on the letter, `sepSet D lam Dc 1 y = ∅` --- and only the geodesic
moves, by `OsinTheorem54SepSmul.isGeodesicWord_mul_left`.  No appeal to
`sepSet_smul` is needed, the separating set never having been translated.

## What it does not say

The bound is on each letter's own depth.  It does not bound the `d_lam`
displacement of the replacement path, spans composing rather than adding; and it
says nothing about avoidance --- a shallow `lam`-letter read at a vertex of
`H_lam` still traverses an edge of `Γ_{H_lam}`.  Shallowness is what makes the
demoted letter a legal base letter; whether the spliced path avoids `Γ_{H_lam}`
turns on the vertex, not on the letter.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **On a geodesic from `g` to `g * y` with `y` a letter of `Y`, every family
letter is shallow.**

The form path surgery meets: the `Y`-membership is a fact about the letter, and
the geodesic realising it starts wherever the path had got to. -/
theorem mem_relBall_of_isCompOf_of_sepSet_empty_smul (D : RelGenSet G Λ)
    (Dc : ℕ) {g y : G} (hy : ∀ lam : Λ, sepSet D lam Dc 1 y = ∅)
    {p : List (RelLetter G Λ)} (hp : IsGeodesicWord D g (g * y) p) {i : ℕ}
    (hi : i < p.length) {mu : Λ} (hc : (p[i]'hi).IsCompOf mu) :
    (p[i]'hi).val ∈ D.relBall mu Dc := by
  have hg : IsGeodesicWord D (g⁻¹ * g) (g⁻¹ * (g * y)) p :=
    (isGeodesicWord_mul_left D g⁻¹ g (g * y) p).mpr hp
  rw [inv_mul_cancel, inv_mul_cancel_left] at hg
  exact mem_relBall_of_isCompOf_of_sepSet_empty D Dc hy hg hi hc

end OsinComponents
end GGT
end GroupApproximation
