import GroupApproximation.Higman.GeneratedCoords

/-!
# Pinning one coordinate and freeing the rest

Higman's Section 2 builds its sets out of conditions on individual coordinates:
the octuple set of Theorem 3 constrains a value track, an index track, an
enumeration parameter and an occupancy flag; the auxiliary sets `E = {g | g 3 = 1}`
and the monotone-flag set of the `W` construction constrain nothing else at all.
Every one of them is an intersection of *pinned* sets — sequences whose value at
one coordinate is prescribed and which are otherwise unconstrained.

This module builds that primitive.  Given the one-point set `{c·e₀}`, the
liberation operations produce `{f | f 0 = c}`:

    π (ρ (π {c·e₀})) = {f | f 0 = c}.

Read left to right, `π` frees the strictly positive coordinates, `ρ` reflects the
index so that the freed half becomes the negative one, and the second `π` frees
the positives again — after which every coordinate except the origin has been
freed exactly once.

## Why this shape and not a shorter one

`ζ` frees the origin, which is the one coordinate that must survive, so it cannot
appear.  `π` alone frees a half-line and leaves the other half pinned to zero,
and `ρ` alone permutes without freeing; only the sandwich frees both half-lines
while fixing the origin, and it does so without ever freeing the origin at an
intermediate stage.

The companion fact — that `{c·e₀}` is generated for every `c` — is the value
calculus, and is not needed here: this module takes the one-point set as a
hypothesis, so it composes with whatever proof of that eventually arrives.
`Seq.higmanGenerated_negOneAtZero` already supplies the case `c = -1`, and `Z`
supplies `c = 0`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

/-- The sequences whose value at the origin is `c`, with every other coordinate
unconstrained. -/
def pinZero (c : ℤ) : Set E := {f | f 0 = c}

/-- The reflection `j ↦ -j` of a sequence. -/
noncomputable def reflect (f : E) : E :=
  Finsupp.equivMapDomain (Equiv.neg ℤ) f

@[simp] theorem reflect_apply (f : E) (i : ℤ) : reflect f i = f (-i) := by
  unfold reflect
  rw [Finsupp.equivMapDomain_apply]
  rfl

/-- **The liberation sandwich.**  Freeing the positives, reflecting, and freeing
the positives again pins exactly the origin. -/
theorem piOp_rhoOp_piOp_single (c : ℤ) :
    piOp (rhoOp (piOp {Finsupp.single (0 : ℤ) c})) = pinZero c := by
  ext f
  constructor
  · rintro ⟨g₁, ⟨g₂, ⟨g₃, hg₃, hg₂⟩, hg₁⟩, hf⟩
    have hg₃' : g₃ = Finsupp.single (0 : ℤ) c := hg₃
    have h0 : f 0 = g₁ 0 := hf 0 le_rfl
    have h1 : g₁ 0 = g₂ 0 := by simpa using hg₁ 0
    have h2 : g₂ 0 = g₃ 0 := hg₂ 0 le_rfl
    have h3 : g₃ 0 = c := by rw [hg₃']; simp
    show f 0 = c
    rw [h0, h1, h2, h3]
  · intro hf
    have hf0 : f 0 = c := hf
    -- free the negatives of `f`, then reflect: the result is pinned at the origin
    refine ⟨reflect (Finsupp.filter (fun j : ℤ => (0 : ℤ) ≤ j) (reflect f)), ?_, ?_⟩
    · refine ⟨Finsupp.filter (fun j : ℤ => (0 : ℤ) ≤ j) (reflect f), ?_, ?_⟩
      · refine ⟨Finsupp.single (0 : ℤ) c, rfl, ?_⟩
        intro i hi
        rcases lt_or_eq_of_le hi with hlt | heq
        · rw [Finsupp.filter_apply, if_neg (by omega), Finsupp.single_apply,
            if_neg (by omega)]
        · subst heq
          rw [Finsupp.filter_apply, if_pos le_rfl, reflect_apply, neg_zero, hf0,
            Finsupp.single_apply, if_pos rfl]
      · intro i
        rw [reflect_apply]
    · intro i hi
      rw [reflect_apply, Finsupp.filter_apply, if_pos (by omega), reflect_apply,
        neg_neg]

/-- **A pinned coordinate is generated**, given the one-point set it is freed
from. -/
theorem higmanGenerated_pinZero (c : ℤ)
    (h : HigmanGenerated ({Finsupp.single (0 : ℤ) c} : Set E)) :
    HigmanGenerated (pinZero c) := by
  rw [← piOp_rhoOp_piOp_single c]
  exact HigmanGenerated.pi (HigmanGenerated.rho (HigmanGenerated.pi h))

/-- The origin pinned to zero: the case `c = 0`, from `Z`. -/
theorem higmanGenerated_pinZero_zero : HigmanGenerated (pinZero 0) := by
  refine higmanGenerated_pinZero 0 ?_
  have h : ({Finsupp.single (0 : ℤ) (0 : ℤ)} : Set E) = Zset := by
    rw [Finsupp.single_zero]
    rfl
  rw [h]
  exact HigmanGenerated.zero

/-- The origin pinned to `-1`: the case `c = -1`, from `S ∩ ζZ`. -/
theorem higmanGenerated_pinZero_neg_one : HigmanGenerated (pinZero (-1)) :=
  higmanGenerated_pinZero (-1) higmanGenerated_negOneAtZero

end Seq
end Higman
end GroupApproximation
