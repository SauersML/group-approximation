import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.DegreeFunctorialityAndHomotopy

/-!
# Degree of the antipodal map

This file advances toward the classical computation

```text
degree(antipodal on Sⁿ) = (-1)^(n+1)
```

and proves its **parity consequence** unconditionally (relative to any chosen
top-homology identification `e`):

```text
degree(antipodal) ≡ 1  (mod 2),    i.e.   Odd (degree (antipodal n)).
```

## Status

The genuine *unconditional* topological degree of self-maps of `Sphere n` still
cannot be defined: the only missing input, the top-homology identification
`Hₙ(Sⁿ; ℤ) ≅ ℤ` (a term of `SphereTopHomologyIso n` for `n ≥ 1`), remains absent
from pinned Mathlib (it needs excision / Mayer–Vietoris / the long exact sequence
of a topological pair / a suspension isomorphism).  Moreover, there is **no
topological mapping-degree theory** in pinned Mathlib at all (no `mapDegree`, no
Brouwer degree, no "degree of a linear sphere map = determinant sign" lemma), so
the *sign* `(-1)^(n+1)` cannot be produced unconditionally.  **No fake degree, no
fake top-homology isomorphism, and no fake orientation theorem are introduced.**

What is genuinely provable, and is provided here, building on the conditional
degree `degreeOfIso` of `Degree.lean` and the `±1` facts of
`DegreeAPIStrengthening.lean`:

* **Parity of `(-1)^(n+1)`.** `odd_neg_one_pow_succ`, `neg_one_pow_succ_emod_two`,
  `neg_one_pow_succ_eq_one_or_neg_one` — pure arithmetic facts about the target
  value.
* **Parity of the antipodal degree (unconditional given `e`).**
  `odd_degreeOfIso_antipodal`, `degreeOfIso_antipodal_emod_two`
  (`degree ≡ 1 mod 2`), and the mod-2 agreement with the target
  `degreeOfIso_antipodal_emod_two_eq_neg_one_pow`.  These are the parity results
  the project's final odd-degree program may consume.
* **Compatibility of the project `antipodal` with ambient negation.**
  `antipodal_coe_eq_ambientNeg`: the bundled `antipodal n` is the restriction to
  the unit sphere of the ambient linear map `-LinearMap.id` whose determinant is
  `det_ambientNeg = (-1)^(n+1)`.
* **Conditional full theorem.** `degreeOfIso_antipodal_eq_neg_one_pow_of_eq_det`:
  *if* the degree of the antipodal map equals the determinant of its ambient
  linear map (the missing "degree = determinant sign for linear sphere maps"
  bridge), *then* `degree (antipodal n) = (-1)^(n+1)`.  Packaged via the
  hypothesis predicate `DegreeEqAmbientDet` and specialized to
  `SphereOrientation.degree`.

## Exact remaining blocker

The single missing piece for the *value* (beyond the degree's own
`Hₙ(Sⁿ;ℤ) ≅ ℤ` blocker) is the topological bridge "the degree of a linear
orthogonal self-map of `Sⁿ` equals the sign of its ambient determinant"
(equivalently, "a reflection has degree `-1`").  That is the irreducible
topological input, absent from pinned Mathlib; here it is isolated as the explicit
hypothesis `DegreeEqAmbientDet`.
-/

noncomputable section

open CategoryTheory

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The ambient antipodal linear map `x ↦ -x` on `ℝ^(n+1)`, abbreviated. Its
determinant is `(-1)^(n+1)` (`det_ambientNeg`). -/
abbrev ambientNeg (n : ℕ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  -LinearMap.id

/-! ## Parity of the target value `(-1)^(n+1)` -/

/-- `(-1)^(n+1)` is odd (it is `±1`). -/
theorem odd_neg_one_pow_succ (n : ℕ) : Odd ((-1 : ℤ) ^ (n + 1)) :=
  (Int.odd_iff.mpr (by decide)).pow

/-- `(-1)^(n+1) ≡ 1 (mod 2)`. -/
theorem neg_one_pow_succ_emod_two (n : ℕ) : ((-1 : ℤ) ^ (n + 1)) % 2 = 1 :=
  Int.odd_iff.mp (odd_neg_one_pow_succ n)

/-- `(-1)^(n+1)` is `1` or `-1`. -/
theorem neg_one_pow_succ_eq_one_or_neg_one (n : ℕ) :
    ((-1 : ℤ) ^ (n + 1)) = 1 ∨ ((-1 : ℤ) ^ (n + 1)) = -1 := by
  rcases Nat.even_or_odd (n + 1) with h | h
  · exact Or.inl (Even.neg_one_pow h)
  · exact Or.inr (Odd.neg_one_pow h)

/-! ## Compatibility of `antipodal` with the ambient negation -/

/-- **Compatibility with ambient negation.** The bundled antipodal self-map
`antipodal n` is the restriction to the unit sphere of the ambient linear map
`-LinearMap.id`: on underlying vectors, `↑(antipodal n x) = (-LinearMap.id) ↑x`.
This is the precise sense in which the orientation sign `det_ambientNeg = (-1)^(n+1)`
governs the antipodal map. -/
theorem antipodal_coe_eq_ambientNeg {n : ℕ} (x : Sphere n) :
    ((antipodal n x : Sphere n) : EuclideanSpace ℝ (Fin (n + 1)))
      = ambientNeg n (x : EuclideanSpace ℝ (Fin (n + 1))) := by
  simp [ambientNeg]

/-! ## Parity of the antipodal degree (unconditional given `e`) -/

/-- **The degree of the antipodal map is odd** (relative to any chosen
identification `e : Hₙ(Sⁿ;ℤ) ≅ ℤ`).  This is the parity consequence of
`degree (antipodal n) = (-1)^(n+1)`, and it holds unconditionally on the sign:
the antipodal map is a self-homeomorphism, so its degree is `±1`, hence odd. -/
theorem odd_degreeOfIso_antipodal {n : ℕ} (e : SphereTopHomologyIso n) :
    Odd (degreeOfIso e (antipodal n)) := by
  rcases degreeOfIso_antipodal_eq_one_or_neg_one e with h | h <;> rw [h] <;> decide

/-- **The degree of the antipodal map is `≡ 1 (mod 2)`** (relative to any chosen
`e`).  This is the parity statement `degree(antipodal) ≡ 1 mod 2` requested as the
minimal milestone. -/
theorem degreeOfIso_antipodal_emod_two {n : ℕ} (e : SphereTopHomologyIso n) :
    degreeOfIso e (antipodal n) % 2 = 1 :=
  Int.odd_iff.mp (odd_degreeOfIso_antipodal e)

/-- **Mod-2 agreement with the target value.** The degree of the antipodal map
agrees with `(-1)^(n+1)` modulo `2`: both are odd. This is the parity content of
the full degree theorem, available now without the orientation sign. -/
theorem degreeOfIso_antipodal_emod_two_eq_neg_one_pow {n : ℕ}
    (e : SphereTopHomologyIso n) :
    degreeOfIso e (antipodal n) % 2 = ((-1 : ℤ) ^ (n + 1)) % 2 := by
  rw [degreeOfIso_antipodal_emod_two, neg_one_pow_succ_emod_two]

/-! ## Conditional full theorem: degree = determinant sign ⇒ `(-1)^(n+1)`

The only missing input for the *value* is the topological bridge
"degree of a linear sphere map = sign of its ambient determinant".  We isolate it
as an explicit hypothesis and show it yields the classical formula. -/

/-- The hypothesis that the antipodal degree equals the determinant of its ambient
linear map `-LinearMap.id`.  This is exactly the (currently missing) topological
bridge "degree of a linear orthogonal self-map of `Sⁿ` = sign of its ambient
determinant", specialized to the antipodal map.  It is stated as a hypothesis, not
proved — there is no fake degree/determinant bridge. -/
def DegreeEqAmbientDet {n : ℕ} (e : SphereTopHomologyIso n) : Prop :=
  (degreeOfIso e (antipodal n) : ℝ) = LinearMap.det (ambientNeg n)

/-- **Conditional antipodal-degree theorem.**  *If* the degree of the antipodal
map equals the determinant of its ambient linear map (`DegreeEqAmbientDet`), *then*
`degree (antipodal n) = (-1)^(n+1)`.  The proof simply rewrites with the genuine
ambient determinant fact `det_ambientNeg`. -/
theorem degreeOfIso_antipodal_eq_neg_one_pow_of_eq_det {n : ℕ}
    (e : SphereTopHomologyIso n) (h : DegreeEqAmbientDet e) :
    degreeOfIso e (antipodal n) = (-1) ^ (n + 1) := by
  rw [DegreeEqAmbientDet, det_ambientNeg] at h
  exact_mod_cast h

/-! ## Oriented-degree wrappers -/

namespace SphereOrientation

variable (o : SphereOrientation)

/-- The degree of the antipodal map is odd. -/
theorem odd_degree_antipodal (n : ℕ) : Odd (o.degree (antipodal n)) :=
  odd_degreeOfIso_antipodal (o.iso n)

/-- The degree of the antipodal map is `≡ 1 (mod 2)`. -/
theorem degree_antipodal_emod_two (n : ℕ) : o.degree (antipodal n) % 2 = 1 :=
  degreeOfIso_antipodal_emod_two (o.iso n)

/-- **Conditional full theorem, oriented form.** If the antipodal degree equals
its ambient determinant, it equals `(-1)^(n+1)`. -/
theorem degree_antipodal_eq_neg_one_pow_of_eq_det (n : ℕ)
    (h : DegreeEqAmbientDet (o.iso n)) :
    o.degree (antipodal n) = (-1) ^ (n + 1) :=
  degreeOfIso_antipodal_eq_neg_one_pow_of_eq_det (o.iso n) h

end SphereOrientation

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
