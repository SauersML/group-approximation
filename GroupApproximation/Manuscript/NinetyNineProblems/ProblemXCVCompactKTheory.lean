import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Problem XCV: the compact `K₀` obstruction

This file kernel-checks the algebraic endpoint of the counterexample to the
first assertion of Problem XCV in Schafhauser--Tikuisis--White.

For a stable-rank-one C*-algebra, the Grothendieck group of the compact
elements of its Cuntz semigroup is `K₀`.  Thus a Cuntz-semigroup isomorphism
with `Cu(𝒵)` would force that group to be `ℤ`.  The nuclear counterexample has
`K₀ = ℤ ⊕ ℤ`, due to its external `K₁ ⊗ K₁` class.  The theorem below proves,
without an axiom or hypothesis, that these two additive groups cannot be
isomorphic.

The operator-algebraic identifications are deliberately not declared here:
Mathlib currently has no Cuntz-semigroup or operator `K`-theory API.  Declaring
them as local axioms would turn the claimed solution into a conditional
formalization.
-/

namespace GroupApproximation.NinetyNineProblems.ProblemXCV

/-- The cyclic group `ℤ` is not additively isomorphic to the rank-two free
abelian group `ℤ × ℤ`.  This is the terminal algebraic contradiction in the
compact-Cuntz-element obstruction to Problem XCV. -/
theorem int_not_addEquiv_int_prod_int : ¬ Nonempty (ℤ ≃+ ℤ × ℤ) := by
  rintro ⟨e⟩
  obtain ⟨m, hm⟩ := e.surjective (1, 0)
  obtain ⟨n, hn⟩ := e.surjective (0, 1)
  have image_eq_zsmul (k : ℤ) : e k = k • e 1 := by
    have h1 : e (k • (1 : ℤ)) = k • e 1 := map_zsmul e k 1
    simpa using h1
  have hm' : m • e 1 = (1, 0) := by simpa [image_eq_zsmul] using hm
  have hn' : n • e 1 = (0, 1) := by simpa [image_eq_zsmul] using hn
  have hma : m * (e 1).1 = 1 := by
    simpa using congrArg Prod.fst hm'
  have hmb : m * (e 1).2 = 0 := by
    simpa using congrArg Prod.snd hm'
  have hnb : n * (e 1).2 = 1 := by
    simpa using congrArg Prod.snd hn'
  have hm0 : m ≠ 0 := by
    intro hm_zero
    simp [hm_zero] at hma
  have hb0 : (e 1).2 = 0 := (mul_eq_zero.mp hmb).resolve_left hm0
  simp [hb0] at hnb

end GroupApproximation.NinetyNineProblems.ProblemXCV
