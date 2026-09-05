import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.Degree

/-!
# A self-homeomorphism of a sphere has odd degree

Lane `found-euler-class`, campaign target 3 (STW Problem LIX).

## Why this is on the critical path

`AlgTop/EulerParityBridge.lean` records the one sentence of the manuscript's Lemma 2
that nobody owns:

```text
Even ⟨c_r(W_g), [S¹ × M]⟩  ↔  Even (number of zeros of the section).
```

That sentence splits cleanly into two halves, and **the split is the whole point of
running the obstruction mod 2**:

* a **local** half — at a zero where the derivative is invertible, the local index is
  odd.  Mod `2` this needs no orientation, no determinant, and no sign: it is exactly
  the statement that the section restricted to a small sphere around the zero, being a
  linear isomorphism up to homotopy, has odd degree.  **That half is this file**, and
  it is built on machinery the campaign already has;
* a **global** half — the local indices sum to the characteristic number.  That needs a
  Thom class, hence relative cohomology with excision, and it is the part still owed.

So this file does not close the bridge.  It closes the half of the bridge that can be
closed with what exists, and it makes precise which half remains.

## The statement

A homeomorphism has a two-sided inverse, so its degree is a unit of `ℤ`, so it is `±1`
and in particular odd.  Only two facts about the degree are used —
`degreeOfIso_id` and `degreeOfIso_comp` — and both are already in the vendored
development.  Note that no `e : Hₙ(Sⁿ; ℤ) ≅ ℤ` has to be *chosen*: the statement is
proved for every `e`, which is how the vendored `degreeOfIso` is set up, and
`degreeOfIso_well_defined` says the answer does not depend on it anyway.

The manuscript's local model at the mapping-torus zero,
`GroupApproximation.AlgTop.eulerLocalModelEquiv` in `AlgTop/EulerLocalModel.lean`, is a
real-linear isomorphism; normalizing it to the unit sphere gives exactly the kind of
self-homeomorphism this file is about.
-/

namespace GroupApproximation.AlgTop

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- If `a * b = 1` in `ℤ` then `b` is odd.  (An even factor would make the product
even, but `1` is not.) -/
theorem not_even_of_mul_eq_one {a b : ℤ} (h : a * b = 1) : ¬ Even b := by
  rintro ⟨r, rfl⟩
  refine Int.not_even_one ?_
  exact ⟨a * r, by rw [← h]; ring⟩

/-- **A self-map of `Sⁿ` with a left inverse has odd degree.**  The degree is
multiplicative and the identity has degree `1`, so `deg g * deg f = 1`; an even `deg f`
would make that product even. -/
theorem not_even_degreeOfIso_of_leftInverse {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)
    (f g : C(Sphere n, Sphere n)) (h : g.comp f = ContinuousMap.id (Sphere n)) :
    ¬ Even (degreeOfIso e f) := by
  have h1 : degreeOfIso e g * degreeOfIso e f = 1 := by
    rw [← degreeOfIso_comp, h, degreeOfIso_id]
  exact not_even_of_mul_eq_one h1

/-- **A self-homeomorphism of `Sⁿ` has odd degree.**  This is the local half of the
Euler-parity bridge: at a zero of a section whose derivative is invertible, the induced
self-map of the small sphere is a homeomorphism up to homotopy, so its mod-2 local
index is `1`. -/
theorem not_even_degreeOfIso_of_homeomorph {n : ℕ}
    (e : (singularHomologyℤ n).obj (TopCat.sphere.{0} n) ≅ ModuleCat.of ℤ ℤ)
    (φ : Sphere n ≃ₜ Sphere n) :
    ¬ Even (degreeOfIso e ⟨φ, φ.continuous⟩) := by
  refine not_even_degreeOfIso_of_leftInverse e ⟨φ, φ.continuous⟩
    ⟨φ.symm, φ.symm.continuous⟩ ?_
  ext x
  exact φ.symm_apply_apply x

end GroupApproximation.AlgTop
