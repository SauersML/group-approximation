import GroupApproximation.Pestov91.Kazhdan
import GroupApproximation.Kazhdan.KazhdanComplex

/-!
# Property `(T)` for the Pestov 9.1 witness, in the complex-unitary form

Pestov's Open Question 9.1 (arXiv:0804.3968v8, p. 21) is about Kazhdan's
property `(T)` in the sense of Bekka--de la Harpe--Valette, Definition 1.1.3:
unitary representations on *complex* Hilbert spaces.  The repository's
`HasKazhdanPropertyT` quantifies over real Hilbert spaces instead.  The two
agree with the same control set and the same tolerance
(`hasKazhdanPropertyT_iff_complex`, proved by realification in one direction
and complexification in the other), so every endpoint of
`GroupApproximation.Pestov91.Kazhdan` has a complex-unitary twin, recorded
here.

At universes `{0, 0}`, `HasKazhdanPropertyTComplex G` asks for a finite set
`Q` and a tolerance `ε > 0` such that every unitary representation
`G →* (E ≃ₗᵢ[ℂ] E)` on a complex Hilbert space `E : Type` with a
`(Q, ε)`-almost invariant unit vector has a nonzero invariant vector.  That is
the definition a statement of Question 9.1 over `Type` writes down, so these
endpoints close it by unfolding.
-/

namespace GroupApproximation

namespace Pestov91

/-- **`EL_n(A)` has property `(T)` in the complex-unitary form**, for every
finitely generated unital ring `A` and every rank `n ≥ 3`. -/
theorem elementary_hasKazhdanPropertyTComplex {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A) {n : ℕ} (hn : 3 ≤ n) :
    HasKazhdanPropertyTComplex.{0, 0} ↥(elementaryGroup (Fin n) A) :=
  hasKazhdanPropertyT_iff_complex.mp (elementary_hasKazhdanPropertyT hA hn)

/-- **The interface for the witness group, complex-unitary form.**  Any group
carrying a surjection from `EL_n(A)` has property `(T)`, for `A` finitely
generated and `n ≥ 3`. -/
theorem hasKazhdanPropertyTComplex_of_surjective {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A) {n : ℕ} (hn : 3 ≤ n)
    {S : Type} [Group S] (f : ↥(elementaryGroup (Fin n) A) →* S)
    (hf : Function.Surjective f) :
    HasKazhdanPropertyTComplex.{0, 0} S :=
  hasKazhdanPropertyT_iff_complex.mp (hasKazhdanPropertyT_of_surjective hA hn f hf)

/-- **`EL_n(A)/Z(EL_n(A))` has property `(T)` in the complex-unitary form**,
for every finitely generated unital ring `A` and every rank `n ≥ 3`. -/
theorem elementaryModCentre_hasKazhdanPropertyTComplex {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A) {n : ℕ} (hn : 3 ≤ n) :
    HasKazhdanPropertyTComplex.{0, 0}
      (↥(elementaryGroup (Fin n) A) ⧸
        Subgroup.center ↥(elementaryGroup (Fin n) A)) :=
  hasKazhdanPropertyT_iff_complex.mp (elementaryModCentre_hasKazhdanPropertyT hA hn)

/-- `EL_n(A)/N` has property `(T)` in the complex-unitary form, for every
normal subgroup `N`. -/
theorem elementaryModNormal_hasKazhdanPropertyTComplex {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A) {n : ℕ} (hn : 3 ≤ n)
    (N : Subgroup ↥(elementaryGroup (Fin n) A)) [N.Normal] :
    HasKazhdanPropertyTComplex.{0, 0} (↥(elementaryGroup (Fin n) A) ⧸ N) :=
  hasKazhdanPropertyT_iff_complex.mp (elementaryModNormal_hasKazhdanPropertyT hA hn N)

/-- Calibration at `A = ℤ`: `EL₃(ℤ)/Z(EL₃(ℤ))` has property `(T)` in the
complex-unitary form. -/
theorem intElementaryModCentre_hasKazhdanPropertyTComplex :
    HasKazhdanPropertyTComplex.{0, 0}
      (↥(elementaryGroup (Fin 3) ℤ) ⧸
        Subgroup.center ↥(elementaryGroup (Fin 3) ℤ)) :=
  hasKazhdanPropertyT_iff_complex.mp intElementaryModCentre_hasKazhdanPropertyT

end Pestov91

end GroupApproximation
