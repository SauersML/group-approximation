import GroupApproximation.Analysis.ShulmanFillConjugatePair

/-!
# Exact commutation, and the unitary Shulman's proof actually conjugates by

`ShulmanFill.conjugateRepresentation` needs a unitary commuting with the image
of the amalgamated algebra.  This module supplies the elementary half: the
elements commuting with a self-adjoint set form a unital `*`-closed family,
conjugation by a unitary of that family fixes the set pointwise, and the
commutation hypothesis of `conjugateRepresentation` is membership in it.

## Correction to the route recorded earlier

An earlier note in this lane said the missing estimate was of
Haagerup--Thorbjørnsen type — random matrices, asymptotic freeness, generic
position.  That is **not** what Shulman's proof does, and no random matrix
appears anywhere in it.  Read from the paper (Shulman, *The MF property for
amalgamated free products*, arXiv:2603.13564v2, 22 March 2026):

* **Theorem 16** (p. 10) is proved in five lines: put
  `D = C*(φ_A(A), φ_B(B)) ⊂ ∏ M_n / ⊕ M_n`; then `A *_C B ⊂ D *_C D` by
  Theorem 13, and `D *_C D` is MF by Theorem 10 because `D` is a separable
  subalgebra of the corona, hence MF; the non-unital case is forced
  unitization plus Lemma 15.
* **Theorem 13** (p. 9) is *cited*, not proved: `([9, Th. 4.11])`.  It says
  that for unital inclusions `θ_A, θ_B, φ_A, φ_B` with
  `φ_A ∘ θ_A = φ_B ∘ θ_B` and `C` separable unital, `A *_C B` embeds into
  `D *_C D`; Remark 14 identifies the embedding as `φ_A * φ_B`.  Lemma 15
  (`A⁺ *_{C⁺} B⁺ = (A *_C B)⁺`) is cited to the same source.
* **Theorem 10** (p. 7--9), the symmetric case, is where the work is, and its
  conjugating unitary is completely explicit.  Let `π = π₁ * π₂ : A *_C A →
  B(H)` be an embedding and put `ρ₁ = π₁ ⊕ π₂`, `ρ₂ = π₂ ⊕ π₁`.  Then
  `(ρ₁ ⊕ ρ₁) * (ρ₂ ⊕ ρ₂)` is again an embedding, and `ρ₁ = u* ρ₂ u` for the
  **flip** `u = ((0,1),(1,0))`.  Because `π₁|_C = π₂|_C`, the element
  `ρ₂(c) = π₂(c) ⊕ π₁(c)` is diagonal, so `[ρ₂(c), u] = 0` — exactly.  The
  proof then lifts `ρ₂` to a contractive discrete asymptotic homomorphism
  (Theorem 4 of the paper, from Shulman [27, Th. 14], with Remark 6 for
  contractivity), lifts `u ⊕ -u*` to a unitary `V_k` with
  `‖[V_k, φ_k(c) ⊕ φ_k(c)]‖ ≤ 1/k` on a finite `F_k` (Lemma 9), sets
  `φ_k^{(2)} = φ_k ⊕ φ_k` and `φ_k^{(1)} = V_k* φ_k^{(2)} V_k`, checks that
  the two asymptotically agree on `C`, and glues them by Lemma 7.
* **Lemma 9** (p. 6--7) is the Halmos dilation: lift `u` to a contraction `X`,
  cut it down to `X̃ = X(1 - i_λ)` by a quasicentral approximate unit
  (Lemma 8), and set
  `V = ((X̃, √(1 - X̃X̃*)), (√(1 - X̃*X̃), -X̃*))`.  Pedersen's inequality
  `‖[A^{1/2}, B]‖ ≤ (5/4)‖[A, B]‖^{1/2}` controls the square-root corners.

So the atom is not an analytic estimate about generic position: it is the
flip, plus Halmos dilation, plus a quasicentral approximate unit.  The peer
lane's `ShulmanCoronaHalmos*`, `ShulmanHalmosDilation*` and
`ShulmanCoronaSquareRoot*` modules are Lemma 9; `ShulmanDenseCompatibility` is
the "asymptotically agree on `C`" step; `MFAlgebraAmalgamCriterion` is Lemma 7.
What no module covers yet is Theorem 4 — the lifting characterization of MF —
and the cited Theorem 13.

## What this module proves

The commutation bookkeeping around the flip, at the level of an arbitrary
self-adjoint set: elements commuting with it are closed under the algebra
operations and under the adjoint, conjugation by a unitary among them is the
identity on the set, and membership gives the hypothesis
`conjugateRepresentation` asks for.  The concrete flip itself lives in
`M₂` over the coefficient algebra: with `cStarDiagonal2` and `cStarMatrixUnit2`
of `Analysis/CStarMatrixTwoByTwo`, it is
`cStarMatrixUnit2 0 1 + cStarMatrixUnit2 1 0`, and what has to be checked is
that it is a self-adjoint unitary commuting with every `cStarDiagonal2 x x`.

This module is in the root import list.  It was authored while builds were
suspended and has not been elaborated.
-/

namespace GroupApproximation
namespace ShulmanFill

noncomputable section

variable {D : Type} [CStarAlgebra D]

/-- The elements commuting with every member of a set. -/
def CommutesWith (S : Set D) (x : D) : Prop := ∀ s ∈ S, x * s = s * x

theorem commutesWith_one (S : Set D) : CommutesWith S (1 : D) := by
  intro s _
  rw [one_mul, mul_one]

theorem commutesWith_zero (S : Set D) : CommutesWith S (0 : D) := by
  intro s _
  rw [zero_mul, mul_zero]

theorem CommutesWith.mul {S : Set D} {x y : D} (hx : CommutesWith S x)
    (hy : CommutesWith S y) : CommutesWith S (x * y) := by
  intro s hs
  rw [mul_assoc, hy s hs, ← mul_assoc, hx s hs, mul_assoc]

theorem CommutesWith.add {S : Set D} {x y : D} (hx : CommutesWith S x)
    (hy : CommutesWith S y) : CommutesWith S (x + y) := by
  intro s hs
  rw [add_mul, mul_add, hx s hs, hy s hs]

theorem CommutesWith.smul {S : Set D} {x : D} (hx : CommutesWith S x) (c : ℂ) :
    CommutesWith S (c • x) := by
  intro s hs
  rw [smul_mul_assoc, hx s hs, mul_smul_comm]

/-- Commuting with a self-adjoint set is preserved by the adjoint. -/
theorem CommutesWith.star {S : Set D} (hS : ∀ s ∈ S, star s ∈ S) {x : D}
    (hx : CommutesWith S x) : CommutesWith S (star x) := by
  intro s hs
  have h := congrArg star (hx (star s) (hS s hs))
  rw [star_mul, star_mul, star_star] at h
  exact h.symm

/-- **Conjugation by a unitary of the commutant is the identity on the set.**
This is the exact form of the compatibility that Shulman's flip has against
the image of the amalgamated algebra. -/
theorem unitaryConj_eq_self_of_commutesWith {S : Set D} (u : unitary D)
    (hu : CommutesWith S (u : D)) {s : D} (hs : s ∈ S) :
    unitaryConj u s = s := by
  show (u : D) * s * star (u : D) = s
  rw [hu s hs, mul_assoc, Unitary.mul_star_self_of_mem u.2, mul_one]

/-- The unitary group of the commutant is never empty. -/
theorem commutesWith_one_unitary (S : Set D) :
    CommutesWith S ((1 : unitary D) : D) := by
  have h : ((1 : unitary D) : D) = 1 := rfl
  rw [h]
  exact commutesWith_one S

variable {C A : Type} [CStarAlgebra C] [CStarAlgebra A]

/-- The image of the amalgamated algebra is self-adjoint. -/
theorem star_mem_range_amalgamated (iA : C →⋆ₐ[ℂ] A) (l : A →⋆ₐ[ℂ] D) :
    ∀ s ∈ Set.range fun c : C ↦ l (iA c),
      star s ∈ Set.range fun c : C ↦ l (iA c) := by
  rintro _ ⟨c, rfl⟩
  exact ⟨star c, by rw [map_star, map_star]⟩

/-- **The hypothesis of `conjugateRepresentation`, as commutant membership.**
A unitary commuting with the image of the amalgamated algebra may be applied to
one factor of a compatible pair. -/
theorem commutes_amalgamated_of_commutesWith (iA : C →⋆ₐ[ℂ] A)
    (l : A →⋆ₐ[ℂ] D) (u : unitary D)
    (hu : CommutesWith (Set.range fun c : C ↦ l (iA c)) (u : D)) :
    ∀ c : C, (u : D) * l (iA c) = l (iA c) * (u : D) :=
  fun c ↦ hu _ ⟨c, rfl⟩

/-- The compatible representation obtained by conjugating one factor by a
unitary of the commutant of the amalgamated image. -/
def conjugateRepresentationOfCommutant {B : Type} [CStarAlgebra B]
    [Nontrivial D] (iA : C →⋆ₐ[ℂ] A) (iB : C →⋆ₐ[ℂ] B)
    (l : A →⋆ₐ[ℂ] D) (r : B →⋆ₐ[ℂ] D) (hlr : l.comp iA = r.comp iB)
    (u : unitary D)
    (hu : CommutesWith (Set.range fun c : C ↦ l (iA c)) (u : D)) :
    CStarAmalgamRepresentation iA iB :=
  conjugateRepresentation iA iB l r hlr u
    (commutes_amalgamated_of_commutesWith iA l u hu)

end

end ShulmanFill
end GroupApproximation
