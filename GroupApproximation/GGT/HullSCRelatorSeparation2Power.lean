import GroupApproximation.GGT.HullSCRelatorSeparation2Core

/-!
# Passing to high powers of the two loxodromic elements

The design of `GGT/HullSCRelatorSeparation2Design.lean` chooses exponents
avoiding finitely many bad values, and that is enough for every clause it
carries -- except one, which no choice of exponent can reach.  The diagonal
`x · a^i · x' = a^i` has the solutions `x = a^k`, `x' = a^{-k}` for **every**
`i`, so a design that has to exclude the diagonal cannot do it by choosing `i`.

The lever that does reach it is the element rather than the exponent.  The
`d̂_λ`-ball of radius `eps` is finite and the powers of a loxodromic are
pairwise distinct, so only finitely many powers of `a_b` lie in the ball;
replacing `a_b` by `a_b^M` for `M` past all of them leaves the cyclic group it
generates meeting the ball only at `1`.  `exists_pow_avoiding_relBall` is that
choice.

`HypEmbeddedCore₂.powCore` is the replacement, and it costs nothing: the
relative generating set, the family, and the hyperbolic embedding are untouched
-- only the two distinguished elements change.  A positive power of a loxodromic
is loxodromic (`HullGeometry.isLoxodromic_pow`) and independence is inherited by
powers, so all three clauses about the elements survive.

`independent_pow₂` is proved here rather than imported: the corresponding lemma
lives in a module under active repair, and the proof is three lines from the
definition -- the Gromov products of the power-orbits of `a^k` and `b^l` are
among those of `a` and `b`, so the same constant serves.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section Power

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-- **Independence passes to powers.**  The orbit of a power is part of the
orbit, so the bound on the Gromov products is inherited. -/
theorem independent_pow₂ {a b : G} {x : X} (h : Independent a b x) (k l : ℕ) :
    Independent (a ^ k) (b ^ l) x := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun n m => ?_⟩
  rw [← zpow_natCast a k, ← zpow_natCast b l, ← zpow_mul, ← zpow_mul]
  exact hC ((k : ℤ) * n) ((l : ℤ) * m)

end Power

section Core

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

/-- **The core with both elements replaced by their `M`-th powers.**

Everything but the two elements is carried over unchanged; the three clauses
about the elements are the three lemmas above. -/
def HypEmbeddedCore₂.powCore (E : HypEmbeddedCore₂ A N) {M : ℕ} (hM : 0 < M) :
    HypEmbeddedCore₂ A N where
  rel := E.rel
  base_eq := E.base_eq
  H := E.H
  fam_eq := E.fam_eq
  le := E.le
  embedded := E.embedded
  lox := fun b => E.lox b ^ M
  lox_mem := fun b => pow_mem (E.lox_mem b) M
  lox_isLoxodromic := fun b => isLoxodromic_pow (E.lox_isLoxodromic b) hM
  lox_independent := independent_pow₂ E.lox_independent M M

@[simp]
theorem HypEmbeddedCore₂.powCore_lox (E : HypEmbeddedCore₂ A N) {M : ℕ}
    (hM : 0 < M) (b : Bool) : (E.powCore hM).lox b = E.lox b ^ M := rfl

@[simp]
theorem HypEmbeddedCore₂.powCore_rel (E : HypEmbeddedCore₂ A N) {M : ℕ}
    (hM : 0 < M) : (E.powCore hM).rel = E.rel := rfl

end Core

section Avoid

variable {G : Type u} [Group G]

/-- **A power whose own powers miss the relative ball.**

Only finitely many powers of a loxodromic lie in the `d̂`-ball of radius `eps`,
that ball being finite and the powers pairwise distinct, so past the largest of
them every multiple is outside.  This is what excludes the solutions of the
diagonal that the choice of exponent cannot. -/
theorem exists_pow_avoiding_relBall {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n)) (eps : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (s : Bool) (k : ℕ), 0 < k →
      a s ^ (M * k) ∉ D.relBall s eps := by
  have hpre : ∀ s : Bool,
      ((fun n : ℕ => a s ^ n) ⁻¹' (D.relBall s eps)).Finite :=
    fun s => Set.Finite.preimage (fun _ _ _ _ hxy => hinj s hxy)
      (hemb.locallyFinite s eps)
  obtain ⟨T₀, hT₀⟩ := (hpre false).bddAbove
  obtain ⟨T₁, hT₁⟩ := (hpre true).bddAbove
  refine ⟨T₀ + T₁ + 1, by omega, ?_⟩
  intro s k hk hmem
  have hMk : T₀ + T₁ + 1 ≤ (T₀ + T₁ + 1) * k :=
    Nat.le_mul_of_pos_right _ hk
  cases s with
  | false =>
      have hle := hT₀ (show (T₀ + T₁ + 1) * k ∈ _ from hmem)
      omega
  | true =>
      have hle := hT₁ (show (T₀ + T₁ + 1) * k ∈ _ from hmem)
      omega

end Avoid

end HullSC
end GroupApproximation
