import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVLowKZero.Absorb
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finitely generated projective modules over a Leavitt ring are retracts of `R`

`simple_kazhdan_sofic_group.tex`, `sec:questions`, l.733-735 (Q2). Work order WO-LVLowK-1.

Let `R` carry a binary Leavitt family and let `P` be a finitely generated projective left
`R`-module. A surjection `Rⁿ → P` splits, and `Rⁿ⁺¹ ≅ R`, so there are `R`-linear maps
`p : R → P` and `s : P → R` with `p ∘ s = id` (`exists_retraction_regular`). The endomorphism
`s ∘ p` of the left module `R` is right multiplication by the idempotent `e = s (p 1)`
(`retraction_mul`, `isIdempotentElem_retraction`), so `P ≅ Re`.

`absorbsRegular_of_retraction` turns four elements `a, b, c, d` of `R` with

  `a b = e`, `b e = b`, `c b = 0`, `a d = 0`, `c d = 1`, `b a + d c = 1`

into an isomorphism `P ⊕ R ≅ R`, namely `(x, r) ↦ s(x) a + r c` with inverse
`r ↦ (p (r b), r d)`. The predicate `IdempotentAbsorbs e` records these six equations: it says
that `e` is Murray-von Neumann equivalent to the complement `1 - d c` of the range of an
isometry `d` (`c d = 1`).
-/

namespace GroupApproximation.Full.LVLowKZero

universe u v

variable {R : Type u} [Ring R]

/-- **An idempotent absorbing the unit**: `e ⊕ 1 ∼ 1` in the Murray-von Neumann sense, witnessed
by `a ∈ eR`, `b ∈ Re` and an isometry `d` (`c d = 1`) whose range complement `1 - d c` is
equivalent to `e` (`simple_kazhdan_sofic_group.tex` l.733-735). -/
def IdempotentAbsorbs (e : R) : Prop :=
  ∃ a b c d : R, a * b = e ∧ b * e = b ∧ c * b = 0 ∧ a * d = 0 ∧ c * d = 1 ∧
    b * a + d * c = 1

/-- `0` absorbs the unit: take `a = b = 0`, `c = d = 1`. -/
theorem idempotentAbsorbs_zero : IdempotentAbsorbs (0 : R) :=
  ⟨0, 0, 1, 1, mul_zero 0, zero_mul 0, mul_zero 1, zero_mul 1, mul_one 1, by
    rw [zero_mul, zero_add, mul_one]⟩

section Retraction

variable {P : Type v} [AddCommGroup P] [Module R P]

/-- The composite `s ∘ p` of a retraction pair is right multiplication by `s (p 1)`. -/
theorem retraction_mul (p : R →ₗ[R] P) (s : P →ₗ[R] R) (t : R) : s (p t) = t * s (p 1) := by
  calc s (p t) = s (p (t • (1 : R))) := by rw [smul_eq_mul, mul_one]
    _ = t • s (p 1) := by rw [map_smul, map_smul]
    _ = t * s (p 1) := smul_eq_mul t (s (p 1))

/-- The element `s (p 1)` of a retraction pair `p ∘ s = id` is idempotent. -/
theorem isIdempotentElem_retraction (p : R →ₗ[R] P) (s : P →ₗ[R] R)
    (hs : p ∘ₗ s = LinearMap.id) : IsIdempotentElem (s (p 1)) := by
  have hps : p (s (p 1)) = p 1 := LinearMap.congr_fun hs (p 1)
  show s (p 1) * s (p 1) = s (p 1)
  rw [← retraction_mul p s (s (p 1)), hps]

/-- **The absorption isomorphism.** If `p ∘ s = id` and `e = s (p 1)` absorbs the unit, then
`P ⊕ R ≅ R`. -/
theorem absorbsRegular_of_retraction (p : R →ₗ[R] P) (s : P →ₗ[R] R)
    (hs : p ∘ₗ s = LinearMap.id) (h : IdempotentAbsorbs (s (p 1))) :
    AbsorbsRegular R P := by
  obtain ⟨a, b, c, d, hab, hbe, hcb, had, hcd, hsum⟩ := h
  have hps : ∀ x : P, p (s x) = x := fun x => LinearMap.congr_fun hs x
  refine ⟨
    { toFun := fun y => s y.1 * a + y.2 * c
      map_add' := ?_
      map_smul' := ?_
      invFun := fun r => (p (r * b), r * d)
      left_inv := ?_
      right_inv := ?_ }⟩
  · intro y z
    show s (y.1 + z.1) * a + (y.2 + z.2) * c = s y.1 * a + y.2 * c + (s z.1 * a + z.2 * c)
    rw [map_add, add_mul, add_mul]
    exact add_add_add_comm _ _ _ _
  · intro r y
    show s (r • y.1) * a + (r • y.2) * c = r • (s y.1 * a + y.2 * c)
    rw [map_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_add, mul_assoc, mul_assoc]
  · intro y
    refine Prod.ext ?_ ?_
    · show p ((s y.1 * a + y.2 * c) * b) = y.1
      calc p ((s y.1 * a + y.2 * c) * b) = p (s y.1 * s (p 1)) := by
            rw [add_mul, mul_assoc, mul_assoc, hab, hcb, mul_zero, add_zero]
        _ = p (s (p (s y.1))) := by rw [← retraction_mul p s (s y.1)]
        _ = y.1 := by rw [hps, hps]
    · show (s y.1 * a + y.2 * c) * d = y.2
      rw [add_mul, mul_assoc, mul_assoc, had, hcd, mul_zero, mul_one, zero_add]
  · intro r
    show s (p (r * b)) * a + r * d * c = r
    calc s (p (r * b)) * a + r * d * c = r * b * a + r * d * c := by
          rw [retraction_mul p s (r * b), mul_assoc r b (s (p 1)), hbe]
      _ = r := by rw [mul_assoc, mul_assoc, ← mul_add, hsum, mul_one]

end Retraction

/-- **Every finitely generated projective module over a Leavitt ring is a retract of `R`.**
A surjection `Rⁿ → P` factors through `Rⁿ⁺¹ ≅ R` (`LeavittFamily.nonempty_linearEquiv_finSucc`)
and splits by projectivity. -/
theorem exists_retraction_regular (L : LeavittFamily R) (P : Type v) [AddCommGroup P]
    [Module R P] [Module.Finite R P] [Module.Projective R P] :
    ∃ (p : R →ₗ[R] P) (s : P →ₗ[R] R), p ∘ₗ s = LinearMap.id := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R P
  obtain ⟨φ⟩ := L.nonempty_linearEquiv_finSucc n
  let g : (Fin (n + 1) → R) →ₗ[R] P := f ∘ₗ LinearMap.funLeft R R (Fin.castSucc (n := n))
  have hg : Function.Surjective g :=
    hf.comp (LinearMap.funLeft_surjective_of_injective R R (Fin.castSucc (n := n))
      (Fin.castSucc_injective n))
  let p : R →ₗ[R] P := g ∘ₗ φ.toLinearMap
  have hp : Function.Surjective p := hg.comp φ.surjective
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective p (LinearMap.range_eq_top.2 hp)
  exact ⟨p, s, hs⟩

/-- **`K₀(R) = 0` from idempotent absorption.** Over a ring with a binary Leavitt family, if
every idempotent `e` absorbs the unit (`IdempotentAbsorbs e`), then every f.g. projective module
`P` satisfies `P ⊕ R ≅ R`, so every class `[P]` vanishes and `K₀(R) = 0`
(`simple_kazhdan_sofic_group.tex` l.733-735). -/
theorem absorbsRegular_of_forall_idempotentAbsorbs (L : LeavittFamily R)
    (h : ∀ e : R, IsIdempotentElem e → IdempotentAbsorbs e) (P : Type v) [AddCommGroup P]
    [Module R P] [Module.Finite R P] [Module.Projective R P] : AbsorbsRegular R P := by
  obtain ⟨p, s, hs⟩ := exists_retraction_regular L P
  exact absorbsRegular_of_retraction p s hs (h _ (isIdempotentElem_retraction p s hs))

end GroupApproximation.Full.LVLowKZero
