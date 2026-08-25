import GroupApproximation.Steinberg.ElementaryIndexPadding
import GroupApproximation.Steinberg.GeneralRankElementaryPropertyT
import GroupApproximation.PropertyT.FiniteFieldElementaryPropertyT

/-!
# Property `(T)` for `EL_n(R)` in every rank, in every prime characteristic

`Steinberg/GeneralRankElementaryPropertyT.lean` proves the Ershov--
Jaikin-Zapirain theorem for `EL_n(R)`, every `n ≥ 3`, over every finite-type
`ZMod 2`-algebra.  Its own docstring identifies exactly what stops the
argument from reaching a general coefficient field, and it is not the
analysis:

* the **Kazhdan-subset half** (`blockElementary_exists_rootSet_isKazhdan`) is
  already characteristic-free -- it needs only `CharP R p` with `0 < p`;
* the **control half** was pinned to `ZMod 2` only because the one rank-`n`
  control set in the tree, `SteinbergHigherRankFiniteControl.finiteControlSetAt`,
  lives over `FreeAlgebra (ZMod 2) X`.

Meanwhile `PropertyT/FiniteFieldElementaryPropertyT.lean` already proves the
control estimate over **every** finite field -- with a genuine additive
character `ψ : AddChar K ℂ` and the character gap `CharacterMass.gap ψ` in
place of the characteristic-two sign characters -- but only at `Fin 3`, and
the deep estimate it rests on (`FreeRootPlaneMass.norm_joinRootMovingProjection_sq_le_explicit_errors`)
is hard-wired to `Fin 3` and cannot be restated generically.  What was missing
was a homomorphism `EL₃(A) →* EL_n(A)` to transport it along.

`Steinberg/ElementaryIndexPadding.lean` supplies that homomorphism
(`ElementaryPadding.elementaryPad`), and this file spends it.

## Main results

* `paddedControlSet` -- scalar-unit and free-generator coefficients in
  *every* ordered root of `EL_n(FreeAlgebra K X)`, a finite set.
* `paddedControlSet_controls_rootSet` -- it controls displacement by every
  ordinary elementary root at rank `n`, with the rank-three constant
  unchanged.  Each root `(u, v)` is reached by padding along the embedding
  `Fin 3 ↪ Fin n` determined by `u`, a third index, and `v`.
* `paddedControlSet_controls_blockRootSet` -- the same finite set controls
  the six *rectangular block* roots, with the finite loss `n²`.
* `freeGeneralRankFiniteField_hasKazhdanPropertyT` and
  `finiteFieldGeneralRankElementary_hasKazhdanPropertyT` -- **property `(T)`
  for `EL_n(A)` in every rank `n ≥ 3`, over every finite-type algebra over
  every finite field.**
* `primeCharGeneralRankElementary_hasKazhdanPropertyT` -- the same conclusion
  phrased for a ring of prime characteristic, which is automatically an
  algebra over the finite field `ZMod p`.

## What this does *not* cover

Positive characteristic that is not prime (say a `ZMod 4`-algebra) is out of
reach here: the Kazhdan-subset half accepts any `0 < p`, but the control half
needs a coefficient **field**, because `CharacterMass.gap` and the finite
dual sum of `PropertyT/CharacterMass.lean` need one.  Characteristic zero is
untouched: `PropertyT/IntegralCharacterMass.lean` isolates the missing input
there (`ColumnPlaneMassBound` over `FreeAlgebra ℤ X`, an equidistribution
estimate on a torus), and nothing in this file bears on it.
-/

namespace GroupApproximation
namespace GeneralRankFiniteField

open FiniteFieldElementaryPropertyT
open SteinbergHigherRankFiniteControl

noncomputable section

variable (X : Type*) [Fintype X]
variable (K : Type*) [Field K] [Fintype K]

/-! ### The rank-`n` control set -/

/-- One member of the rank-`n` control set: a scalar unit or a free
generator, placed in a chosen ordered root of `EL_n`. -/
def paddedControlElement (n : ℕ)
    (p : IndexedRoot (Fin n) × (K ⊕ Fin (Fintype.card X))) :
    elementaryGroup (Fin n) (FreeAlgebra K X) :=
  elementaryRoot p.1.1.1 p.1.1.2 p.1.2 (controlCoefficient X K p.2)

/-- Scalar-unit and free-generator coefficients in every ordered root of
`EL_n(FreeAlgebra K X)`. -/
def paddedControlSet (n : ℕ) :
    Finset (elementaryGroup (Fin n) (FreeAlgebra K X)) := by
  classical
  exact (Finset.univ : Finset
    (IndexedRoot (Fin n) × (K ⊕ Fin (Fintype.card X)))).image
      (paddedControlElement X K n)

theorem paddedControlElement_mem (n : ℕ)
    (p : IndexedRoot (Fin n) × (K ⊕ Fin (Fintype.card X))) :
    paddedControlElement X K n p ∈ paddedControlSet X K n := by
  classical
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩

/-! ### Transport of the rank-three estimate -/

/-- **The rank-`n` control estimate over every finite field.**  The
rank-three constant is unchanged: each ordered root of `EL_n` sits inside an
embedded rank-three elementary subgroup, and the padded control set restricts
to the rank-three control set there. -/
theorem paddedControlSet_controls_rootSet (n : ℕ) (hn : 3 ≤ n)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) :
    ControlsSubsetDisplacement
      (elementaryGroup (Fin n) (FreeAlgebra K X))
      (paddedControlSet X K n)
      (elementaryRootSet (Fin n) (FreeAlgebra K X))
      (2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
        6 * Fintype.card X + 4) + 1 : ℝ) := by
  classical
  intro E _ _ _ rho z hz δ hδ hnear g hg
  obtain ⟨u, v, huv, a, rfl⟩ := hg
  obtain ⟨w, hwu, hwv⟩ := Fin.exists_ne_and_ne_of_two_lt u v (by omega)
  let e : Fin 3 ↪ Fin n := tripleEmbedding u w v hwu.symm huv hwv
  let rho3 : elementaryGroup (Fin 3) (FreeAlgebra K X) →* (E ≃ₗᵢ[ℝ] E) :=
    rho.comp (ElementaryPadding.elementaryPad e)
  have hnear3 : ∀ s ∈ controlSet X K, ‖rho3 s z - z‖ < δ := by
    intro s hs
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hs
    have hmap : ElementaryPadding.elementaryPad e (controlElement X K p) =
        paddedControlElement X K n
          (⟨(e p.1.1.1, e p.1.1.2), e.injective.ne p.1.2⟩, p.2) := by
      simp [controlElement, paddedControlElement]
    show ‖rho (ElementaryPadding.elementaryPad e (controlElement X K p)) z - z‖ < δ
    rw [hmap]
    exact hnear _ (paddedControlElement_mem X K n _)
  have hg3 : elementaryRoot (0 : Fin 3) 2 (by decide) a ∈
      (elementaryA2System (FreeAlgebra K X)).rootSet :=
    ⟨0, 2, by decide, a, rfl⟩
  have hmove := controlSet_controls_rootSet X K ψ hψ E rho3 z hz δ hδ hnear3 _ hg3
  simpa [rho3, e] using hmove

/-- The same finite set controls the six rectangular block roots of
`EL_n(FreeAlgebra K X)`, with only the finite loss `n²`. -/
theorem paddedControlSet_controls_blockRootSet (n : ℕ) (hn : 3 ≤ n)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) :
    ControlsSubsetDisplacement
      (elementaryGroup (Fin n) (FreeAlgebra K X))
      (paddedControlSet X K n)
      (BlockElementary.blockElementaryA2System (FreeAlgebra K X) n hn).rootSet
      ((n * n : ℕ) * (2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
        6 * Fintype.card X + 4) + 1 : ℝ) + 1) := by
  intro E _ _ _ rho z hz δ hδ hnear g hg
  obtain ⟨i, j, hij, hgm⟩ := hg
  have hord := paddedControlSet_controls_rootSet X K n hn ψ hψ E rho z hz δ hδ hnear
  have hgap := CharacterMass.gap_pos ψ
  have hginv : (0 : ℝ) < (CharacterMass.gap ψ)⁻¹ := by positivity
  have hcardK : (0 : ℝ) ≤ Fintype.card K := by positivity
  have hcardX : (0 : ℝ) ≤ Fintype.card X := by positivity
  have hCpos : (0 : ℝ) < 2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
      6 * Fintype.card X + 4) + 1 := by positivity
  have hD : (0 : ℝ) ≤ (2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
      6 * Fintype.card X + 4) + 1 : ℝ) * δ := le_of_lt (mul_pos hCpos hδ)
  have hroot : ∀ (u v : Fin n) (huv : u ≠ v) (c : FreeAlgebra K X),
      ‖rho (elementaryRoot u v huv c) z - z‖ ≤
        (2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
          6 * Fintype.card X + 4) + 1 : ℝ) * δ := by
    intro u v huv c
    exact le_of_lt (hord _ ⟨u, v, huv, c, rfl⟩)
  have hbound := BlockElementary.norm_blockRoot_displacement_le
    (blk := BlockElementary.finBlock n) hij rho z _ hD hroot g hgm
  rw [Fintype.card_fin] at hbound
  nlinarith [hbound, hδ, hCpos]

/-! ### The Kazhdan pair and property `(T)` -/

/-- The padded control set is a genuine finite Kazhdan pair for `EL_n` of the
free algebra of a finite field, in every rank `n ≥ 3`. -/
theorem paddedControlSet_isKazhdanPair (n : ℕ) (hn : 3 ≤ n) :
    ∃ epsilon : ℝ,
      IsKazhdanPair (elementaryGroup (Fin n) (FreeAlgebra K X))
        (paddedControlSet X K n) epsilon := by
  obtain ⟨ψ, hψ⟩ := CharacterMass.exists_addChar_ne_one K
  have hprime : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  obtain ⟨kappa, hkappa⟩ :=
    BlockElementary.blockElementary_exists_rootSet_isKazhdan
      (FreeAlgebra K X) (ringChar K) hprime.pos n hn
  have hgap := CharacterMass.gap_pos ψ
  have hginv : (0 : ℝ) < (CharacterMass.gap ψ)⁻¹ := by positivity
  have hcardK : (0 : ℝ) ≤ Fintype.card K := by positivity
  have hcardX : (0 : ℝ) ≤ Fintype.card X := by positivity
  have hC : (0 : ℝ) < (n * n : ℕ) *
      (2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
        6 * Fintype.card X + 4) + 1 : ℝ) + 1 := by positivity
  exact ⟨kappa / (2 * ((n * n : ℕ) *
      (2 * (8 * (CharacterMass.gap ψ)⁻¹ * Fintype.card K +
        6 * Fintype.card X + 4) + 1 : ℝ) + 1)),
    IsKazhdanSubset.to_pair_of_controls hkappa hC
      (paddedControlSet_controls_blockRootSet X K n hn ψ hψ)⟩

/-- Elementary rank `n ≥ 3` over the free algebra of a finite field on a
finite alphabet has Kazhdan's property `(T)`. -/
theorem freeGeneralRankFiniteField_hasKazhdanPropertyT (n : ℕ) (hn : 3 ≤ n) :
    HasKazhdanPropertyT (elementaryGroup (Fin n) (FreeAlgebra K X)) := by
  obtain ⟨epsilon, hpair⟩ := paddedControlSet_isKazhdanPair X K n hn
  exact ⟨paddedControlSet X K n, epsilon, hpair⟩

end

end GeneralRankFiniteField

/-- **The Ershov--Jaikin-Zapirain theorem in every rank over every finite
field**: the elementary group `EL_n(A)`, for every `n ≥ 3`, of any
finite-type algebra over any finite field has Kazhdan's property `(T)`.

Rank three is `finiteFieldElementaryThree_hasKazhdanPropertyT`; the higher
ranks are new, and unlike `SteinbergHigherRankPropertyT` they need no
`CompleteMatrixFamily`, and unlike
`BlockElementary.finiteTypeCharTwoElementary_hasKazhdanPropertyT` they are not
restricted to characteristic two. -/
theorem finiteFieldGeneralRankElementary_hasKazhdanPropertyT
    {k A : Type} [Field k] [Finite k] [Ring A] [Algebra k A]
    [Algebra.FiniteType k A] (n : ℕ) (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) A) := by
  letI : Fintype k := Fintype.ofFinite k
  obtain ⟨X, hX, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_freeAlgebra'
      (R := k) (A := A)).mp inferInstance
  letI : Fintype X := hX
  exact HasKazhdanPropertyT.of_surjective
    (elementaryGroupMap (ι := Fin n) f.toRingHom)
    (elementaryGroupMap_surjective_of_surjective f.toRingHom hf)
    (GeneralRankFiniteField.freeGeneralRankFiniteField_hasKazhdanPropertyT X k n hn)

/-- The general-rank, finite-coefficient-field form of the
Ershov--Jaikin-Zapirain theorem proved in this file.

The printed Ershov--Jaikin-Zapirain statement is stronger in the base ring:
it allows every finitely generated unital associative ring, in particular
characteristic zero.  Nothing here addresses that axis; see the module
docstring. -/
def GeneralRankFiniteFieldElementaryPropertyT : Prop :=
  ∀ (k A : Type) [Field k] [Finite k] [Ring A] [Algebra k A]
    [Algebra.FiniteType k A] (n : ℕ), 3 ≤ n →
      HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) A)

theorem generalRankFiniteFieldElementaryPropertyT :
    GeneralRankFiniteFieldElementaryPropertyT := by
  intro k A hk hkfin hA hAlg hFT n hn
  exact @finiteFieldGeneralRankElementary_hasKazhdanPropertyT k A hk hkfin hA hAlg hFT n hn

/-- **Every prime characteristic.**  A ring of prime characteristic `p` is an
algebra over the finite field `ZMod p`, so the finite-field theorem applies
verbatim.  This is the "arbitrary positive characteristic" form: only the
non-prime positive characteristics (a `ZMod 4`-algebra, say) are missed, and
they are missed because the control half needs a coefficient field. -/
theorem primeCharGeneralRankElementary_hasKazhdanPropertyT
    (p : ℕ) (hp : p.Prime) (A : Type) [Ring A] [CharP A p]
    (hfin : @Algebra.FiniteType (ZMod p) A _ _ (ZMod.algebra A p))
    (n : ℕ) (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, 0} (elementaryGroup (Fin n) A) := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) A := ZMod.algebra A p
  haveI : Algebra.FiniteType (ZMod p) A := hfin
  exact finiteFieldGeneralRankElementary_hasKazhdanPropertyT (k := ZMod p) n hn

end GroupApproximation
