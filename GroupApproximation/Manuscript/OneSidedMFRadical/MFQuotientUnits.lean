import GroupApproximation.Manuscript.OneSidedMFRadical.MFHomKernel
import GroupApproximation.Algebra.FinitelyGeneratedAbelianResiduallyFinite

/-!
# `thm:mf-quotient-units`: MF quotients of unit groups

`non_mf_groups_exist.tex`, Theorem `thm:mf-quotient-units`:

> Let `R` be a countable purely infinite simple ring, let `n ≥ 1`, and let `N_n`
> be the intersection of the kernels of all homomorphisms from `GL_n(R)` to MF
> groups.  Then `N_n = [GL_n(R), GL_n(R)]` and `GL_n(R)/N_n ≅ K_1(R)`, a
> countable abelian group, which is MF.

`mfHomKernel` is the printed `N_n`; it is the paper's `Rad_MF` for the group
`GL_n(R)`, in the same quantification the tree's other endpoints use
(`∀ (M : Type) [Group M], IsOperatorMF M → …`, as in
`FullDefectRing.manuscriptSaturatedPrintedDefectRadical`).

## What is quoted and what is proved

Quoted, each as one named proposition with its provenance:

* `AGPMatrixReduction` --- Ara--Goodearl--Pardo Corollary 1.7, the printed "the
  ring `M_n(R)` is again countable, purely infinite, and simple".
* `AGPUnitK1` --- AGP Theorem 2.4, the printed "`κ` is surjective with kernel
  `[H,H]`", packaged so that `K_1(R)` is supplied as an abstract countable
  abelian group rather than constructed as `lim GL_n/EL_n`.
* `AGPMenalMoncasiReduction` --- AGP Theorem 2.4 Step 2 with the elementary
  reduction of Menal and Moncasi, the printed "`u = PvQ` … so `u ≡ v` modulo
  `N`".
* `AGPStepOne` --- AGP Theorem 2.4 Step 1, the printed last paragraph.
* `CountableAbelianMF` --- the printed "a countable abelian group `A` is MF".
  This one is *not* a literature input: it is discharged below by
  `countableAbelianMF`, from
  `Algebra.FinitelyGeneratedAbelianResiduallyFinite`.  It survives as a named
  proposition only because the `n = 1` theorem is stated with it explicit.

Proved here: everything else, including the two containments that make up the
theorem.  `eq:corner-units` is `MFHomKernel.cornerUnitSubgroup_le_mfHomKernel`,
which is where Theorem `thm:full-defect-ring` enters.

## One place this is weaker than the print

The printed conclusion identifies the quotient with `K_1(R)` on the nose.  The
statement below gives a countable abelian MF group and an isomorphism onto it,
which is what the proof produces once `K_1` is packaged abstractly inside
`AGPUnitK1`.  Naming that group `K_1(R)` needs the colimit `lim GL_n/EL_n` and,
for `n ≥ 2`, the Morita isomorphism `K_1(M_n R) ≅ K_1(R)`; neither is built
here, and neither is used anywhere else in the printed proof.  `n ≥ 2` is
handled by applying the `n = 1` argument to the ring `M_n(R)`, whose unit group
*is* `GL_n(R)`, so the Morita step is not needed for the shape stated.
-/

namespace GroupApproximation
namespace MFQuotientUnits

open Manuscript.OneSidedMFRadical

/-! ### The quoted inputs -/

/-- **Ara--Goodearl--Pardo, Corollary 1.7.**  Matrix rings over a countable
purely infinite simple ring are again purely infinite simple.  Countability of
`M_n(R)` is automatic and is not part of the statement. -/
def AGPMatrixReduction : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ n : ℕ, 1 ≤ n →
      IsPurelyInfiniteSimpleRing (Matrix (Fin n) (Fin n) R)

/-- **Ara--Goodearl--Pardo, Theorem 2.4.**  The canonical map `κ : Rˣ → K_1(R)`
is surjective with kernel the commutator subgroup, and `K_1(R)` is countable
abelian.

`K_1(R)` is supplied as an abstract group rather than constructed: the printed
proof uses nothing about it beyond these three properties. -/
def AGPUnitK1 : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∃ (A : Type) (_ : CommGroup A) (_ : Countable A) (κ : Rˣ →* A),
      Function.Surjective κ ∧ κ.ker = commutator Rˣ

/-- **Ara--Goodearl--Pardo, Theorem 2.4, Step 2, with the elementary reduction
of Menal and Moncasi.**  Every element of `ker κ` agrees, modulo the corner
units, with one supported off a nonzero idempotent.

This is the printed "`u = PvQ`, where `P` and `Q` are products of elementary
matrices of this matrix ring and `v = e_1 + (1-e_1)v(1-e_1)`", together with
the sentence that follows it, which puts `P` and `Q` into the corner-unit
subgroup. -/
def AGPMenalMoncasiReduction : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (A : Type) [CommGroup A] (κ : Rˣ →* A), Function.Surjective κ →
      κ.ker = commutator Rˣ →
        ∀ u ∈ κ.ker, ∃ (v : Rˣ) (e : R), e ≠ 0 ∧ IsIdempotentElem e ∧
          (v : R) = e + (1 - e) * (v : R) * (1 - e) ∧
          u * v⁻¹ ∈ cornerUnitSubgroup R

/-- **Ara--Goodearl--Pardo, Theorem 2.4, Step 1.**  A unit supported off a
nonzero idempotent and killed by `κ` is a corner unit.

This is the printed last paragraph: `diag(v,1,…,1) ∈ EL_n(R)` for some `n ≥ 2`,
and the idempotent decomposition and ring isomorphism `θ` that carry it back to
`v = 1 - P + θ(diag(v,1,…,1))`. -/
def AGPStepOne : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ (A : Type) [CommGroup A] (κ : Rˣ →* A), Function.Surjective κ →
      κ.ker = commutator Rˣ →
        ∀ (v : Rˣ) (e : R), e ≠ 0 → IsIdempotentElem e →
          (v : R) = e + (1 - e) * (v : R) * (1 - e) → κ v = 1 →
            v ∈ cornerUnitSubgroup R

/-- **The printed "a countable abelian group `A` is MF".**  Not a literature
input: `countableAbelianMF` below proves it. -/
def CountableAbelianMF : Prop :=
  ∀ (A : Type) [CommGroup A] [Countable A], IsOperatorMF A

/-- The printed sentence, proved.  The print argues through residual
finite-dimensionality of `C*_max(A)` and Brown--Kirchberg; the proof used here
runs through LEF and residual finiteness of finitely generated abelian groups,
so it quotes nothing. -/
theorem countableAbelianMF : CountableAbelianMF := fun A _ _ ↦
  isOperatorMF_of_commGroup_countable A

/-! ### The theorem at `n = 1` -/

/-- **`thm:mf-quotient-units` at `n = 1`.**  For a countable purely infinite
simple ring, the intersection of the kernels of all homomorphisms from `Rˣ` to
MF groups is the commutator subgroup, and the quotient is a countable abelian
MF group. -/
theorem mfHomKernel_units_eq_commutator
    (hB : FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo)
    (hK1 : AGPUnitK1) (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne)
    (hAb : CountableAbelianMF)
    (R : Type) [Ring R] [Countable R] (hR : IsPurelyInfiniteSimpleRing R) :
    mfHomKernel Rˣ = commutator Rˣ ∧
      ∃ (A : Type) (_ : CommGroup A) (_ : Countable A),
        Nonempty (Rˣ ⧸ mfHomKernel Rˣ ≃* A) ∧ IsOperatorMF A := by
  obtain ⟨A, hcomm, hcount, κ, hsurj, hker⟩ := hK1 R hR
  letI : CommGroup A := hcomm
  letI : Countable A := hcount
  have hMFA : IsOperatorMF A := hAb A
  -- `N ≤ ker κ`, because `κ` is a homomorphism to an MF group.
  have hle : mfHomKernel Rˣ ≤ κ.ker := by
    intro x hx
    exact (mem_mfHomKernel_iff x).mp hx A hMFA κ
  -- `ker κ ≤ N`, by the two Ara--Goodearl--Pardo steps and `eq:corner-units`.
  have hcorner : cornerUnitSubgroup R ≤ mfHomKernel Rˣ :=
    cornerUnitSubgroup_le_mfHomKernel hB R
  have hge : κ.ker ≤ mfHomKernel Rˣ := by
    intro u hu
    obtain ⟨v, e, hene, hidem, hvform, huv⟩ :=
      hMM R hR A κ hsurj hker u hu
    have huvN : u * v⁻¹ ∈ mfHomKernel Rˣ := hcorner huv
    have hkuv : κ (u * v⁻¹) = 1 := hle huvN
    have hkv : κ v = 1 := by
      have hku : κ u = 1 := hu
      rw [map_mul, hku, one_mul, map_inv, inv_eq_one] at hkuv
      exact hkuv
    have hvN : v ∈ mfHomKernel Rˣ :=
      hcorner (hS1 R hR A κ hsurj hker v e hene hidem hvform hkv)
    have hsplit : u = u * v⁻¹ * v := by group
    rw [hsplit]
    exact (mfHomKernel Rˣ).mul_mem huvN hvN
  have heq : mfHomKernel Rˣ = κ.ker := le_antisymm hle hge
  refine ⟨by rw [heq, hker], A, hcomm, hcount, ⟨?_⟩, hMFA⟩
  exact (QuotientGroup.quotientMulEquivOfEq heq).trans
    (QuotientGroup.quotientKerEquivOfSurjective κ hsurj)

/-! ### The printed theorem -/

/-- **`thm:mf-quotient-units`, as a closed proposition.**

The quotient is stated as "some countable abelian MF group" rather than as
`K_1(R)`; see the module docstring for exactly what that costs. -/
def PrintedMFQuotientUnits : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ n : ℕ, 1 ≤ n →
      mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ =
          commutator (Matrix (Fin n) (Fin n) R)ˣ ∧
        ∃ (A : Type) (_ : CommGroup A) (_ : Countable A),
          Nonempty ((Matrix (Fin n) (Fin n) R)ˣ ⧸
            mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ ≃* A) ∧ IsOperatorMF A

/-- **The printed theorem, from the quoted inputs.**  The rank reduction is the
printed one: `M_n(R)` is again countable purely infinite simple, and its unit
group is `GL_n(R)`, so the `n = 1` argument applies to it directly. -/
theorem printedMFQuotientUnits_of_inputs
    (hB : FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo)
    (hMat : AGPMatrixReduction) (hK1 : AGPUnitK1)
    (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne)
    (hAb : CountableAbelianMF) :
    PrintedMFQuotientUnits := by
  intro R _ _ hR n hn
  haveI : Countable (Matrix (Fin n) (Fin n) R) := by
    show Countable (Fin n → Fin n → R)
    infer_instance
  exact mfHomKernel_units_eq_commutator hB hK1 hMM hS1 hAb
    (Matrix (Fin n) (Fin n) R) (hMat R hR n hn)

/-- **The printed theorem from the Ara--Goodearl--Pardo inputs alone.**  The
countable-abelian clause is discharged, so the only remaining hypotheses are
Theorem `thm:full-defect-ring` in its rank-two form and the four propositions
quoted from Ara--Goodearl--Pardo. -/
theorem printedMFQuotientUnits_of_agp
    (hB : FullDefectRankTwo.PrintedFullComplementaryIdempotentsRankTwo)
    (hMat : AGPMatrixReduction) (hK1 : AGPUnitK1)
    (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne) :
    PrintedMFQuotientUnits :=
  printedMFQuotientUnits_of_inputs hB hMat hK1 hMM hS1 countableAbelianMF

end MFQuotientUnits
end GroupApproximation
