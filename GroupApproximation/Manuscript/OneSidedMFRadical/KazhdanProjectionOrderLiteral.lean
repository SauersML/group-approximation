import GroupApproximation.Analysis.MaximalCStarKazhdanProjection
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanProjectionOrder

/-!
# `lem:kazhdan-projection-order` with the printed `≤`

`non_mf_groups_exist.tex`, Lemma `lem:kazhdan-projection-order`:

> Let `L` have property (T), let `B` be a unital `C*`-algebra, and let
> `π : L → U(B)` be a homomorphism.  Denote by `P ∈ B` the image of the Kazhdan
> projection under the extension `C*_max(L) → B`.  If `U ∈ U(B)` satisfies
> `U π(L) U* ⊆ π(L)`, then `U* P U ≤ P`.

The conclusion of that sentence is an inequality, and this module states it as
one, for a unital `C*`-algebra `B` carrying no order hypothesis at all.

## What was in the way, and how it is removed

The order half of Mathlib's projection API —
`IsStarProjection.le_iff_mul_eq_left` / `le_iff_mul_eq_right` — is stated for
`[PartialOrder A] [StarOrderedRing A]`, and a general `CStarAlgebra` does not
carry those globally: installing them as instances would collide with
`ComplexOrder` on `ℂ`.  The two existing statements of this lemma therefore each
paid for that in a different currency.

* `Manuscript/OneSidedMFRadical/KazhdanProjectionOrder.lean`
  (`OneSidedKazhdanProjectionOrder`) keeps `B` order-free and writes the
  conclusion as the two absorption identities `(U⁎ P U) P = U⁎ P U` and
  `P (U⁎ P U) = U⁎ P U`.
* `Analysis/MaximalCStarKazhdanProjection.lean`
  (`MaximalCStarKazhdanProjectionOrder`) writes the literal `≤`, but takes
  `[PartialOrder B] [StarOrderedRing B]` from the caller — hypotheses the
  printed lemma does not have.

Neither of those is the printed sentence on the nose.  The way out is that a
`C*`-algebra has a canonical order, and it is *the* order the manuscript means:
`CStarAlgebra.spectralOrder`, `x ≤ y` iff `y - x` is self-adjoint with
nonnegative spectrum, the Loewner order.  It is a `@[reducible] def` rather than
an instance precisely so that it can be installed where it is wanted, and the
place it is wanted here is *inside the proposition*.  Both endpoints below bind
`B` with `[CStarAlgebra B]` alone and then open the inequality with

```
letI : PartialOrder B := CStarAlgebra.spectralOrder B
```

so the `≤` that appears is the spectral order of that very algebra, chosen by
the statement rather than demanded from a caller.  `StarOrderedRing` never
appears in either statement: it is needed only to run
`IsStarProjection.le_iff_mul_eq_left`, and
`CStarAlgebra.spectralOrderedRing B` supplies it inside the proofs.

## The two `P`s

Both readings of "the Kazhdan projection" are covered, because the two existing
modules construct it in the two different places and the printed proof uses
both sides of that passage.

* `LiteralMaximalCStarKazhdanProjectionOrder` is the printed `P`: a single
  element `p` of `C*_max(L)`, pinned down by seven clauses (self-adjoint,
  idempotent, **nonzero**, `ran p ⊆ Fix`, `Fix ⊆ ran p`, uniqueness — the
  printed definite article — and `f p = 1` for every `⋆`-homomorphism
  trivialising `L`), whose image under any extension `C*_max(L) → B` satisfies
  `U⁎ (f p) U ≤ f p`.  The vacuity discussion of
  `MaximalCStarKazhdanProjectionOrder` applies verbatim: `p = 0` would make
  every displayed inequality read `0 ≤ 0`, and clauses 3, 6 and 7 exclude it
  three times over.
* `LiteralOneSidedKazhdanProjectionOrder` is the same inequality for the
  Kazhdan projection built directly inside `B` as the spectral projection of the
  orbit average at the isolated point `1`, which is the form the transport
  argument consumes.

Neither statement is new mathematics: the absorption identities were already
proved order-free in the two modules imported here.  What is new is that the
displayed relation of the manuscript is now a relation in Lean.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open MaximalCStarKazhdanProjection
open UltraproductKazhdanProjection

universe u v w

/-! ## Unitary conjugation preserves star projections

Pure star-ring algebra: no order, no norm, no `C*`-identity. -/

/-- If `P` is a self-adjoint idempotent and `V` is a coisometry, then
`V⁎ P V` is again a self-adjoint idempotent. -/
theorem isStarProjection_star_conj {A : Type*} [Ring A] [StarRing A]
    {P V : A} (hP : IsStarProjection P) (hV : V * star V = 1) :
    IsStarProjection (star V * P * V) := by
  constructor
  · show (star V * P * V) * (star V * P * V) = star V * P * V
    have hrw : (star V * P * V) * (star V * P * V)
        = star V * (P * (V * star V) * P) * V := by noncomm_ring
    rw [hrw, hV, mul_one, hP.isIdempotentElem.eq]
  · show star (star V * P * V) = star V * P * V
    rw [star_mul, star_mul, star_star, hP.isSelfAdjoint.star_eq, mul_assoc]

/-! ## The inequality for a Kazhdan compression datum

`KazhdanCompressionRep.kt_09_proj_mul_conjugate` is `P (V P V⁎) = P`;
conjugating it by `V⁎ · V` turns it into `(V⁎ P V) P = V⁎ P V`, which is
`V⁎ P V ≤ P` by `IsStarProjection.le_iff_mul_eq_left`. -/

/-- The printed one-sided inequality for the spectral Kazhdan projection of a
compression datum, in the spectral order of the target algebra. -/
theorem kazhdanCompressionRep_star_conj_le
    {Gamma : Type u} {H : Type w} {B : Type v}
    [Group Gamma] [Group H] [CStarAlgebra B]
    (D : KazhdanCompressionRep Gamma H B) :
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    star D.shift * D.proj * D.shift ≤ D.proj := by
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  have hP : IsStarProjection D.proj :=
    ⟨KazhdanCompressionRep.kt_08_proj_mul_proj D,
      KazhdanCompressionRep.kt_08_isSelfAdjoint_proj D⟩
  have hQ : IsStarProjection (star D.shift * D.proj * D.shift) :=
    isStarProjection_star_conj hP (KazhdanCompressionRep.shift_mul_star D)
  have habs : (star D.shift * D.proj * D.shift) * D.proj
      = star D.shift * D.proj * D.shift := by
    have hleft := congrArg (fun x : B ↦ star D.shift * x * D.shift)
      (KazhdanCompressionRep.kt_09_proj_mul_conjugate D)
    simpa only [mul_assoc, KazhdanCompressionRep.shift_star_mul, one_mul,
      mul_one] using hleft
  exact (hQ.le_iff_mul_eq_left hP).mpr habs

/-! ## Endpoint 1: `P` the image of the Kazhdan projection of `C*_max(L)` -/

/-- **Lemma `lem:kazhdan-projection-order`, printed literally, with `P` the
image of the Kazhdan projection under `C*_max(L) → B`.**

> Let `L` have property (T), let `B` be a unital `C*`-algebra, and let
> `π : L → U(B)` be a homomorphism.  Denote by `P ∈ B` the image of the Kazhdan
> projection under the extension `C*_max(L) → B`.  If `U ∈ U(B)` satisfies
> `U π(L) U* ⊆ π(L)`, then `U* P U ≤ P`.

This is `MaximalCStarKazhdanProjectionOrder` with its two caller-supplied order
instances deleted: `B` is bound with `[CStarAlgebra B]` and nothing else, and
the order in which the final inequality is read is the algebra's own spectral
order, installed by the statement itself.  Every other clause is unchanged, so
the definite description of `P` — and with it the argument that the inequality
cannot be satisfied vacuously by `P = 0` — is the same one. -/
def LiteralMaximalCStarKazhdanProjectionOrder : Prop :=
  ∀ (L : Type u) [Group L], HasKazhdanPropertyT.{u, u} L →
    ∃ p : MaximalGroupCStar L,
      IsSelfAdjoint p ∧ p * p = p ∧ p ≠ 0 ∧
        (∀ l : L, maximalGroupCStarGenerator L l * p = p) ∧
        (∀ x : MaximalGroupCStar L,
          (∀ l : L, maximalGroupCStarGenerator L l * x = x) → p * x = x) ∧
        (∀ q : MaximalGroupCStar L, IsSelfAdjoint q →
          (∀ l : L, maximalGroupCStarGenerator L l * q = q) →
          (∀ x : MaximalGroupCStar L,
            (∀ l : L, maximalGroupCStarGenerator L l * x = x) → q * x = x) →
          q = p) ∧
        (∀ (B : Type v) [CStarAlgebra B] (f : MaximalGroupCStar L →⋆ₐ[ℂ] B),
          (∀ l : L, f (maximalGroupCStarGenerator L l) = 1) → f p = 1) ∧
        ∀ (B : Type v) [CStarAlgebra B] (pi : L →* unitary B),
          (∃! f : MaximalGroupCStar L →⋆ₐ[ℂ] B,
            ∀ l : L, f (maximalGroupCStarGenerator L l) = (pi l : B)) ∧
          ∀ U : unitary B,
            (∀ l : L, ∃ l' : L, U * pi l * U⁻¹ = pi l') →
            ∀ f : MaximalGroupCStar L →⋆ₐ[ℂ] B,
              (∀ l : L, f (maximalGroupCStarGenerator L l) = (pi l : B)) →
              letI : PartialOrder B := CStarAlgebra.spectralOrder B
              star ((U : unitary B) : B) * f p * ((U : unitary B) : B) ≤ f p

/-- Closed proof of `lem:kazhdan-projection-order` in the printed `≤` form,
with `P` the image of the Kazhdan projection of `C*_max(L)` and with no order
hypothesis on `B`. -/
theorem manuscriptLiteralMaximalCStarKazhdanProjectionOrder :
    LiteralMaximalCStarKazhdanProjectionOrder.{u, v} := by
  intro L _ hT
  obtain ⟨K⟩ := exists_kazhdanData L hT
  refine ⟨K.projection, K.isSelfAdjoint_projection,
    K.projection_mul_projection, ?_⟩
  refine ⟨projection_ne_zero K, ?_⟩
  refine ⟨K.generator_mul_projection, ?_⟩
  refine ⟨?_, ?_⟩
  · intro x hx
    exact K.projection_mul_eq_of_generator_mul_eq hx
  refine ⟨?_, ?_⟩
  · intro q hqsa hqfix hqabs
    exact K.eq_projection_of_absorbs hqsa hqfix hqabs
  refine ⟨?_, ?_⟩
  · intro B _ f hf
    exact image_projection_eq_one K f hf
  · intro B _ pi
    refine ⟨maximalGroupCStar_existsUnique_lift_allUniverses L pi, ?_⟩
    intro U hcomp f hf
    letI : PartialOrder B := CStarAlgebra.spectralOrder B
    letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
    exact star_conj_image_le K pi f hf ((U : unitary B) : B) U.property.1
      U.property.2 (compresses_coe pi U hcomp)

/-! ## Endpoint 2: `P` the spectral Kazhdan projection built inside `B` -/

/-- **Lemma `lem:kazhdan-projection-order`, printed literally, with `P` the
Kazhdan projection constructed inside the target algebra.**

Same sentence, same order, same absence of order hypotheses; only the
construction of `P` differs.  Here `P` is the spectral projection of the orbit
average at the isolated spectral point `1`, which is
`OneSidedKazhdanProjectionOrder`'s `P`, and the conclusion of that proposition
— two absorption identities — is replaced by the displayed inequality it was
standing in for. -/
def LiteralOneSidedKazhdanProjectionOrder : Prop :=
  ∀ (Gamma : Type) (B : Type) [Group Gamma] [CStarAlgebra B]
    (_hT : HasKazhdanPropertyT.{0, 0} Gamma)
    (rho : Gamma →* unitary B) (U : unitary B)
    (hcompresses : ∀ gamma : Gamma, ∃ delta : Gamma,
      U * rho gamma * U⁻¹ = rho delta),
    ∃ (S : Finset Gamma) (kappa : ℝ)
      (hkazhdan : IsKazhdanPair.{0, 0} Gamma S kappa)
      (hone : 1 ∈ S) (hsymm : ∀ gamma ∈ S, gamma⁻¹ ∈ S)
      (hgenerates : Subgroup.closure (S : Set Gamma) = ⊤),
      letI : PartialOrder B := CStarAlgebra.spectralOrder B
      star ((U : unitary B) : B)
            * (targetUnitaryCompressionData rho U S kappa hkazhdan hone hsymm
                hgenerates hcompresses).proj
            * ((U : unitary B) : B)
          ≤ (targetUnitaryCompressionData rho U S kappa hkazhdan hone hsymm
              hgenerates hcompresses).proj

/-- Closed proof of `lem:kazhdan-projection-order` in the printed `≤` form,
with `P` built inside the target algebra and with no order hypothesis on `B`. -/
theorem manuscriptLiteralOneSidedKazhdanProjectionOrder :
    LiteralOneSidedKazhdanProjectionOrder := by
  intro Gamma B _ _ hT rho U hcompresses
  obtain ⟨S, kappa, hone, hsymm, hgenerates, -, -, hkazhdan₀⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  have hkazhdan : IsKazhdanPair.{0, 0} Gamma S kappa := hkazhdan₀
  exact ⟨S, kappa, hkazhdan, hone, hsymm, hgenerates,
    kazhdanCompressionRep_star_conj_le
      (targetUnitaryCompressionData rho U S kappa hkazhdan hone hsymm
        hgenerates hcompresses)⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
