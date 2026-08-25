import GroupApproximation.Sofic.UltraproductKazhdanProjection

/-!
# One-sided order for the Kazhdan projection

This is the manuscript-facing endpoint for
`non_mf_groups_exist.tex`, Lemma `lem:kazhdan-projection-order`.

The unitary in this lemma is an arbitrary unitary of the target algebra; it
need not lie in the image of a larger ambient-group representation.  We put
it into `KazhdanCompressionRep` by taking the ambient group to be `unitary B`
itself.  The resulting `proj` is the image of the Kazhdan projection,
constructed as the spectral projection at the isolated point `1`.  For
projections, the two absorption identities below are the algebraic
(order-instance-free) spelling of

`shift⁎ * proj * shift ≤ proj`.

`Analysis/KazhdanProjectionOneSidedOrder.lean` proves the printed fixed-space
argument and literal Loewner inequality after passing to a Hilbert-space
representation.  It deliberately leaves the abstract `C*`-algebra bridge as
a hypothesis.  This wrapper therefore reuses the complementary existing
abstract-algebra route `KazhdanCompressionRep.kt_09_*`: that is what identifies
the spectral Kazhdan projection and proves the absorption identities inside
the manuscript's arbitrary target algebra `B`.  The two modules are not
duplicate endpoints; they formalize the two sides of the faithful-
representation passage used in the printed proof.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open UltraproductKazhdanProjection

universe u v

/-- Package an arbitrary target-algebra unitary satisfying the manuscript's
one-sided inclusion as Kazhdan compression data.  Taking the ambient group to
be `unitary B` is what preserves the full generality of the printed lemma. -/
noncomputable def targetUnitaryCompressionData
    {Gamma : Type u} {B : Type v} [Group Gamma] [CStarAlgebra B]
    (rho : Gamma →* unitary B) (U : unitary B)
    (S : Finset Gamma) (kappa : ℝ)
    (hkazhdan : IsKazhdanPair.{u, v} Gamma S kappa)
    (hone : 1 ∈ S) (hsymm : ∀ gamma ∈ S, gamma⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set Gamma) = ⊤)
    (hcompresses : ∀ gamma : Gamma, ∃ delta : Gamma,
      U * rho gamma * U⁻¹ = rho delta) :
    KazhdanCompressionRep Gamma (unitary B) B where
  pi := MonoidHom.id (unitary B)
  iota := rho
  s := U
  Q := S
  kappa := kappa
  kazhdan := hkazhdan
  S := S
  QS := Finset.Subset.rfl
  one_mem := hone
  symm := hsymm
  generates := hgenerates
  compresses := hcompresses

/-- **Lemma `lem:kazhdan-projection-order`.**  If a unitary conjugates the
Kazhdan group into itself, then the inverse-conjugated Kazhdan projection is
dominated by the original projection.  Projection order is written as its two
absorption identities, avoiding a noncanonical order instance on an arbitrary
C-star algebra.  In the displayed order of the manuscript these are exactly

`(U⁎ P U) P = U⁎ P U` and `P (U⁎ P U) = U⁎ P U`,

i.e. `U⁎ P U ≤ P` from Lemma `lem:kazhdan-projection-order`. -/
def OneSidedKazhdanProjectionOrder : Prop :=
  ∀ (Gamma : Type) (B : Type) [Group Gamma] [CStarAlgebra B]
    (_hT : HasKazhdanPropertyT.{0, 0} Gamma)
    (rho : Gamma →* unitary B) (U : unitary B)
    (hcompresses : ∀ gamma : Gamma, ∃ delta : Gamma,
      U * rho gamma * U⁻¹ = rho delta),
    ∃ (S : Finset Gamma) (kappa : ℝ)
      (hkazhdan : IsKazhdanPair.{0, 0} Gamma S kappa)
      (hone : 1 ∈ S) (hsymm : ∀ gamma ∈ S, gamma⁻¹ ∈ S)
      (hgenerates : Subgroup.closure (S : Set Gamma) = ⊤),
      let D := targetUnitaryCompressionData rho U S kappa hkazhdan
        hone hsymm hgenerates hcompresses
      (star D.shift * D.proj * D.shift) * D.proj
            = star D.shift * D.proj * D.shift ∧
          D.proj * (star D.shift * D.proj * D.shift)
            = star D.shift * D.proj * D.shift

/-!
This module states the order in absorption form.  Mathlib exposes projection
order through `IsStarProjection.le_iff_mul_eq_left/right`, which require local
`[PartialOrder B] [StarOrderedRing B]` instances, and a general `CStarAlgebra B`
does not install them globally (doing so would conflict with the existing order
on `ℂ`).

**Superseded 2026-08-25.**  This note used to say there was "deliberately no
unconditional `≤` corollary", on the reasoning that stating one would force
those instances on the caller.  That reasoning was wrong: the instances do not
have to come from the caller.  `Manuscript/OneSidedMFRadical/KazhdanProjectionOrderLiteral.lean`
installs `CStarAlgebra.spectralOrder B` inside the proposition with `letI` and
`CStarAlgebra.spectralOrderedRing B` inside the proof, and states the literal
printed inequality `U⁎ P U ≤ P` over `[CStarAlgebra B]` and nothing else --
`manuscriptLiteralOneSidedKazhdanProjectionOrder` for the projection built
inside `B`, and `manuscriptLiteralMaximalCStarKazhdanProjectionOrder` for the
manuscript's own `P`, the image of the Kazhdan projection of `C*_max(L)`.

Both forms are kept.  They are not the same claim: the literal endpoints fix
one order, the Loewner order of that algebra, which is what `≤` means in the
printed lemma; `MaximalCStarKazhdanProjectionOrder` quantifies over whatever
compatible order a caller supplies.  Neither implies the other.
-/

/-- Closed proof of the manuscript's one-sided Kazhdan-projection order. -/
theorem manuscriptOneSidedKazhdanProjectionOrder :
    OneSidedKazhdanProjectionOrder := by
  intro Gamma B _ _ hT rho U hcompresses
  obtain ⟨S, kappa, hone, hsymm, hgenerates, -, -, hkazhdan₀⟩ :=
    KazhdanProjection.HasKazhdanPropertyT.exists_symmetric_generating_pair hT
  have hkazhdan : IsKazhdanPair.{0, 0} Gamma S kappa := hkazhdan₀
  refine ⟨S, kappa, hkazhdan, hone, hsymm, hgenerates, ?_⟩
  let D := targetUnitaryCompressionData rho U S kappa hkazhdan hone hsymm
    hgenerates hcompresses
  have hQP := KazhdanCompressionRep.kt_09_conjugate_mul_proj D
  have hPQ := KazhdanCompressionRep.kt_09_proj_mul_conjugate D
  have hleft := congrArg
    (fun x : B ↦ star D.shift * x * D.shift) hPQ
  have hright := congrArg
    (fun x : B ↦ star D.shift * x * D.shift) hQP
  constructor
  · simpa only [mul_assoc, KazhdanCompressionRep.shift_star_mul,
      one_mul, mul_one] using hleft
  · simpa only [← mul_assoc, KazhdanCompressionRep.shift_star_mul,
      one_mul, mul_one] using hright

end OneSidedMFRadical
end Manuscript
end GroupApproximation
