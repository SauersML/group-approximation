import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Meta.AxiomGuard

/-!
# One finite quotient for a finite residual packet

Residual finiteness separates one nonidentity element in a finite quotient.
For a finite packet, taking the intersection of the finitely many separating
normal subgroups gives one quotient which separates every element at once.

This file packages that elementary construction in the form used by finite
compression arguments.  The quotient is bundled as a `FiniteModel`, and the
quotient map is recorded together with the simultaneous separation property.

The empty packet is allowed.  Its intersection is the whole group, so the
resulting quotient is trivial; all separation and trace conclusions are then
vacuous.
-/

namespace GroupApproximation
namespace ResidualFinitePacket

noncomputable section

variable {H : Type} [Group H]

/-- A single normal finite-index subgroup avoiding every element of a finite
packet. -/
structure Packet (H : Type) [Group H] (D : Finset H) where
  /-- The common finite-index kernel. -/
  subgroup : Subgroup H
  /-- The common kernel is normal, so its coset type is a quotient group. -/
  normal' : subgroup.Normal
  /-- The common kernel has finite index. -/
  finiteIndex' : subgroup.FiniteIndex
  /-- Every requested element survives in the quotient. -/
  avoids : ∀ d ∈ D, d ∉ subgroup

namespace Packet

variable {D : Finset H} (P : Packet H D)

instance subgroupNormal : P.subgroup.Normal := P.normal'

instance subgroupFiniteIndex : P.subgroup.FiniteIndex := P.finiteIndex'

instance quotientFinite : Finite (H ⧸ P.subgroup) :=
  P.subgroup.finite_quotient_of_finiteIndex

noncomputable instance quotientFintype : Fintype (H ⧸ P.subgroup) :=
  Fintype.ofFinite _

noncomputable instance quotientDecidableEq : DecidableEq (H ⧸ P.subgroup) :=
  Classical.decEq _

/-- The common finite quotient, bundled as a matrix-model index type. -/
@[reducible] noncomputable def quotientModel : FiniteModel :=
  ⟨H ⧸ P.subgroup, P.quotientFintype, P.quotientDecidableEq⟩

noncomputable instance quotientNonempty : Nonempty P.quotientModel :=
  ⟨(1 : H ⧸ P.subgroup)⟩

/-- The quotient map associated to the common kernel. -/
def quotientMap : H →* (H ⧸ P.subgroup) :=
  QuotientGroup.mk' P.subgroup

@[simp] theorem quotientMap_apply (h : H) :
    P.quotientMap h = QuotientGroup.mk' P.subgroup h :=
  rfl

/-- Every element of the packet has nonidentity image in the common finite
quotient. -/
theorem quotientMap_ne_one_of_mem {d : H} (hd : d ∈ D) :
    P.quotientMap d ≠ 1 := by
  intro hq
  apply P.avoids d hd
  exact (QuotientGroup.eq_one_iff d).mp hq

end Packet

/-- A residually finite group admits one normal finite-index subgroup avoiding
all elements of any prescribed finite nonidentity packet. -/
theorem exists_packet [Group.ResiduallyFinite H] (D : Finset H)
    (hD : ∀ d ∈ D, d ≠ 1) : Nonempty (Packet H D) := by
  classical
  have hchoice : ∀ d : {x // x ∈ D}, ∃ N : Subgroup H,
      N.Normal ∧ N.FiniteIndex ∧ d.1 ∉ N := by
    intro d
    obtain ⟨N, hdN⟩ :=
      Group.exists_finiteIndexNormalSubgroup_notMem d.1 (hD d.1 d.2)
    exact ⟨N.toSubgroup, N.isNormal', N.isFiniteIndex', hdN⟩
  choose Nd hNdNormal hNdFiniteIndex hNdAvoids using hchoice
  let N : Subgroup H := ⨅ d : {x // x ∈ D}, Nd d
  have hNNormal : N.Normal := by
    constructor
    intro g hg x
    rw [show N = ⨅ d : {x // x ∈ D}, Nd d from rfl,
      Subgroup.mem_iInf] at hg ⊢
    intro d
    exact (hNdNormal d).conj_mem g (hg d) x
  haveI : ∀ d : {x // x ∈ D}, (Nd d).FiniteIndex := hNdFiniteIndex
  have hNFiniteIndex : N.FiniteIndex := by
    exact Subgroup.finiteIndex_iInf hNdFiniteIndex
  refine ⟨⟨N, hNNormal, hNFiniteIndex, ?_⟩⟩
  intro d hd hdN
  have hdNd : d ∈ Nd ⟨d, hd⟩ := by
    exact Subgroup.mem_iInf.mp
      (show d ∈ ⨅ z : {x // x ∈ D}, Nd z from hdN) ⟨d, hd⟩
  exact hNdAvoids ⟨d, hd⟩ hdNd

end

end ResidualFinitePacket
end GroupApproximation

open GroupApproximation.ResidualFinitePacket

#audit_axioms Packet.quotientMap_ne_one_of_mem
#audit_axioms exists_packet
