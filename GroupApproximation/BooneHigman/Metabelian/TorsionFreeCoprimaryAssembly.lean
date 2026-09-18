import GroupApproximation.BooneHigman.GroupRing.Noetherian
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryStatement
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryField
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeCoprimaryBlock
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion-free linearity from the coprimary case (lane bh-met-42)

`torsionFreeModuleLinearity_of_coprimary`: `CoprimaryTorsionFreeLinearityStatement` implies
`TorsionFreeModuleLinearityStatement`.

Proof.  `ℤ[Q]` is Noetherian, so the finitely generated torsion-free module `W` has a coprimary
decomposition `0 = S_1 ∩ ... ∩ S_n` (`Primary.exists_coprimary_decomposition`).  Keep the indices
`j` whose quotient `W ⧸ S_j` is torsion-free; by `eq_zero_of_mem_torsionFree_pieces` those pieces
alone already meet in `0`.  Each such `W ⧸ S_j` is coprimary and torsion-free, so the hypothesis
gives an equivariant injection `W ⧸ S_j ↪ K_j^{d_j}` over a field of characteristic zero.  Embed
all `K_j` into one field `L` of characteristic zero (`exists_common_field_finset`) and assemble
the block-diagonal representation (`exists_linearization_of_field_pieces`).
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- **Reduction to the coprimary case.** -/
theorem torsionFreeModuleLinearity_of_coprimary (h : CoprimaryTorsionFreeLinearityStatement) :
    TorsionFreeModuleLinearityStatement := by
  intro Q _ hfg W _ _ _ _
  haveI : Group.FG Q := hfg
  haveI := GroupRing.isNoetherianRing_intGroupRing Q
  obtain ⟨n, S, P, e, hS, -, hP⟩ :=
    Primary.exists_coprimary_decomposition (MonoidAlgebra ℤ Q) W
  choose K _ d ρ ι hchar hinj hequiv using
    fun j : {i : Fin n // IsAddTorsionFree (W ⧸ S i)} =>
      h Q hfg (W ⧸ S j.1) inferInstance j.2 (P j.1) (e j.1) (hP j.1)
  haveI : ∀ j, CharZero (K j) := fun j =>
    (CharP.ringChar_zero_iff_CharZero (R := K j)).mp (hchar j)
  haveI : Fintype {i : Fin n // IsAddTorsionFree (W ⧸ S i)} := Fintype.ofFinite _
  haveI : DecidableEq {i : Fin n // IsAddTorsionFree (W ⧸ S i)} := Classical.decEq _
  obtain ⟨L, _, _, hL⟩ := exists_common_field_finset K Finset.univ
  have f : ∀ j, K j →+* L := fun j => Classical.choice (hL j (Finset.mem_univ j))
  obtain ⟨d', ρ', ι', hinj', hequiv'⟩ :=
    exists_linearization_of_field_pieces (fun q (w : W) => MonoidAlgebra.of ℤ Q q • w) K f d ρ
      (fun j => (ι j).comp (S j.1).mkQ.toAddMonoidHom)
      (fun w hw => eq_zero_of_mem_torsionFree_pieces S hS hP w fun i hi => by
        have h0 : ι ⟨i, hi⟩ (Submodule.Quotient.mk w) = ι ⟨i, hi⟩ 0 :=
          (hw ⟨i, hi⟩).trans (map_zero (ι ⟨i, hi⟩)).symm
        exact (Submodule.Quotient.mk_eq_zero (S i)).mp (hinj ⟨i, hi⟩ h0))
      (fun j q w => hequiv j q (Submodule.Quotient.mk w))
  exact ⟨L, inferInstance, d', ρ', ι', ringChar.eq_zero (R := L), hinj', hequiv'⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.torsionFreeModuleLinearity_of_coprimary

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
