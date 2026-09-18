import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCTreeNFSchreier
import GroupApproximation.Meta.AxiomGuard

/-!
# LOUD converse: the Schreier gap is Prop-equivalent to (1) (lane bh-met-77l)

Assuming (1) (`ker ≤ K` for all `d > 1`), `E : Q →* V_d` is injective.  The trivial witness
then works: `X = Q`, right multiplication, `x₀ = 1`, `c = id`.  Every Schreier element is
`x * g * (x * g)⁻¹ = 1 ∈ U`.  So `HigmanVCTreeNFSchreierStatement` is NOT strictly weaker than
(1) as a Prop.  Its value is proof-content only; see the docstring of
`EnvelopeHigmanVCTreeNFSchreier`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

theorem higmanVCTreeNF_mk_surjective (d : ℕ) : Function.Surjective (higmanVCCommon_mk d) :=
  QuotientGroup.mk'_surjective (Subgroup.normalClosure (higmanVC_rels d fun _ => True))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_mk_surjective

/-- Under (1) at `d`, the evaluation `E : Q →* V_d` is injective. -/
theorem higmanVCTreeNF_E_injective_of_ker_le {d : ℕ}
    (h : (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True))
    {q q' : higmanVCCommon_Q d} (e : higmanVCTreeNF_E d q = higmanVCTreeNF_E d q') :
    q = q' := by
  obtain ⟨r, rfl⟩ := higmanVCTreeNF_mk_surjective d q
  obtain ⟨r', rfl⟩ := higmanVCTreeNF_mk_surjective d q'
  rw [higmanVCTreeNF_E_mk, higmanVCTreeNF_E_mk] at e
  have hk : r * r'⁻¹ ∈ (higmanVC_evalAll d).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, e, mul_inv_cancel]
  have h1 := higmanVCCommon_mk_eq_one_iff.mpr (h hk)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_E_injective_of_ker_le

/-- **LOUD converse:** (1) gives the Schreier gap, via the trivial witness. -/
theorem higmanVCTreeNF_schreier_of_ker_le
    (h : ∀ d : ℕ, 1 < d →
      (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True)) :
    HigmanVCTreeNFSchreierStatement := by
  intro d hd N
  obtain ⟨n, hN, a, b, ha, hb, hab, hba, -⟩ := higmanVCTreeLevel_level_of_ker_le h d hd N
  refine ⟨n, hN, a, b, ha, hb, hab, hba, higmanVCCommon_Q d, fun x q => x * q, 1, id,
    fun x => mul_one x, fun x q q' => (mul_assoc x q q').symm, ?_, ?_, ?_⟩
  · intro x q q' e
    show x * q = x * q'
    rw [higmanVCTreeNF_E_injective_of_ker_le (h d hd) e]
  · exact (higmanVCTreeNF_U d).one_mem
  · intro g _ x
    show x * g * (x * g)⁻¹ ∈ higmanVCTreeNF_U d
    rw [mul_inv_cancel]
    exact (higmanVCTreeNF_U d).one_mem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_schreier_of_ker_le

/-- **LOUD equivalence** with (1). -/
theorem higmanVCTreeNF_schreier_iff_ker_le :
    HigmanVCTreeNFSchreierStatement ↔ ∀ d : ℕ, 1 < d →
      (higmanVC_evalAll d).ker ≤ Subgroup.normalClosure (higmanVC_rels d fun _ => True) :=
  ⟨higmanVCTreeNF_ker_le_of_schreier, higmanVCTreeNF_schreier_of_ker_le⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCTreeNF_schreier_iff_ker_le

end GroupApproximation.BooneHigman.Metabelian.Envelope
