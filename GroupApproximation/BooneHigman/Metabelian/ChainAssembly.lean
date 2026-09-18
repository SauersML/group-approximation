import GroupApproximation.BooneHigman.Metabelian.ChainQuasiLinear
import Mathlib.GroupTheory.QuotientGroup.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# Chain skeleton, part 5: assembly

Research node `fp-metabelian-groups-satisfy-boone-higman`, route
`fp-metabelian-bh-via-quasi-linear-pbh`: a finitely generated metabelian group is a subdirect
product of finitely many linear groups, each over a single field
(`fg-metabelian-groups-embed-in-products-of-coprimary-quotients`, lane `bh-met-04`); so it is
quasi-linear, and the quasi-linear node gives `Products.MetabelianPiecesStatement`.  Together with
the envelope statement (lane `bh-met-07`) the existing reduction
`Products.finitelyPresentedMetabelianStatement_of_pieces` closes the root.

The FRONTIER tree and its Lean statements:

* root `fp-metabelian-groups-satisfy-boone-higman`: `FinitelyPresentedMetabelianStatement`;
* `fg-metabelian-groups-embed-in-products-of-coprimary-quotients`:
  `CoprimaryLinearQuotientsStatement` (here);
* `quasi-linear-groups-satisfy-permutational-boone-higman`: `QuasiLinearHostStatement`;
* `char-p-linear-groups-satisfy-permutational-boone-higman`: `CharPLinearHostStatement`, with
  leaves `CharPCoords.CharPPolynomialCoordinatesStatement` (on disk, lane `bh-met-03`),
  `CharPElementaryAbsorptionStatement`, `ElemFP.PolynomialFpElementaryFPStatement` (on disk,
  lane `bh-met-06`),
  `AffineExtensionFPStatement`, `CharPAffineSelfSimilarStatement`;
* `char-zero-linear-groups-satisfy-permutational-boone-higman`: `CharZeroLinearHostStatement`,
  with leaves `CharZeroPolynomialCoordinatesStatement`, `CharZeroElementaryAbsorptionStatement`,
  `CharZeroElementaryFPStatement`, `AffineExtensionFPStatement`,
  `CharZeroAffineSelfSimilarStatement`;
* `fp-self-similar-subgroups-satisfy-permutational-boone-higman` and
  `boone-higman-type-a-class-closed-under-finite-extensions`: replaced, since `B_A` is replaced by
  `Products.EmbedsInFPSelfSimilarGroup`, by the proved `Products.embedsInFPSelfSimilarGroup_of_rep`
  and `Products.embedsInFPSelfSimilarGroup_pi_fin`, plus `Products.FPSelfSimilarEnvelopeStatement`.

Endpoint: `finitelyPresentedMetabelianStatement_of_chain`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Chain

/-- **Research node `fg-metabelian-groups-embed-in-products-of-coprimary-quotients`** (lane
`bh-met-04`; restated here since no such interface was on disk): a finitely generated metabelian
group has finitely many normal subgroups with trivial intersection, each quotient embedding in a
general linear group over a field.  (True by Remeslennikov: `G` embeds in `GL_d(∏_{i<r} K_i)`; take
the kernels of the coordinate projections.) -/
def CoprimaryLinearQuotientsStatement : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → IsMetabelianGroup G →
    ∃ (r : ℕ) (N : Fin r → Subgroup G) (_ : ∀ i, (N i).Normal), (⨅ i, N i) = ⊥ ∧
      ∀ i, ∃ (K : Type) (_ : Field K) (d : ℕ)
        (f : G ⧸ N i →* Matrix.GeneralLinearGroup (Fin d) K), Function.Injective f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.CoprimaryLinearQuotientsStatement

/-- A group with finitely many normal subgroups of trivial intersection, each quotient linear over a
field, is quasi-linear. -/
theorem isQuasiLinear_of_quotients {G : Type} [Group G] {r : ℕ} (N : Fin r → Subgroup G)
    [∀ i, (N i).Normal] (hN : (⨅ i, N i) = ⊥) (K : Fin r → Type) [∀ i, Field (K i)]
    (d : Fin r → ℕ) (f : ∀ i, G ⧸ N i →* Matrix.GeneralLinearGroup (Fin (d i)) (K i))
    (hf : ∀ i, Function.Injective (f i)) : IsQuasiLinear G := by
  refine ⟨r, K, inferInstance, d, MonoidHom.pi fun i => (f i).comp (QuotientGroup.mk' (N i)), ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : x ∈ ⨅ i, N i := by
    rw [Subgroup.mem_iInf]
    intro i
    have hi : f i (x : G ⧸ N i) = 1 := congrFun hx i
    exact (QuotientGroup.eq_one_iff (N := N i) x).1
      ((injective_iff_map_eq_one (f i)).1 (hf i) _ hi)
  rw [hN] at hmem
  exact Subgroup.mem_bot.1 hmem

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Chain.isQuasiLinear_of_quotients

/-- Finitely generated metabelian groups are quasi-linear, from the coprimary node. -/
theorem isQuasiLinear_of_coprimaryLinearQuotients (hcop : CoprimaryLinearQuotientsStatement)
    {G : Type} [Group G] (hG : Group.FG G) (hmet : IsMetabelianGroup G) : IsQuasiLinear G := by
  obtain ⟨r, N, _, hN, hlin⟩ := hcop G hG hmet
  choose K _ d f hf using hlin
  exact isQuasiLinear_of_quotients N hN K d f hf

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.isQuasiLinear_of_coprimaryLinearQuotients

/-- **Composition for `fp-metabelian-bh-via-quasi-linear-pbh`**: the pieces statement, with a
single piece `G` itself. -/
theorem metabelianPiecesStatement_of_quasiLinear (hcop : CoprimaryLinearQuotientsStatement)
    (hql : QuasiLinearHostStatement) : Products.MetabelianPiecesStatement := by
  intro G _ hG hmet
  exact ⟨1, fun _ => G, fun _ => inferInstance,
    fun _ => hql G hG (isQuasiLinear_of_coprimaryLinearQuotients hcop hG hmet),
    MonoidHom.pi fun _ => MonoidHom.id G, fun x y h => congrFun h 0⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.metabelianPiecesStatement_of_quasiLinear

/-- **The root from the leaves of the FRONTIER tree** (quasi-linear route). -/
theorem finitelyPresentedMetabelianStatement_of_chain
    (hcop : CoprimaryLinearQuotientsStatement)
    (hcoordP : CharPCoords.CharPPolynomialCoordinatesStatement)
    (habsP : CharPElementaryAbsorptionStatement) (hfpP : ElemFP.PolynomialFpElementaryFPStatement)
    (hssP : CharPAffineSelfSimilarStatement)
    (hcoord0 : CharZeroPolynomialCoordinatesStatement)
    (habs0 : CharZeroElementaryAbsorptionStatement) (hfp0 : CharZeroElementaryFPStatement)
    (hss0 : CharZeroAffineSelfSimilarStatement) (haff : AffineExtensionFPStatement)
    (henv : Products.FPSelfSimilarEnvelopeStatement) :
    FinitelyPresentedMetabelianStatement :=
  Products.finitelyPresentedMetabelianStatement_of_pieces
    (metabelianPiecesStatement_of_quasiLinear hcop
      (quasiLinearHostStatement_of_chain hcoordP habsP hfpP hssP hcoord0 habs0 hfp0 hss0 haff))
    henv

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Chain.finitelyPresentedMetabelianStatement_of_chain

end Chain
end Metabelian
end BooneHigman
end GroupApproximation
