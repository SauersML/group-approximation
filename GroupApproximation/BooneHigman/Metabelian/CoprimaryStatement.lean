import Mathlib.Algebra.CharP.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import GroupApproximation.BooneHigman.Products.Hosts
import GroupApproximation.BooneHigman.Metabelian.CoprimarySplitting
import GroupApproximation.Meta.AxiomGuard

/-!
# Coprimary splitting of f.g. metabelian groups (lane bh-met-04)

Target node `fg-metabelian-groups-embed-in-products-of-coprimary-quotients`: a finitely generated
metabelian group `G` embeds in a finite product of quotients `G ⧸ N_i`, each isomorphic to a
finitely generated subgroup of `GL_d(K)` over a field `K` of a single characteristic
(`CoprimarySplittingStatement`).

The group-theoretic part, route (a) of `fg-metabelian-coprimary-quotients-proof` (Hall, the
Lasker--Noether decomposition, characteristic of the pieces, trivial intersection), is proved in
full in `CoprimarySplitting` (`exists_pureCharacteristic_split`).

**Remaining gap.** `PureCharacteristicLinearityStatement`: a finitely generated metabelian group
`Γ` of pure characteristic `c`, meaning `Γ'` torsion-free (`c = 0`) or of exponent a power of the
prime `c`, has a faithful finite-dimensional representation over a field of characteristic `c`.

* *True.* For `c = 0` this is Remeslennikov, *Representations of finitely generated metabelian
  groups by matrices*, Alg. i Logika 8 (1969), as quoted in the first sentence of §1 of Wehrfritz,
  Canad. J. Math. 27 (1975), 1355--1360.  For `c = p` prime, `Γ'` is a `p`-group and Theorem 1.1
  of Wehrfritz (1975), with `G = G_0 = Γ`, gives a faithful representation of finite degree over
  a field of characteristic `p`.
* *Strictly smaller in proof content.* It is the citation step (b) of the route alone.  It asserts
  nothing about arbitrary f.g. metabelian groups, and none of Hall's finiteness, the primary
  decomposition, the pieces or the embedding into the product is part of it; all of these are
  proved here and in `CoprimarySplitting`.

Endpoints:
* `coprimarySplittingStatement_of_linearity`;
* `metabelianPiecesStatement_of_coprimarySplitting`, which feeds
  `Products.MetabelianPiecesStatement` from `Products.LinearHostStatement`;
* `metabelianPiecesStatement_of_linearity`, both combined.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- **Linearity of pure-characteristic pieces** (Remeslennikov 1969; Wehrfritz 1975, Thm 1.1). -/
def PureCharacteristicLinearityStatement : Prop :=
  ∀ (Γ : Type) [Group Γ], Group.FG Γ → IsMetabelianGroup Γ → ∀ c : ℕ,
    IsPureCharacteristic Γ c → ∃ (K : Type) (_ : Field K) (d : ℕ)
      (f : Γ →* Matrix.GeneralLinearGroup (Fin d) K), ringChar K = c ∧ Function.Injective f

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.PureCharacteristicLinearityStatement

/-- **Coprimary splitting.** A f.g. metabelian group embeds in a finite product of quotients, each
isomorphic to a f.g. subgroup of `GL_d(K)` over a field `K` of the characteristic of the piece. -/
def CoprimarySplittingStatement : Prop :=
  ∀ (G : Type) [Group G], Group.FG G → IsMetabelianGroup G →
    ∃ (n : ℕ) (N : Fin n → Subgroup G) (_ : ∀ i, (N i).Normal),
      (∃ f : G →* ∀ i, G ⧸ N i, Function.Injective f) ∧
        ∀ i, N i ≤ commutator G ∧ ∃ (c : ℕ) (K : Type) (_ : Field K) (d : ℕ)
          (H : Subgroup (Matrix.GeneralLinearGroup (Fin d) K)),
          IsPureCharacteristic (G ⧸ N i) c ∧ ringChar K = c ∧ H.FG ∧ Nonempty (G ⧸ N i ≃* H)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.CoprimarySplittingStatement

/-- The coprimary splitting from the linearity of the pure-characteristic pieces. -/
theorem coprimarySplittingStatement_of_linearity (h : PureCharacteristicLinearityStatement) :
    CoprimarySplittingStatement := by
  intro G _ hfg hG
  haveI := hfg
  obtain ⟨n, N, hN, hone, hpieces⟩ := exists_pureCharacteristic_split G hG
  refine ⟨n, N, hN, ⟨MonoidHom.pi fun i => QuotientGroup.mk' (N i), ?_⟩, fun i => ?_⟩
  · refine (injective_iff_map_eq_one _).mpr fun g hg => hone g fun i => ?_
    have h1 : (g : G ⧸ N i) = 1 := congrFun hg i
    exact (QuotientGroup.eq_one_iff g).mp h1
  · obtain ⟨hle, c, hc⟩ := hpieces i
    haveI hQ : Group.FG (G ⧸ N i) := Group.fg_of_surjective (QuotientGroup.mk'_surjective (N i))
    obtain ⟨K, _, d, f, hK, hf⟩ := h (G ⧸ N i) hQ (isMetabelianGroup_quotient hG (N i)) c hc
    refine ⟨hle, c, K, inferInstance, d, f.range, hc, hK, ?_, ⟨MonoidHom.ofInjective hf⟩⟩
    exact (Group.fg_iff_subgroup_fg f.range).mp (Group.fg_range f)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.coprimarySplittingStatement_of_linearity

/-- The metabelian reduction of the product step from the coprimary splitting and the linear
hosts. -/
theorem metabelianPiecesStatement_of_coprimarySplitting (hsplit : CoprimarySplittingStatement)
    (hlin : Products.LinearHostStatement) : Products.MetabelianPiecesStatement := by
  intro G _ hfg hG
  obtain ⟨n, N, hN, hf, hpieces⟩ := hsplit G hfg hG
  refine ⟨n, fun i => G ⧸ N i, fun i => QuotientGroup.Quotient.group (N i), fun i => ?_, hf⟩
  obtain ⟨-, c, K, _, d, H, -, -, hH, ⟨e⟩⟩ := hpieces i
  exact (hlin K d H hH).of_mulEquiv e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.metabelianPiecesStatement_of_coprimarySplitting

/-- The metabelian reduction from the linearity of pure-characteristic pieces and the linear
hosts. -/
theorem metabelianPiecesStatement_of_linearity (h : PureCharacteristicLinearityStatement)
    (hlin : Products.LinearHostStatement) : Products.MetabelianPiecesStatement :=
  metabelianPiecesStatement_of_coprimarySplitting (coprimarySplittingStatement_of_linearity h) hlin

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.metabelianPiecesStatement_of_linearity

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
