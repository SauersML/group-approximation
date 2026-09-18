import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.Ext
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.Blocks
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.SL3Laurent
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2ThomT.RelTLaurent
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.A2Endpoint.ThomGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# Property (T) for Thom's group `G_0(F_p[t,t⁻¹])` (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–59 (table row A2); A. Thom, Groups Geom.
Dyn. 4 (2010), §2.1, Lemma 2.1.

The block map `G_0(L) → SL_3(L)`, `L = F_p[t,t⁻¹]`, is surjective (`thomBlockHom_surjective`), and
its target has property (T) (`hasKazhdanPropertyT_sl3Laurent`). Its kernel `N` has relative
property (T) (`hasRelativePropertyT_thomG0_ker`), by transfer from the pair
`(L³ ⋊ EL_3(L), L³)` (`isRelativeKazhdanPair_relT`). The extension lemma
(`hasKazhdanPropertyT_of_relative_of_surjective`) then gives property (T) for `G_0(L)`.
-/

namespace GroupApproximation.Full.A2ThomT

/-- **Thom's group `G_0(F_p[t,t⁻¹])` has Kazhdan's property (T)** (Thom, GGD 4 (2010), §2.1,
Lemma 2.1; tex l.57–59, table row A2). -/
theorem hasKazhdanPropertyT_thomG0 (p : ℕ) [Fact p.Prime] :
    HasKazhdanPropertyT.{0, 0} ↥(Full.A2Endpoint.thomG0 (LaurentPolynomial (ZMod p))) := by
  obtain ⟨Q, ε, hQ⟩ := isRelativeKazhdanPair_relT.{0} p
  exact hasKazhdanPropertyT_of_relative_of_surjective
    (thomBlockHom (LaurentPolynomial (ZMod p))) thomBlockHom_surjective
    (hasRelativePropertyT_thomG0_ker (relTAction p) (relTAction_apply p) ⟨Q, ε, hQ⟩)
    (hasKazhdanPropertyT_sl3Laurent p)

#audit_axioms hasKazhdanPropertyT_thomG0

end GroupApproximation.Full.A2ThomT
