import GroupApproximation.GGT.DGOProposition414AdditiveParameters

/-!
# Dahmani–Guirardel–Osin Lemma 4.21(a)

The completed additive quasi-geodesic surgery proves the uniform `(1,1)`
sum bound needed by the component-counting proof. Thus clause (a) now holds
under the original hypotheses without assuming general Proposition 4.14.
-/

namespace GroupApproximation.GGT.OsinComponents

universe u w

/-- **DGO Lemma 4.21(a).** Every `W` word above one depth threshold is
`(4,1)`-quasi-geodesic. The original proposition is proved as stated. -/
theorem dgoLemma421a : DGOLemma421a.{u, w} := by
  intro G _ Lambda D hhyp hbase
  obtain ⟨C, hC, hbound⟩ :=
    DGOProposition414.exists_uniformSumBound_one_of_hyperbolic D hhyp hbase 1
  exact ⟨50 * C, wWord_quasiGeodesic_of_uniformBound hC hbound⟩

end GroupApproximation.GGT.OsinComponents

#audit_closed_axioms GroupApproximation.GGT.OsinComponents.dgoLemma421a
