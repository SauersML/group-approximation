import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.TriangleCorner
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P01, empty two-gons: endpoint

`proof` closes `OsinLemma94ContactMapEmptyTwoGonInput` unconditionally, by feeding the triangle
corner theorem `switchCornerOne` into the bridge `proof_of_one`.

This module sits downstream of `TriangleCorner`, so it avoids the import cycle through
`P01EmptyTwoGon.Proof` (which `TouchTwoGon` imports).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon

universe u w v

/-- Empty two-gons in the contact map: the unconditional P01 endpoint. -/
theorem proof : OsinLemma94ContactMapEmptyTwoGonInput.{u, w, v} :=
  proof_of_one switchCornerOne

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon.proof

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01EmptyTwoGon
