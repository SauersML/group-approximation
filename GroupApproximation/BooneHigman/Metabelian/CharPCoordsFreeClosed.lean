import GroupApproximation.BooneHigman.Metabelian.CharPCoordsAssembly
import GroupApproximation.BooneHigman.Metabelian.CharPCoordsFree
import GroupApproximation.Meta.AxiomGuard

/-!
# Polynomial coordinates in characteristic `p`: closed endpoint (lane bh-met-10)

Research node `char-p-linear-groups-embed-in-polynomial-f-p-groups`: "every finitely generated
subgroup of `GL_n(K)`, `K` a field of characteristic `p > 0`, embeds in
`GL_M(F_p[x_1, ..., x_k])` for some `M, k`".

**Endpoint.** `charPPolynomialCoordinates : CharPPolynomialCoordinatesStatement`, obtained by
feeding `finiteDomainAwayEmbedding` (generic freeness, `CharPCoordsFree.lean`) into lane
bh-met-03's reduction `charPCoordinates_of_finiteDomainAway` (`CharPCoordsAssembly.lean`).
No hypothesis Statement remains.
-/

namespace GroupApproximation.BooneHigman.Metabelian.CharPCoords

/-- **Polynomial coordinates in characteristic `p`, unconditional.**  Every finitely generated
subgroup of `GL_n(K)`, `ringChar K = p > 0`, embeds in `GL_M(F_p[x_0, ..., x_{k-1}])`. -/
theorem charPPolynomialCoordinates : CharPPolynomialCoordinatesStatement :=
  charPCoordinates_of_finiteDomainAway finiteDomainAwayEmbedding

#audit_axioms GroupApproximation.BooneHigman.Metabelian.CharPCoords.charPPolynomialCoordinates

end GroupApproximation.BooneHigman.Metabelian.CharPCoords
