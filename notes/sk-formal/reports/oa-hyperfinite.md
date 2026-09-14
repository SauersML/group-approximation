# oa-hyperfinite: R, R^ω and embeddings behind tex l.168–173 of simple_kazhdan_sofic_group.tex (tip e80dcf20a)

Lane oa-hyperfinite, launched ~20:15 by main. Brief: `ct/ROSTER-sk.md`, "OA LANES 20:15". No literature input.

## CLAIM
CLAIM twisted group von Neumann algebra L_β(Γ) on ℓ²(Γ) (twisted regular operators, commutation, trace, separating vector) GroupApproximation/Analysis/TwistedGroupVonNeumann.lean
CLAIM the Pauli model R = L_β(ℕ →₀ (ZMod 2 × ZMod 2)): factor, infinite-dimensional, faithful trace, hyperfinite GroupApproximation/Analysis/PauliHyperfiniteFactor.lean
CLAIM unital trace-preserving M_{2^j} ↪ R from Pauli matrix units GroupApproximation/Analysis/PauliMatrixUnits.lean
CLAIM the tracial ultrapower R^ω (bounded sequences modulo the 2-norm null ideal, ultratrace) GroupApproximation/Analysis/HyperfiniteTracialUltrapower.lean
CLAIM unital trace-preserving *-homomorphism from the tracial matrix ultraproduct into R^ω (the interface for oa-ozawa71) GroupApproximation/Analysis/MatrixUltraproductToHyperfiniteUltrapower.lean

## Model: why this R
R := L_β(Γ), the twisted group von Neumann algebra of Γ = ℕ →₀ (ZMod 2 × ZMod 2) for the Pauli bicharacter
β((a,b),(c,d)) = Σ_i b_i c_i, acting on ℓ²(Γ) by (λ_g f)(h) = (-1)^{β(g, h-g)} f(h-g).
- λ_g λ_k = (-1)^{β(g,k)} λ_{g+k}; the right operators (ρ_g f)(h) = (-1)^{β(h-g, g)} f(h-g) commute with every λ_k.
- The trace is ⟪δ₀, x δ₀⟫, and δ₀ separates L_β(Γ), as for the untwisted L(G) in `Analysis/GroupVonNeumannTrace`.
- The symmetrized form β(g,k)+β(k,g) is nondegenerate, so the centre is trivial and R is a factor (the twisted analogue of ICC).
- The operators supported on sites < j span exactly M_{2^j} (Pauli matrices). So unital trace-preserving M_{2^j} ↪ R is explicit,
  and the finite-dimensional stages approximate every element in the 2-norm (hyperfinite) through finitely supported ℓ² vectors.
- For every n, and for the tracial matrix ultraproduct, the passage into R^ω uses dyadic corners M_n ⊗ 1_r ⊂ M_{2^j} with
  2-norm unit defect √(n/2^j) → 0. No projection comparison theory is needed.
- For oa-mcduff: L(G) ⊗̄ R is the twisted algebra of G × Γ on ℓ²(G × Γ), with no completed Hilbert tensor product. The
  interleaving bijection Γ × Γ ≅ Γ (even and odd sites) preserves β, which gives R ⊗̄ R ≅ R spatially.
- Notation point: the printed R is "the" hyperfinite II₁ factor. This lane proves that the Pauli model is a hyperfinite II₁
  factor; uniqueness up to isomorphism (Murray–von Neumann) is not part of this claim.

## Ownership check (20:3x)
- origin, the shared tree, `lanes/*.files` and landed.log have no hyperfinite, ultrapower or twisted group algebra module.
- oa-mcduff owns the II₁-factor predicate (`Analysis/GroupVonNeumannIIOneFactor`) and the spatial tensor product; this lane
  proves that R satisfies that predicate once it lands.
- Consumed carriers: `Analysis/GroupVonNeumannAlgebra`, `GroupVonNeumannTrace`, `TwoSidedRegularCommutant`,
  `ReducedGroupCStarTrace(Faithful)` (the untwisted L(G) and its coefficient calculus), `TracialMatrixUltraproduct` and
  `TracialQuotientCStar` (∏_ω M_n with its ultratrace).

## Ledger
No census rows of this lane's own: the printed sentences l.168–173 belong to oa-ozawa71 and oa-mcduff, which consume these modules.
