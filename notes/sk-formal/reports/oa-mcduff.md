# oa-mcduff: tex l.169–173 of simple_kazhdan_sofic_group.tex (tip e80dcf20a)

Lane oa-mcduff, launched ~20:15 by main. Brief: `ct/ROSTER-sk.md`, "OA LANES 20:15". No literature input.

## CLAIM
CLAIM infinite simple ⇒ ICC and not RF (row 6e8db7db6717) GroupApproximation/Manuscript/SimpleKazhdanSofic/InfiniteSimpleICC.lean
CLAIM the II₁-factor predicate, and L(G) is a II₁ factor for infinite ICC G (row 07ce3ce2146f, first clause) GroupApproximation/Analysis/GroupVonNeumannIIOneFactor.lean
CLAIM spatial von Neumann tensor product, McDuff factors, L(G)⊗̄R McDuff, embeds in R^ω, G ⊆ U(L(G)⊗̄R) (row 07ce3ce2146f) GroupApproximation/Analysis/VonNeumannTensorProduct.lean GroupApproximation/Manuscript/SimpleKazhdanSofic/McDuffBrownFormulation.lean

## Ownership check (20:2x)
- origin: no McDuff notion, no II₁-factor predicate, no von Neumann tensor product.
- Already on origin: ICC ⇒ factor (`GroupVonNeumann.isFactor`, Analysis/GroupStandardFormInstance); the trace facts (Analysis/GroupVonNeumannTrace); not RF (`not_isResiduallyFinite_of_isSimpleGroup_of_infinite`, Manuscript/NinetyNineProblems/FactorizationProperty, root-imported).
- No lane `.files` holds a von Neumann, McDuff or hyperfinite path, and there is no other oa-* report.
- Consumed from other lanes: R, R^ω and trace-preserving embeddings (oa-hyperfinite); L(G) ↪ R^ω (oa-ozawa71).

## Ledger (tex at e80dcf20a, census 09e580c38)
| hash | tex | sentence | status | carrier |
|---|---|---|---|---|
| 6e8db7db6717 | 169–170 | Since G is infinite and simple, its nontrivial conjugacy classes are infinite and G is not residually finite. | building | InfiniteSimpleICC |
| 07ce3ce2146f | 170–173 | So L(G) is a II₁ factor, and L(G)⊗̄R is a McDuff factor that embeds in R^ω and whose unitary group contains G. | building | GroupVonNeumannIIOneFactor, McDuffBrownFormulation |
| 8085aa93f38b | 173 | This is Brown's formulation. | attribution | none |
