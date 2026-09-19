# bh-pal-graphprod
Direction: T7 = BFFHZ Q3.1 (graph products of PBH groups are PBH), unconditional Lean, Mathlib only.
Prefix: GroupApproximation/BHPalomar/GraphProducts/ (registered in LEAN-OWNERS.md).
Plan:
1. Statement.lean: IsTypeA, SatisfiesPBH, GraphProduct, Question31, RetractAmalgam, relAut (Palomar shared block).
2. Steps 1-5 of pbh-graph-product-closure-proof, no literature: X *_C (C x K) embeds in Aut_H(H * F_2)
   (FreeProductMap, Twist, Semidirect, Embedding).
3. Reduction: RetractAmalgamClosure and Question31 from two named literature Props (BFFHZ Thm C (i)=>(iv) + Thm E;
   Zaremsky Prop 5.5), plus Step 6 (graph product = retract amalgam), which is pure algebra.
Status 09-18 15:45: steps 1-2 drafted; first MSI probe queued.
