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
09-18 20:55: all 11 GraphProducts modules are on main (8d6acdcd0c, coordinator sweep; red allowed, never probed).
  Re-probe of GraphProducts.Main against main (empty overlay) is queued behind Slurm batch 1338076.
  Workdir holds hardening edits ready for the next probe: explicit CoprodI.of families, rfl for lift_mk',
  induction-using instead of beta-unreduced refine, cases instead of subst, and no let-bound Normal subgroup.
  Status: question31_of_envelopeInput : EnvelopeInput → Question31. The one hypothesis left is
  EnvelopeInput = BFFHZ Thm C (i)⇒(iv) + Thm E. ProductInput (Zaremsky 5.5) is proved in ProductInput.lean.
09-18 21:30: landed the hardening edits as ab84f925c9 (8 modules) and 70e4d3e8e4 (FreeProductMap). UNPROBED: Slurm submission is
  blocked group-wide (state/SLURM-BLOCKED). The empty-overlay probe of GraphProducts.Main is still queued, and
  I re-probe once when the flag clears.
