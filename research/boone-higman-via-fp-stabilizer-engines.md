---
rg: 2
id: boone-higman-via-fp-stabilizer-engines
kind: route
title: Embed the input in a finitely presented decidable group B_0 (Clapham), double it to B = B_0 wr Z/2 so that the input lies in [B, B], and take the derived full group of Z/2 * B on its compactified Bass–Serre tree
target: boone-higman-conjecture
requires:
  - clapham-fp-embedding-preserves-word-problem
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
  - fp-decidable-vertex-groups-have-fp-stabilizer-engines
---

**Correction, 2026-09-20.** The historical deduction below has an additional
algebraic error: `g ↦ (g,g⁻¹)` is not a homomorphism for nonabelian inputs.
`inverse-diagonal-is-homomorphic-iff-abelian` now invalidates this route in
the graph. Its commutator identity is true elementwise and does not fix the
map. A perfect decidable finitely presented envelope from
`mitosis-and-virtually-free-perfect-envelope-proof` supplies a legitimate
replacement embedding where applicable; the engine premise remains refuted.
The text below is retained as the historical failed deduction.

Let `G` be a finitely generated group with solvable word problem. We may assume `G` is
infinite, since finite groups embed in Thompson's `V`.

1. **Clapham.** `G` embeds in a finitely presented group `B_0` with solvable word problem
   (`clapham-fp-embedding-preserves-word-problem`).
2. **Doubling.** Put `B = B_0 ≀ Z/2 = (B_0 × B_0) ⋊ ⟨τ⟩`, with `τ` swapping the factors.
   - `B` is finitely presented, infinite and has solvable word problem.
   - The map `g ↦ (g, g^{-1})` is an injective homomorphism `G -> B_0 × B_0`.
   - Its image lies in `[B, B]`: `(g, g^{-1}) = [(g, 1), τ]`.
3. **The engine.** `B <= F_B`, so `[B, B] <= [F_B, F_B] = D(F_B)`. `D(F_B)` is simple
   (`free-product-boundary-groupoids-carry-the-vertex-group-homology`) and finitely presented
   by the open `fp-decidable-vertex-groups-have-fp-stabilizer-engines`. So `G` embeds in a
   finitely presented simple group. `∎`

**Status. DEAD AS STATED (2026-09-18).** Its engine claim
`fp-decidable-vertex-groups-have-fp-stabilizer-engines` is refuted by
`free-product-emitter-full-groups-need-isolated-vertex-groups`: a finitely presented
`D(F_B)` forces `B` to be *isolated* (finitely presented and finitely discriminable), and Reid's
`B = Z` fails.
- Clapham's `B_0` need not be isolated. For residually finite `B_0` neither `B_0` nor
  `B_0 ≀ Z/2` is isolated.
- **The corrected route** replaces step 1 by "`G` embeds in an isolated group `B_0`". Then
  `B = B_0 ≀ Z/2` is isolated (Cornulier–Guyot–Pitsch, Thm. 7), and step 3 needs the corrected
  engine conjecture for isolated `B`.
- The new step 1 is exactly Cornulier–Guyot–Pitsch Question 4 (J. Algebra 2007), which is
  open and weaker than Boone–Higman. So the corrected route shows: corrected engine
  conjecture ⇒ (BH ⟺ CGP Question 4).

## Lesson for general BH

The asserted doubling embedding is invalid, as the correction above explains.
A valid perfect-envelope construction repairs this algebraic step only.
Finite presentation of the proposed engine remains a separate, already
obstructed premise; finitely presented decidable germs do not supply it.
