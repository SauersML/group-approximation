# Lane `lix-evenside-n` — Step D at rank `n` mod every prime dividing the rank, rank-`n` Step A, and the glue of Lemma 2

Successor of `sp-evenside-n` (report `notes/lix-stronger-lane-reports/sp-evenside-n.md`, read in
full).  Owns `GroupApproximation/CharClass/LIXStepDGen*.lean` and, by the lead's ruling of
2026-09-11 ~21:55, `CharClass/LIXLemmaTwoGen*` (rank-`n` Step A, `StepCHalf`, the glue, the
coordinate-swap bridge).  Clone: SHARED `lix-c` (rule 20).

## STEP 0 (2026-09-11 ~21:25)

* The predecessor's `LIXStepDGenParity`, `LIXStepDGenData`, `LIXStepDGenAxiomCheck` are on origin/main
  (batch 1, f643c96ea) byte-identical to the shared tree; nothing of this lane was unlanded.
* Scope (1), the `F₂` bridge `Gen.WuStepDData` / `Gen.stepD_of_wu(_stage)` with the `n = 2` rfl
  bridges, was already DONE and compiled.

## GREEN

* Probe `0911-215333-54272` on lix-c (acn112, 8818 jobs, PROBE GREEN): `BUILT` + `COMPILED`
  `CharClass.LIXStepDGenModP`, `CharClass.LIXStepDGenHalf`; `#audit_axioms` classical.
* Probe `0911-221342-93884` on lix-c (SLURM acn75, 8827 jobs, PROBE GREEN, first try): `BUILT` +
  `COMPILED` `CharClass.LIXLemmaTwoGenStepA`, `CharClass.LIXLemmaTwoGenGlue`; `#audit_axioms` classical.

## LANDED

* 1aaaa40d6 (unverified), e644de5e0 / 36226d62e (attic) — superseded by:
* **8b8f85baf NORMAL** — `LIXStepDGenModP`, `LIXStepDGenHalf` from the green record above.
  WIRE top: `GroupApproximation.CharClass.LIXStepDGenHalf`.
* 93e1d2992 — `LIXLemmaTwoGenStepA`, `LIXLemmaTwoGenGlue`, landed unverified; the green record of
  probe 0911-221342-93884 matches those origin bytes (md5 8d0433d2…, 2fea7e83…), so both are COMPILED
  on main with no second commit.  WIRE top: `GroupApproximation.CharClass.LIXLemmaTwoGenGlue`
  (reaches StepA, LIXStepDGenHalf, LIXStepDGenModP).

## What is proved (declarations)

`LIXStepDGenModP`: `Gen.gamma_rank_eq_zero_modP` (uniform theorem at `m + (n + 1)`, index-orientation
fix); `Gen.ModPStepDData n p dd R H γ`; `Gen.ModPStepDData.toParityPData` (INSTANCE of lix-evenside's
`ParityPData`, three fields derived by their producers, nothing re-derived);
`Gen.ModPStepDData.gamma_top_eq_zero`.

`LIXStepDGenHalf`: `Gen.StepDHalf n dd topClass` (section-free); `stepDHalf_of_wu(_stage)`,
`stepDHalf_of_modP(_stage)`, `stepDHalf_powers_of_modP / _of_wu` (∀ k, p ∤ k → ∀ j), and
`stepDHalf_two_iff` (n = 2 `Iff.rfl` against `LemmaTwoInput`'s stepD conjunct).

`LIXLemmaTwoGenStepA` (compiled): `Gen.fromBlocks_rankOneProj_zero`, `Gen.isStarProjection_FHmatOf`,
`Gen.isStarProjection_EHmat`, `Gen.exists_cornerUnitary_of_continuousMvNEquiv` (for any continuous unit
`b`: `G (e_last, 0) = (b, 0)`), `Gen.hasStepAUnitary_of_continuousMvNEquiv`,
`hasStepAUnitary_of_continuousMvNEquiv_of_gen` (rank-two bridge).

`LIXLemmaTwoGenGlue` (compiled): `Gen.lastZeroSwap`, `Gen.isCornerUnitary_submatrix_lastZeroSwap`,
`Gen.submatrix_lastZeroSwap_mulVec_eZero`; **`Gen.StepCHalf`** (committed spelling, sent to the lead);
**`Gen.lemmaTwoFor_of_halves`**; `Gen.lemmaTwoFor_powers_of_halves`; `Gen.lemmaTwoFor_powers_of_stepC_modP`.

## The section bridge (ruling b)

`LemmaTwoFor` keeps `e_last`, KGen keeps `e₀`.  Bridged by right multiplication, not conjugation of the
complements: Step A gives `G (e_last, 0) = (b, 0)`; `G ∘ τ = (G m).submatrix id τ` with `τ` the swap
`0 ↔ last` (identity on `H`) is a continuous corner unitary (τ fixes `V`) carrying `(e₀, 0)` to `(b, 0)`.
So Step C at `e₀` is consumed for the SAME section `b = KGen.bVecK n (k − 1)`; no `σ ∘ b` anywhere.

## Concrete mod-p assembly at the real mapping torus (option (a), approved 2026-09-11 ~22:50)

`H` and `R` of `ParityPData` must be COMMUTATIVE; over `K` at odd `p` the whole ring `TotalHOf K X` is only
graded-commutative, so they are the EVEN parts.  `CharClass/LIXStepDGenRealEven.lean`: `Gen.evenPart K X`
(subring of classes vanishing in odd degrees), `Gen.instCommRingEvenPart` (commutative with no hypothesis,
from lix-cupone's `TotalHOf.mul_comm_of_isEven_left`), `Gen.evenMap K f` (pullback as a ring hom),
`Gen.evenRestrictAdd f hf` (P^i restricted).  `CharClass/LIXStepDGenReal.lean`: `Gen.tClassOf`, `Gen.xClassOf`,
`Gen.zClass`, `Gen.isEven_zClass`, `Gen.zClass_mul_self` (z² = 0 with NO sign: z even ⇒ z t = t z, so
z z = (t t) x x = 0 from H²(S¹) = 0 alone), `Gen.RealTorusModP` (torus inputs: H²(S¹)=0, Künneth z_inj, P^i
on N and Y with P⁰ = id, Cartan, naturality, P^{>0} t = P^{>0} x = 0, instability on Y),
`Gen.RealTorusModP.PN_zClass` (P(z) = z by Cartan), `Gen.RealBundleModP` (bundle inputs: even Chern classes,
Künneth components, degree of b, slice, Wu with unit c), `RealBundleModP.instability_b`,
**`RealBundleModP.toModPStepDData`** (the instance over the even parts), `RealBundleModP.gamma_top_eq_zero`,
`Gen.realWu_of_splitting` (field wu from lix-evenside's `wu_field_of_splitting`; unit via
`ParityP.isUnit_wuLeading`), `Gen.stepDHalf_of_realModP`, `Gen.lemmaTwoFor_powers_of_stepC_realModP`.
Landed unverified: d6009101a (RealEven), 73ff46a09 + b4d828247 (Real).  Probe running on lix-c.

## NEEDS

* lix-oddside-n: `StepCHalf n (lixDD n j) (KGen.bVecK n (k − 1)) topClass` at the top mod-`p` class.
* Producers of `Gen.ModPStepDData`'s fields over real objects: `TotalH` over `F_p` + Künneth (lix-lh,
  lix-coeff); odd-primary `P^i` with Cartan, `P⁰ = id`, instability (lix-steenrod); Wu with a unit
  leading coefficient, L4a (lix-evenside).

## TRAPS

* `NM_UNVERIFIED` refuses a path already on origin/main (even an unverified landing); the in-flight edit
  goes as `NM_ATTIC=1`.
* Name resolution at v4.32 (`Lean/ResolveName.lean`, `resolveUsingNamespace`): the INNERMOST namespace
  with a match wins and open declarations are consulted only when no namespace prefix matches, so a
  `Gen.foo` shadows `CharClass.foo` inside `namespace Gen` without ambiguity.
