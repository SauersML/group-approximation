# kh-ejz lane report (2026-09-11/12)

Scope: property (T) of GHB(7), the `hT` leaf of kh-cckw's `ghb7LatticeRouteInput`, and the fidelity
of that statement to the manuscript's use of property (T).

## Results (relaunch 2026-09-12)

1. **Compiled bytes = origin bytes.** All ten lane files (ThreeVertexDuality, Closure, Proposition,
   Kazhdan; EJZAngleTranslates, Heisenberg, Bessel, SylowFourGram, SylowFour, GHB) match green probe
   0912-004202-1394 on origin/main; EJZAngleGHB landed f816893382e0. Nothing to land. EJZAngleSylowFour
   and EJZAngleGHB are root-wired (bfbe000c7), so `hasKazhdanPropertyT_ghb7` sits inside the root axiom
   audit.
   `GroupApproximation.KMSGroup.GHBQuotient.hasKazhdanPropertyT_ghb7 : HasKazhdanPropertyT.{0, 0} (GHB 7)`
   (Kazhdan/EJZAngleGHB.lean), under `#audit_closed_axioms`.
2. **`hT` discharged.** New module Kazhdan/GHBLatticeRouteKazhdan (in the lead's next root-wiring wave at
   green bytes 0912-093109-89237): landed 5a5886551,
   green probe 0912-092240-22748 (the normal landing reported NOTHING TO LAND, bytes identical).
   ```lean
   def PrintedGHB7PropertyT : Prop :=
     HasKazhdanPropertyT.{0, 0} (GHB 7) ∧ HasKazhdanPropertyTComplex.{0, 0} (GHB 7)
   theorem printedGHB7PropertyT : PrintedGHB7PropertyT          -- #audit_closed_axioms
   def ghb7KazhdanLatticeRouteInput (hconj : CCKWFiniteOrderConjugateIntoVertex)
       [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
       (h4 : Nat.card (U4 7) ≤ 7 ^ 4) (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) :
       Hyperbolic.LatticeRouteInput
   theorem sharpExistence_of_ghb7KazhdanLeaves (same binders) : Hyperbolic.SharpExistence
   ```
   Extension, landed 8085b58cd, green probe 0912-093109-89237: the same module spends `h3`, `h4`
   through `card_U3_seven_le`, `card_U4_seven_le` (Kazhdan/UnipotentSylowCounts, root-wired) and names
   the Fournier-Facio input.
   ```lean
   theorem sharpExistence_of_ghb7ConjHyp (hconj : CCKWFiniteOrderConjugateIntoVertex)
       (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) : Hyperbolic.SharpExistence
   theorem kotowskiOllivierStatement_of_ghb7ConjHyp (hconj : CCKWFiniteOrderConjugateIntoVertex)
       (hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)) :
       Manuscript.NonMF.TheoremC.KotowskiOllivierStatement
   ```
3. **Fidelity.**
   - Definition and universe: no gap. `HasKazhdanPropertyT.{0,0}` (real orthogonal representations on
     real Hilbert spaces in `Type`) is equivalent to the textbook complex-unitary form at every
     representation universe (`hasKazhdanPropertyT_iff_textbook`, Kazhdan/KazhdanUniverse.lean);
     `PrintedGHB7PropertyT` records both forms.
   - Manuscript: the tex names no GHB(7), no CCKW, no Kotowski–Ollivier, and prints no definition of
     (T). Property (T) enters at tex 1675 (`G_0` with property (T), citing [FFF §2]); inside [FFF §2]
     the input is an infinite finitely presented torsion-free hyperbolic group with (T).
   - Route: `TheoremC.KotowskiOllivierStatement` is `abbrev … := Hyperbolic.SharpExistence`
     (Manuscript/NonMF/FournierFacioInput.lean), the field `kotowskiOllivier` of
     `TheoremC.LiteratureInputs`, consumed as `hKO` by `HullSC.literatureInputs_of_leastAreaLeaves`
     and `manuscriptTorsionFreeTheorem_of_hullLeaves` (TorsionFreeLiteratureInputsLeastArea).
     `TheoremC.kotowskiOllivier` (TheoremCAssembly) is still `sorry`. Once `hconj` and `hhyp` are
     proved, `kotowskiOllivierStatement_of_ghb7ConjHyp` replaces that `sorry` with GHB(7) as witness.

Census: metadata/nm-census-rows/kh-ejz.tsv, LINE:1675 `partial` (does not carry the sentence).

## Remaining leaves of the GHB(7) route
- `hconj : CCKWFiniteOrderConjugateIntoVertex` (CCKW Theorem 3.1(ii), cyclic case): kh-cckw.
- `hhyp : Hyperbolic.IsHyperbolicGroup (GHB 7)` (CCKW Theorem 3.1(i)): kh-hyperbolic.
  `GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold (hzip : Systolic.ZipSpurStatement CCKW.cosetComplex)
  (hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex) : Hyperbolic.IsHyperbolicGroup (GHB 7)`
  (Kazhdan/GHBHyperbolicDiscCounts, glue landed 6827a8024 unverified; waits on go-sr1's SystolicDiscFilling
  and SystolicDiscCounts) has exactly the type of the `hhyp` binder. Owners (lead ruling 2026-09-12):
  - `hzip`: `Systolic.zipSpur X : Systolic.ZipSpurStatement X` (GGT/SystolicDiscZip.lean), kh-torsion.
    It was briefly assigned to kh-ejz, which wrote no Lean and handed over its case analysis: pendant
    edge, fold of two edges at distinct vertices, and a cut vertex through
    `restrict_planar_of_euler_four`, with the `[u]` branch at outer degree 2.
  - `hfold`: `Systolic.mirrorFold X : Systolic.MirrorFoldStatement X`, fff-periodic.

## Current assignment (2026-09-12)
Hyde–Lodha Proposition 4.7, alongside fff-quotient:
`HydeLodha.StabKFinitelyPresented Γ` (GroupTheory/HydeLodha/QTwoFinitelyPresented.lean). kh-ejz takes one
separable sub-lemma that fff-quotient is not writing; the statement and path are agreed before any Lean is
written. Edits to the rooted Q2 modules (QTwoFinitelyPresented, QTwoFinitePresentationShort,
QTwoBrownTriangle, QTwoFinitePresentationLong) land NM_ATTIC until green.

## Landing rule
Edits to EJZAngleGHB, EJZAngleSylowFour and GHBLatticeRouteKazhdan land with NM_ATTIC until a probe is
green, never NM_UNVERIFIED.

## Model test (scratch Python, not landed)
- Regular-representation angles of the CCKW Prop 7.15 images in SL4(F7): <a,b> (343) 0.377964 = 1/√7;
  <c,b>, <c,a> (2401) 0.534522 = √(2/7).
- 1/√2 (HeisenbergAngleBound) FAILS both EJZ Cor 3.3 and Thm 5.9 for GHB(7).
- Sharp angles pass Cor 3.3: eps0 = 0.958 < 1.  Rational constants: e3 = 0.378, e1 = e2 = 0.5346,
  eps0 = 0.96.
- U4 key inequality Σ_{0<m<p} ⟨x, b^m x⟩ / ‖x‖² ≤ 0.22 on samples (claim ≤ 1).

## GREEN, landed
- PropertyT/ThreeVertexDuality: EJZ Lemma 2.4 (density form), Lemma 2.5.
- PropertyT/ThreeVertexClosure: closures, EJZ (3.3), two-subspace estimate.
- PropertyT/ThreeVertexProposition: EJZ Prop 3.2 in Hilbert form (density replaces X + Y = U).
- PropertyT/ThreeVertexKazhdan: MovingAngleLE, isKazhdanSubset_of_movingAngles (EJZ Cor 3.3(a)).
- Kazhdan/EJZAngleTranslates: translate sums; twisted fixed vectors orthogonal off V^z.
- Kazhdan/EJZAngleHeisenberg: movingAngleLE_heisenberg (1/√p, CCKW Prop 7.3(i), character-free).
- Kazhdan/EJZAngleBessel: Bessel for translate sums over transversal cyclic subgroups; w^i z^j calculus.
- Kazhdan/EJZAngleSylowFourGram: a b^m = b^m a w^m z^{m(m-1)/2}; Gram-sum bound for U4(p).
- Kazhdan/EJZAngleSylowFour: movingAngleLE_sylowFour (√(2/p), CCKW Prop 7.3(ii), character-free).
- Kazhdan/EJZAngleGHB: hasKazhdanPropertyT_ghb7.
- Kazhdan/GHBLatticeRouteKazhdan: PrintedGHB7PropertyT, sharpExistence_of_ghb7KazhdanLeaves,
  sharpExistence_of_ghb7ConjHyp, kotowskiOllivierStatement_of_ghb7ConjHyp.

## TRAPS
- `omit [..] in` must precede the docstring, not sit between docstring and theorem.
- `Finset.add_sum_erase _ _ h` cannot infer the summand: pass the lambda explicitly.
- `gcongr` may discharge side goals itself; following `·` bullets then fail with "no goals".
- Unused simp args are errors (`simp [real_inner_self_eq_norm_sq]` when simp closes without it).
