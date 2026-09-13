# dgo-geometric lane report

Lane of the non-MF verbatim swarm. It owns the geometric DGO/Osin carriers and the GHW archimedean
modules `Kazhdan/GHWArchimedeanMinkowski` and `Kazhdan/GHWArchimedeanWalls`.

## 2026-09-13: W3 MirrorFold leaf truth audit

The lead's assignment:
- check that `Systolic.MirrorFoldDistinctStatement X` and `Systolic.MirrorFoldPinchedStatement X`
  (`GGT/SystolicDiscMirrorFoldCases`, 0fb6f2305) hold for every triangle complex `X`;
- build models;
- check the consumer.

Checked against origin 19461b5bc.

### Verdict: both Props are true for every `X`
- The proof uses only irreflexivity of `X.G` and `tri_adj`.
  - Write the face of `d` as `[d, d1, d2]` (vertices `u → v → w`) and the face of `alpha d` as
    `[alpha d, e1, e2]` (`v → u → w'`).
  - Adjacent labels make `u, v, w` pairwise distinct disc vertices, and likewise `u, v, w'`.
  - No edge joins `w` and `w'`.
- No systolic, 6-large, simply connected or locally finite hypothesis enters.
- `TriangulatedDisc` asks for no simplicity, no injective labels and no simple boundary.

**Distinct (`w ≠ w'`).**
- The fold:
  - delete the six triangle darts;
  - pair `alpha d2 ↔ alpha e1` and `alpha d1 ↔ alpha e2`;
  - keep `facePerm` on the remaining darts.
- Counts: the rotations at `u` and `v` stay single cycles, and those at `w` and `w'` merge. So V−1,
  E−3, F−2, the map stays connected, and χ = 2.
- The outer cycle and `base` are unchanged, so `γ` is kept and `innerFaceCount` drops by exactly 2.
- In repo primitives:
  1. `EdgeDeletion` of `d`;
  2. `FoldMap.IsFoldable (p := d1) (d := d2) (e := e1)`, whose `distinct_ends` is exactly `w ≠ w'`;
  3. `FoldStage.deleteDigon`.

**Pinched (`w = w'`).**
- Delete the edge of `d`. The face `[d1, d2, e1, e2]` passes through `w` twice.
- Split `w` with `FoldMap.joined M d1 e1`, which is `PinchLemma` with `(p, d, e) := (d1, d2, e1)`:
  - `split_euler` gives χ = 4;
  - `reach_or_reach` and `not_reach_p` give exactly two components, with faces `[d1, e2]` and
    `[d2, e1]`;
  - `CombMap.restrict_planar_of_euler_four` makes both planar.
- Keep the component with the outer face and delete its digon. The drop is at least 2 and `γ` is
  kept. The loss can exceed 2, which is why the Prop says `+ 2 ≤`.
- Coinciding edges:
  - a coinciding `u–w` edge (`e1 = alpha d2`) or `v–w` edge needs no special case, because the spur
    side is a one-edge sphere that cannot contain the outer face;
  - both coinciding is impossible, because the pair would close up with no outer face.
- `eulerCharacteristic_le_two` is proved in `VanKampen/CombMapEulerUpperBound`.

### Models (paper, dart level)
`X` is the 2-simplex on `{a, b, c}`, with `x̄ = alpha x` and `sigma = facePerm ∘ alpha`.

1. **Distinct.** `u=a, v=b, w=c, w'=c`.
   - Darts: `d:u→v, p:v→w, q:w→u, r:u→w', s:w'→v` and their reverses.
   - Faces: `[d,p,q]`, `[d̄,r,s]`, outer `[q̄,p̄,s̄,r̄]`. V=4, E=5, F=3, and `γ = [a,c,b,c,a]`.
   - D' is the path `a–c–b` (V=3, E=2, F=1). `innerFaceCount` goes 2 → 0.
2. **Pinched, shared `u–w` edge.**
   - Darts: `d:u→v, p:v→w, q:w→u, s:w→v` and their reverses.
   - Faces: `[d,p,q]`, `[d̄,q̄,s]`, outer `[s̄,p̄]`. V=3, E=4, F=3, and `γ = [b,c,b]`.
   - D' is the single edge `b–c`. `innerFaceCount` goes 2 → 0.
3. **Pinched, two lobes.** Add `x=a`.
   - Darts: `d,p,q`, `d̄, r:u→w, s:w→v`, `t:v→x, m:w→x`, and their reverses (14 in all).
   - Faces: `[d,p,q]`, `[d̄,r,s]`, outer `[q̄,r̄]`, `[p̄,t,m̄]`, `[s̄,m,t̄]`. V=4, E=7, F=5, and
     `γ = [a,c,a]`.
   - The split leaves the outer edge `a–c` and a separate lobe with χ = 2. `innerFaceCount` goes 4 → 0.

### Consumer
- `CCKW.systolicInvariantClique_of_zipFold` takes `∀ (V : Type) (X), MirrorFoldStatement X`.
  - It uses it only at its own `X`, through `exists_invariantClique_of_linksSixLarge`.
  - That lemma passes it to the projection-clique, triangle-condition and no-induced-4/5-cycle lemmas.
- `mirrorFoldStatement_of_cases` splits on `third d = third (alpha d)`. It hands the two Props the
  same `X` and nothing else.
- `hzip` is closed: `zipSpurStatement` in `GGT/SystolicDiscZip`.
- Universes: the Props live at `V : Type u` with `map : CombMap.{0}`, and every construction above is
  a subtype of `Dart`.
- Once both leaves close: `hfold := fun V X => mirrorFoldStatement_of_cases X (distinct X) (pinched X)`.

### Sent, residual and next
- Sent to main and to the owners, fff-periodic and systolic-counts (Pinched) and ko-closed and
  kh-cckw (Distinct).
- Residual Props owned by this lane: none.
- Next, unless the lead redirects: a Lean nonvacuity fixture of models 1 and 2, built with
  `OrbitClassifier.orbitEquiv` as in `VanKampen/SelfContiguityModel`.

## 2026-09-13: GHW char 0 handed to ghw-assembly; archimedean half on main

This lane's section of ROSTER-0913 says: "Target: closed GHWCharZeroFiniteness. Also: GHWArchimedeanBound and
GHWArchimedeanSeparation green; land the in-flight files." A reassignment line in the same roster
moves GHW char 0 (`Kazhdan/GHWCharZero`, `Algebra/IntegerGridFinite`) to ghw-assembly, so this lane
has stopped its char-0 modules.

### Char 0: stopped, with one duplicate on main
- `Algebra/IntegerPolynomialUnisolvence` was landed unverified at 4896458dc and is not wired. It
  proves the same two facts as ghw-assembly's `Algebra/IntegerGridFinite` (3108f1cc7, build fix
  489b5e67a):
  - integer polynomials of bounded total degree with bounded values on an injective complex grid
    form a finite set;
  - there is an algebraically independent `ℕ → ℂ` over `ℤ`.
- Its only probe, 0913-022920-78224, is red at line 122, and the audit of
  `finite_bounded_on_grid` shows `sorryAx`.
  - Cause: in `(coeff (expVec m) G : ℂ)`, `coeff` elaborates at `ℂ`.
  - Fix: `((coeff (expVec m) G : ℤ) : ℂ)`.
- The module is off this lane's probe list. The lead decides whether it stays on main as an orphan.
- No files were written for the rest of the char-0 route. The design was: places over
  `ℤ[t_1..t_d]` for `p ∣ M` and for total degree, archimedean places over grid evaluations, then
  `GHW.hasHaagerupProperty_of_countable_places`. It matches ghw-assembly's report.

### Archimedean half
- `GHWArchimedeanBound`, `GHWArchimedeanSeparation` and `GHWArchimedeanWedge`:
  - their origin/main blobs equal 6d8971521, 448d1bf45 and 4197466c8, and all three are wired in
    the root import list;
  - sec2-sentences' probe 0912-093859-21657 built Separation;
  - probe 0912-094259-57545 was green for Bound, where `separationFinite` and
    `ghwArchimedeanAffineBound` pass `#audit_closed_axioms`;
  - re-verification probe 0913-025429-71955 (base c3cfee844) is PROBE GREEN. Both modules were
    replayed from cache (inputs unchanged, 0 rebuilt), and Minkowski, Walls and Interfaces are
    recorded COMPILED.
- `GHWArchimedeanMinkowski` and `GHWArchimedeanWalls`: origin/main equals the green landings
  b5e5abc13 and 896416980, and both are wired.

### In-flight files
- All 28 files on this lane's probe list are byte-identical to origin/main (`git hash-object`
  against the origin blob).
- 26 are imported by the root. `GGT/HypEmbeddedCentralizer` and `GGT/OsinLinealAxis` are imported
  by the wired `Manuscript/NonMF/FreeNormalSubgroupSlice` and `GGT/OsinLinealExclusion`.
- Nothing is left to land.

### Residual Props and next item
- None owned by this lane. `GHWFinitelyGeneratedCharZero` belongs to ghw-assembly.
- Next: the lead's next item.

## 2026-09-12: GHW Theorem 4, archimedean half, wall modules green

### `GroupApproximation.Kazhdan.GHWArchimedeanMinkowski`
Compiled in probes 0912-004642-27086, 0912-092049-2822 and 0912-092424-41024. Landed at b5e5abc13;
re-landed normally after 0912-092424-41024.

- Minkowski space is `Fin 4 → ℝ` through `herm`/`coords`, with `lorentzQ v = v 0 * v 1 - v 2 ^ 2 - v 3 ^ 2`
  and polar form `lorentzB v w = v ⬝ᵥ (gram *ᵥ w)`.
- `det_gram_ne_zero : gram.det ≠ 0` (explicit `gramInv`) replaces the earlier `det_gram`.
- `conjAct g : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)` is the determinant-normalized conjugation action of
  `GL (Fin 2) ℂ`, with `conjAct_mul`, `conjAct_one`, `conjAct_inv_conjAct`, `conjAct_conjAct_inv`,
  `lorentzB_conjAct`, `abs_det_conjAct`, `measurePreserving_conjAct`,
  `conjAct_origin_of_mem_unitary` and `measurePreserving_conjAct_shell`.
- `origin = ![1, 1, 0, 0]`, `shell = {v | 1 ≤ -lorentzQ v ∧ -lorentzQ v ≤ 2}`,
  `shellMeasure = volume.restrict shell`.

### `GroupApproximation.Kazhdan.GHWArchimedeanWalls`
Green probe 0912-092424-41024 (base 896416980). Repairs were landed unverified as b9f144093, 587dde0d5
and 896416980: `open scoped symmDiff`, and a classical indicator unfolding in the norm identity. The
module was then landed normally.

- `theorem conjAct_preimage_halfSpace (g : GL (Fin 2) ℂ) (x : Fin 4 → ℝ) :
  conjAct g ⁻¹' halfSpace (conjAct g x) = halfSpace x`
- `def koopman : GL (Fin 2) ℂ →* (Lp ℝ 2 shellMeasure ≃ₗᵢ[ℝ] Lp ℝ 2 shellMeasure)`
- `def SeparationFinite : Prop := ∀ g : GL (Fin 2) ℂ,
  shellMeasure (halfSpace (conjAct g origin) \ halfSpace origin) ≠ ⊤ ∧
  shellMeasure (halfSpace origin \ halfSpace (conjAct g origin)) ≠ ⊤`
- `theorem isCocycle_wallCocycle (hfin : SeparationFinite) :
  Delorme.IsCocycle koopman (wallCocycle hfin)`
- `theorem norm_wallCocycle_sq (hfin : SeparationFinite) (g : GL (Fin 2) ℂ) :
  ‖wallCocycle hfin g‖ ^ 2 = (shellMeasure (halfSpace origin ∆ halfSpace (conjAct g origin))).toReal`
- `def wallAction (hfin : SeparationFinite) (c : ℝ) : Haagerup.AffineAction.{0, 0} (GL (Fin 2) ℂ)`
  with `wallAction_b : (wallAction hfin c).b g = c • wallCocycle hfin g`
- `def Haagerup.AffineAction.comapHom (A : AffineAction G) (ρ : Γ →* G) : AffineAction Γ` with
  `comapHom_b`.

Every audit closure is `[propext, Classical.choice, Quot.sound]`.

### Residual (with sec2-sentences)
`SeparationFinite` is a hypothesis in Walls only. sec2-sentences discharges it in
`Kazhdan/GHWArchimedeanBound` (`separationFinite`, from `Wedge.separation_diff_lt_top`). The same
module proves `ghwArchimedeanAffineBound : GHWArchimedeanAffineBound`. When this section was
written, neither `Kazhdan/GHWArchimedeanSeparation` nor `Kazhdan/GHWArchimedeanBound` had compiled.
Both compiled later on 09-12 (see the 2026-09-13 section). Pre-probe fixes sent to sec2-sentences:

- `open scoped symmDiff` in Bound;
- drop the unused `with hg`;
- `push_neg` → `push Not` in Separation.

No census row: these modules are infrastructure for the Toeplitz–Jacobson remark (tex line 1146,
[GHW, Theorem 4]) and certify no printed sentence on their own.

### Earlier compiled landings of this lane
- `GHWInterfaces`: `GHWArchimedeanAffineBound`, `GHWComplexEmbeddingExtension`.
- `ghwComplexEmbeddingExtension` (c577ea5ec).
- `isAcylindricallyHyperbolicOsin_of_limitSet`, `isAcylindricallyHyperbolicLimitSet_iff_all` (6b5a5f75e).
- `dgoTheorem235Printed` (cebe6f695).
