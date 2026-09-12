# systolic-counts lane report

Lane `systolic-counts` (clone `cs-stages`, shared with go-sr1).  Goal: unblock
`GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold` (kh-hyperbolic, `Kazhdan/GHBHyperbolicDiscCounts`), which imports
go-sr1's red `GGT/SystolicDiscFilling` and `GGT/SystolicDiscCounts`, and then discharge its two open
hypotheses `hzip : Systolic.ZipSpurStatement CCKW.cosetComplex` and
`hfold : Systolic.MirrorFoldStatement CCKW.cosetComplex`.

## 09-12 10:25 status

* File split proposed to go-sr1: systolic-counts takes `GGT/SystolicDiscFilling`, go-sr1 keeps
  `GGT/SystolicDiscCounts` (go-sr1 is editing Counts in the tree).  Awaiting go-sr1's agreement; no edit to
  the tree yet.
* Red evidence for Filling: probe 0912-092123-9062 (base 40ecb054b), four real errors:
  * lines 110, 117, 122: `rintro (hlen | ⟨D⟩)` on `x.length = 1 ∨ Nonempty (TriangulatedDisc X x)` names
    the `Nonempty` proof `D` without destructuring it (the one-element tuple is read as the field
    list of `Or.inr`), so `hc/hb/ha p q .. D` get `Nonempty (..)` where a disc is expected;
  * line 142: `List.length_singleton` is an unused simp argument (warningAsError).
  The two `sorryAx` audit errors are consequences.
* Draft fix (scratch): `rintro (hlen | hD)` then `obtain ⟨D⟩ := hD` in all four branches; drop
  `List.length_singleton`.  To be put into the tree, landed `NM_ATTIC`, and probed once go-sr1 agrees.

## Residual statements on this route

* `Systolic.ZipSpurStatement CCKW.cosetComplex` (HC3(d)): owner kh-torsion (`GGT/SystolicDiscZip.lean`,
  not on main yet).
* `Systolic.MirrorFoldStatement CCKW.cosetComplex` (HC6): owner fff-periodic
  (`GGT/SystolicDiscMirrorFold.lean`, not on main yet).
* Producers already on main: `attachPendantStatement` (SystolicDiscMovesAdapter),
  `insertChordStatement` and `attachTriangleStatement` (SystolicDiscMovesChord).
