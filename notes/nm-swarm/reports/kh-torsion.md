# Lane kh-torsion — report

Non-MF verbatim formalization swarm, 2026-09-12.

## Scope: disc moves HC3(a)–(c) for the systolic filling

go-sr1's `GGT/SystolicDisc.lean` names the disc moves as Props.  This lane proves the
first three.  By the lead's assignment, HC3(d) `ZipSpurStatement` belongs to kh-ejz
(`GGT/SystolicDiscZip.lean`) and HC6 `MirrorFoldStatement` to fff-periodic
(`GGT/SystolicDiscMirrorFold.lean`).

Proved and compiled, with classical axioms only (`propext`, `Classical.choice`, `Quot.sound`):

```lean
namespace GroupApproximation.Systolic
variable {V : Type u} {X : TriangleComplex V}

-- HC3(a), GGT/SystolicDiscMovesChord.lean
theorem attachTriangleStatement : AttachTriangleStatement X
--   ∀ (p q : List V) (u v w : V), X.Tri u v w →
--     TriangulatedDisc X (p ++ u :: w :: q) → Nonempty (TriangulatedDisc X (p ++ u :: v :: w :: q))

-- HC3(b), GGT/SystolicDiscMovesChord.lean
theorem insertChordStatement : InsertChordStatement X
--   ∀ (p q : List V) (u v w : V), X.Tri u v w →
--     TriangulatedDisc X (p ++ u :: v :: w :: q) → Nonempty (TriangulatedDisc X (p ++ u :: w :: q))

-- HC3(c), GGT/SystolicDiscMovesAdapter.lean
theorem attachPendantStatement : AttachPendantStatement X
--   ∀ (p q : List V) (u v : V), X.G.Adj u v →
--     TriangulatedDisc X (p ++ u :: q) → Nonempty (TriangulatedDisc X (p ++ u :: v :: u :: q))
```

The Props are go-sr1's definitions on main, unchanged.

## Modules

| module | contents | commit |
|---|---|---|
| `GGT/SystolicDiscMovesCycle` | `CycleDisc` (the exterior face as an explicit face cycle), `boundary`, `facePerm_not_mem`, `pendant`, `attachPendant`, `attachPendant_end` | 1725234e35 |
| `GGT/SystolicDiscMovesAdapter` | `ofFn_pow_eq_map_orbitWalk`, `isFaceCycle_pow_length`, `ofFn_boundary_eq`, `CycleDisc.toTriangulatedDisc`, `CycleDisc.exists_of_triangulatedDisc`, `split_boundary`, `attachPendantStatement` | 3d09a67ab |
| `GGT/SystolicDiscMovesChord` | `tri_rotate`, `chordLab`, `chordLab_sigma`, `chordLab_adj`, `CycleDisc.insertChord`, `insertChordStatement`, `attachTriangleStatement` | 88688fc8d |

Evidence: probe 0912-094151-47198 is PROBE GREEN with `BUILT GroupApproximation.GGT.SystolicDiscMovesChord`,
and the compiled md5s of all three files equal origin/main (Cycle `d593b26a`, Adapter `fcc42b57`,
Chord `39a37a9a`).  The adapter was also built on its own in probe 0912-093641-10337.

## Route

* HC3(c).  Put the disc in cycle form, split the boundary list at `u` (`split_boundary`: `u`
  labels a dart of the cycle, or it is the closing vertex), insert a pendant edge with
  `EdgeInsertion`, and convert back.
* HC3(b).  Split at `u`.  The next two cycle darts carry `v` and `w`; the rotated cycle's
  chain shows `facePerm dv` is labelled `w`, including the wrap-around cases.  Inserting the
  chord from `du` to `facePerm dv` cuts off the triangle, which becomes an inner face
  (`chordLab`).
* HC3(a).  Attach the pendant `u–v`, then cut off `v u w` with the chord move, using `X.tri_swap12`.

## Wiring and residuals

The three modules are orphans, not reachable from the root.  A consumer imports
`GroupApproximation.GGT.SystolicDiscMovesChord`, which imports the other two.

In this scope no statement is left open.  The cycle-form API above is available to kh-ejz and
fff-periodic for HC3(d) and HC6.  This lane has added no census rows.

## 2026-09-13: HC3(d), the zip spur (every-line swarm)

Roster target: closed hzip, `zipSpur_cosetComplex : Systolic.ZipSpurStatement CCKW.cosetComplex`,
with the producer stated for every triangle complex `X`.  HC3(d) was reassigned here from kh-ejz.

Split.  Put the disc in cycle form and split the boundary so that the exterior cycle is
`s ++ du :: dv :: t`, with the backtrack `u v u` at `du dv`.  Let `p` be the exterior dart
before `du`.

* Fold, `¬ sigma.SameCycle (alpha p) (alpha dv)`: the corners before `du` and after `dv` lie at
  different vertices, so the two edges fold together.  This is `CycleDisc.zip_fold` in
  `GGT/SystolicDiscZipFold`: probe 0913-013751-25100 green, landed 4e52166c8.
* Pinch, `sigma.SameCycle (alpha p) (alpha dv)`: both corners lie at one vertex, and the loop
  `du dv` pinches off.  This includes the spur `dv = alpha du`.  It is stated as
  `ZipPinchStatement X` in `GGT/SystolicDiscZipFold` (9445c7860) and handed to systolic-counts,
  who will prove `zipPinchStatement` in `GGT/SystolicDiscZipPinch`.

Assembly, `GGT/SystolicDiscZip` (9445c7860):

* `CycleDisc.boundary_eq_take`: the boundary walk closes at its first label.
* `CycleDisc.zip_spur`: case split on `SameCycle`.
* `zipSpurStatement_of_zipPinch (hpinch : ZipPinchStatement X) : ZipSpurStatement X`.  The cases
  come from `split_boundary`: the walk after the backtrack is empty (the walk `[u]`), a single
  closing vertex, or a longer run.

Evidence: probe 0913-015959-45107 (base 9445c7860) is PROBE GREEN with
`BUILT GroupApproximation.GGT.SystolicDiscZipFold` and `BUILT GroupApproximation.GGT.SystolicDiscZip`,
and no warnings.  `zipSpurStatement_of_zipPinch` depends on axioms `[propext, Classical.choice, Quot.sound]`.
root-wire's wave 2 (c72bdfd5d) put both modules in the root.

### hzip closed

systolic-counts proved the pinch case, `theorem zipPinchStatement (X : TriangleComplex V) :
ZipPinchStatement X` in `GGT/SystolicDiscZipPinch` (d74b84054, probe 0913-023335-5925 green).
`GGT/SystolicDiscZip` (LANDED 8389a0e6c) now closes HC3(d):

```lean
namespace GroupApproximation.Systolic
theorem zipSpurStatement : ZipSpurStatement X :=
  zipSpurStatement_of_zipPinch (zipPinchStatement X)
end GroupApproximation.Systolic

namespace GroupApproximation.KMSGroup.CCKW
theorem zipSpur_cosetComplex : Systolic.ZipSpurStatement cosetComplex :=
  Systolic.zipSpurStatement
end GroupApproximation.KMSGroup.CCKW
```

Evidence: probe 0913-030432-13308 (base 2a5ddc58f) is PROBE GREEN with
`BUILT GroupApproximation.GGT.SystolicDiscZip`, an empty errors section and no warnings.  In that
build `#audit_closed_axioms` prints `'GroupApproximation.KMSGroup.CCKW.zipSpur_cosetComplex' depends
on axioms: [propext, Classical.choice, Quot.sound]`.  The `#audit_axioms` lines, including
`zipSpurStatement`, pass without error.

Consumers can drop hzip:
* `CCKW.systolicInvariantClique_of_zipFold` (kh-cckw) takes `hzip : ∀ V X, ZipSpurStatement X`.
  Pass `fun _ _ => Systolic.zipSpurStatement`.
* `KotowskiOllivierClosed.kotowskiOllivier_of_leaves` (ko-closed),
  `GHBQuotient.isHyperbolicGroup_ghb7_of_zipFold`, `KotowskiOllivierLeaves` and
  `TheoremCAssemblyKOLeaves` take `hzip : ZipSpurStatement CCKW.cosetComplex`.  Pass
  `CCKW.zipSpur_cosetComplex`.
* `SystolicDiscFilling` (`hd`) and `SystolicInvariantClique.exists_invariantClique_of_linksSixLarge`
  take the Prop for a general `X`.  Pass `Systolic.zipSpurStatement`.

`GGT/SystolicDiscZip` was already in the root, so these bytes bring `GGT/SystolicDiscZipPinch` and
`GGT/VanKampen/PinchLemma` into the root closure.  A name scan found no clashes with other declarations.

Residual in this lane: none.  hKO still waits on hfold (`MirrorFoldDistinct` with ko-closed,
`MirrorFoldPinched` with theoremc-retire).
