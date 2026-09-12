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
