# w1-binder-5: second start on binder 5 of the W1 waist

Lane of session `nonsofic-existence-49` (wave 2, 2026-09-13). It lands new modules only and never edits owners' files.

## Binder, verified at origin/main 19d96c2c5

- `OsinMultipleEdgePocketRegionSectionStatement` (`Estimating/OsinPocketMultipleEdgeAssembly.lean:195`). With the
  quantifier prefix of `OsinMultipleEdgeCutSectionStatement`, it concludes `MultipleEdgePocketRegionInput`
  (`Estimating/OsinPocketRegionSide.lean:49`) on `S.diagram`, with both `FollowsBoundary` clauses.
- Consumers: `osinMultipleEdgeCutSection_of_pieces`, `OsinDescentResiduals`, `OsinGreendlingerOpenResiduals`.
- Truth status (main's 15:45 ruling, after audit-sec5's truth audit): on `S.diagram`, configuration (b′) has no `P`,
  so the `S.diagram` form is circular. hull-select restates it on an O-equivalent copy with legal labels (drafts r1,
  Rule 22 co-probe).

## Producer route: the cell-to-cell analogue of kh-ejz's section-pocket route

| step | piece | state |
|---|---|---|
| 1 | walk data `s_1 t_1 s_2 t_2` | `CellPocketWalk.exists_of_joinsCells` (jacobson, 65e5e758c) |
| 2 | the walk is a nonempty closed walk (`chain`, `closes`) | no statement on origin, no in-flight file: CLAIMED below |
| 3 | `nodup`, `alpha_not_mem` on a copy | section-pocket analogue: hs-vanishes' `OsinPocketCopyWalk`; cell version open |
| 4 | orientation | section-pocket analogue: cite-hull's `PocketWalkColour.walk_orient` |
| 5 | kept cell | zero-cell merge (hull-select, closed on `S.diagram`) |
| 6 | pocket face set, pinch, region with both `FollowsBoundary` | audit-sec5 owns the cell-to-cell face set and pinch Prop (15:25 ruling) |

## Claims

CLAIM cell pocket walk chain and closes: `GroupApproximation/GGT/VanKampen/Estimating/OsinPocketCellWalkChain.lean`
- `CellPocketWalk.walk_isChain_closes`
- `CellPocketWalk.exists_of_joinsCells_closedWalk`

Both consume kh-ejz's `OsinPocketWalkChain` (ecb23058f) and jacobson's `OsinPocketCellWalk`.

## Landed

- **Step 2 CLOSED: cb5b195c8** (probe 0913-170545-75404 GREEN at base 46dd14831, BUILT
  `OsinPocketCellWalkChain`, empty error index, no `sorryAx`). The module is new, unwired and wire-queued.
  Every declaration is under `#audit_axioms`:
  ```lean
  theorem closedWalk_isChain_closes_of_interleave {S₁ T₁ S₂ T₂ A₁ A₂ B₁ B₂ : List α}
      (hA : (A₁ ++ S₂ ++ A₂).IsChain R) (hB : (B₂ ++ S₁ ++ B₁).IsChain R)
      (hT₁ : T₁.IsChain R) (hT₂ : T₂.IsChain R) (hT₁ne : T₁ ≠ []) (hT₂ne : T₂ ≠ [])
      (hT₁h : T₁.head? = B₁.head?) (hT₁l : T₁.getLast? = A₁.getLast?)
      (hT₂h : T₂.head? = A₂.head?) (hT₂l : T₂.getLast? = B₂.getLast?) :
      (S₁ ++ T₁ ++ S₂ ++ T₂).IsChain R ∧
        ∀ a ∈ (S₁ ++ T₁ ++ S₂ ++ T₂).getLast?, ∀ b ∈ (S₁ ++ T₁ ++ S₂ ++ T₂).head?, R a b
  theorem CellPocketWalk.walk_ne_nil (K : CellPocketWalk D eps X i j) : K.walk ≠ []
  theorem CellPocketWalk.walk_isChain_closes (K) (hij : i ≠ j) (ha : a.JoinsCells i j)
      (hb : b.JoinsCells i j) (hai hbi haj hbj : 0 < (_.cellArcList _).length)
      (hfirst : K.firstSide = b.sideFrom j) (hsecond : K.secondSide = a.sideFrom i) (G₁ G₂)
      (h₁ : K.firstArc.darts = a.cellArcList i ++ G₁ ++ b.cellArcList i)
      (h₂ : K.secondArc.darts = b.cellArcList j ++ G₂ ++ a.cellArcList j) :
      K.walk.IsChain R ∧ ∀ x ∈ K.walk.getLast?, ∀ y ∈ K.walk.head?, R x y
  theorem CellPocketWalk.exists_of_joinsCells_closedWalk (S : RealizedSectionFamily …)
      (ha hb hab) (hij : i ≠ j) (hai hbi) :
      ∃ K, (the conjuncts of exists_of_joinsCells) ∧
        ∃ hne : K.walk ≠ [], K.walk.IsChain R ∧ R (K.walk.getLast hne) (K.walk.head hne)
  ```
  Here `R d e` is `vertexOf (alpha d) = vertexOf e`. The joints `t_2 s_1` and `s_1 t_1` come from `b`'s boundary cycle
  rotated by `(invDarts (b.cellArcList i) ++ b.sideFrom i).length`. The joints `t_1 s_2` and `s_2 t_2` come from `a`'s
  boundary cycle (`boundary_cycle_rotate_of_joinsCells`).
- No census rows: the module certifies no printed sentence on its own.

## Residual for the binder-5 producer (cell-to-cell pocket)

- Step 3: an O-equivalent copy with legal labels satisfying cell edge conditions, then `walk.Nodup` and
  `alpha_not_mem`. This is the cell analogue of hs-vanishes' `PocketWalk.CopyClean` and
  `walk_nodup_and_alpha_not_mem`. The section version separates `Π` from the exterior face; the cell version must
  separate `Π_i` from `Π_j`. No statement is on origin.
- Step 4: orientation of the colouring, the cell analogue of cite-hull's `PocketWalkColour.walk_orient`.
- Steps 5–6: the kept cell, and the pocket region with both `FollowsBoundary` on the copy (R1). audit-sec5 owns the
  cell-to-cell face set and pinch Prop.
- Assembly target: `hull-select`'s copy form of `MultipleEdgePocketRegionInput` (drafts r1), which takes
  `CellPocketWalk.walk` as the split.
