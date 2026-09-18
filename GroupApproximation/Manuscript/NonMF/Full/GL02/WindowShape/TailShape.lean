import GroupApproximation.Manuscript.NonMF.Full.GL02.WindowShape.TailShapeDeps
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the tail shape of a class window arc

*GL02 copy.*  Re-proof of the foreign module `Piece04.WindowShape.TailShape`
(origin/main blob `07e63cf94`), moved to namespace `Piece04.GL02` since the modules it
imports include files last changed by commits marked WIP.  Only namespaces, the imports of
copied modules, and the qualification of foreign names differ from the original.

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-07`.

*Statement* (`WindowTailShapeStatement`).  Let class `i` of polygon `k` have kind `cell j`, let
`x ≤ y ≤ |word k i|`, let `y` not lie strictly inside a gap, let the run window `U` of `[x, y]` be
nonempty, and let `arc` be an arc of `∂Π` with `arc.reverseDarts = classWindow k i x y`.  Then
`RotationTurns.WindowTailShape M U arc.darts`: `U = U' ++ [u]`, `arc.darts = γ ++ α u :: p'`, and
`σ (φ u) = γ.head` whenever `γ` is nonempty.

*Truth check (T4 of the lane file).*  Write `φ = σ α`.

1. Tail split (lane 05): `U = U' ++ [u]` and `classWindow = rest ++ u :: γc`, where `γc = []`, or
   `γc = gap_s` is the whole gap after side `s`, `u = side_s.last`, and the next class side `s'`
   starts with `e = classDarts[y]`, while `g0 = classDarts[y-1] = γc.last`.
2. `arc.darts = (arc.reverseDarts.map α).reverse` (`α` is an involution), so
   `arc.darts = (γc.map α).reverse ++ α u :: (rest.map α).reverse`.  Take
   `γ = (γc.map α).reverse` and `p' = (rest.map α).reverse`.
3. If `γc = []` then `γ = []` and there is nothing to prove.
4. Otherwise `γ.head = α g0`.  By lane 02 (`ClassSidesSucc.succ`), `s < sideCount` and
   `s' = (s + 1) % sideCount`.  By lane 03 (`SideSuccFace.facePerm_last`), `φ u = e`.  The class
   window has at least two darts and length at most `y - x`, so `1 ≤ y`, and `g0`, `e` sit at
   positions `y - 1`, `y` of the class.  By lane 01 (`ClassStep.sigma_succ`), `σ e = α g0`.  So
   `σ (φ u) = σ e = α g0 = γ.head`.

*Endpoint.*  `windowTailShape_of_windowTailSplit : WindowTailSplitStatement →
WindowTailShapeStatement`.  Lanes 01, 02 and 03 are on disk and used directly.  Lane 05 runs in
parallel and is not on disk; its target is stated with the exact lane text in
`WindowShape.TailShapeDeps`.  Once it lands, the unconditional endpoint is

```
theorem windowTailShape : WindowTailShapeStatement.{u, w, v} :=
  windowTailShape_of_windowTailSplit WindowTailSplit.split
```

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.TailShape

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents

/-- **The tail shape of a class window arc from the tail split** (lane gl-p04-07).  The class step
(lane 01), the successor sides (lane 02) and side contiguity (lane 03) are used unconditionally. -/
theorem windowTailShape_of_windowTailSplit (h5 : WindowTailSplitStatement.{u, w, v}) :
    WindowTailShapeStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts S P Q k i j x y arc hi hkind hxy hyw hng hne harc
  obtain ⟨u, U', γc, rest, hU, hW, hγ⟩ := h5 Q k i x y hi hxy hyw hng hne
  unfold RotationTurns.WindowTailShape
  refine ⟨u, U', (rest.map S.diagram.toCombMap.alpha).reverse,
    (γc.map S.diagram.toCombMap.alpha).reverse, hU, darts_eq_of_reverseDarts arc (harc.trans hW),
    ?_⟩
  intro g hg
  rcases hγ with rfl | ⟨n, s, s', e, g0, he, hg0, hlast, -, hs, hs', hu, he'⟩
  · simp at hg
  · have hg' : S.diagram.toCombMap.alpha g0 = g := alpha_eq_of_head?_reverse_map hlast hg
    have hsides := Piece04.WindowShape.ClassSidesSucc.succ Q k i hi
    have hsm : s < P.sideCount k := hsides.1 s (List.mem_of_getElem? hs)
    have hss' : s' = (s + 1) % P.sideCount k := hsides.2 n s s' hs hs'
    rw [hss'] at he'
    have hfu : S.diagram.toCombMap.facePerm u = e :=
      Piece04.WindowShape.SideSuccFace.facePerm_last Q k s hsm u e hu he'
    have hy : 1 ≤ y := one_le_of_classWindow Q k hW hlast
    have he1 : (Q.classDarts k i)[y - 1 + 1]? = some e := by
      rw [Nat.sub_add_cancel hy]
      exact he
    have hse : S.diagram.toCombMap.sigma e = S.diagram.toCombMap.alpha g0 :=
      Piece04.WindowShape.ClassStep.sigma_succ Q k i j hi hkind (y - 1) g0 e hg0 he1
    rw [hfu, hse]
    exact hg'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.TailShape.windowTailShape_of_windowTailSplit

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.GL02.WindowShape.TailShape
