import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurnTerminal
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalSuccStatement
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.PocketRunArc
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSideFaces
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkNoninterleavingJoints
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: closing the petal turn statement (lane gl-p06-18b)

Target: `P06LakeFree.CellPocketLakeFreePetalTurnStatement` (`P06LakeFree/PetalSuccStatement.lean`).
Endpoint: `P06LakeFree.PetalTurn.cellPocketLakeFreePetalTurn`, and through the reductions on disk
`P06LakeFree.PetalTurn.cellPocketFaceSetLakeFreeEnclosed`.

## Truth check

The target is TRUE; nothing false was found.  The search starts from the whole boundary
`∂K = s₁ t̄₁ s₂ t̄₂` read backwards and cuts it at bad repeated vertices; the face of `C` stays
on the side of one piece.  Only the noncrossing hypothesis `hw` (no repeats, no bridges, closed
walk) and `C.face ∈ K.faces` are used; lake freeness, `i ≠ j`, letter labels and word lengths are not needed.

## The mathematical proof

1. *Environment* (`petalTurnEnv_of_cellPocket`): `T = ∂K` has no repeats and no bridges (`hw`),
   `t₁ = t̄₁` and `t₂ = t̄₂` are infixes of `T` by the decomposition, and read backwards the arcs of
   the cell boundaries turn by `σ` (`isChain_sigma_invDarts`).
2. *Initial walk* (`petalTurnInv_initial`): `W₀ = invDarts T` is a closed vertex walk with
   `invDarts W₀ = T`, a sublist of `T`, convex in every infix of `T` (no `y ∉ T` lies on it), and
   `sideFaces T = K.faces ∋ C.face` (`sideFaces_boundaryCycle_eq`, outer face off `K.faces`).
3. *Search* (`exists_succTurn_of_inv`), by induction on the length: a walk with the invariant turns
   to its successors, or is cut at a bad repeated vertex (`succTurn_or_cut`) into two shorter walks,
   one of which keeps the invariant (`petalTurnInv_cut`).
4. The terminal walk gives the target with rotation `0`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn

open Embedded SimpleClosedWalkSides

universe u w v

/-- A list is a sublist of an equal list. -/
theorem sublist_of_eq_self {α : Type*} {l l' : List α} (h : l = l') : l <+ l' := by
  subst h
  exact List.Sublist.refl _

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.sublist_of_eq_self

/-- A list equal to `T` is convex in every infix of `T`. -/
theorem runConvex_of_eq_of_infix {α : Type*} {L T t : List α} (h : L = T) (ht : t <:+: T) :
    OrderCactus.RunConvex L t := by
  intro u y v hte hy
  rw [h] at hy
  have hmem : y ∈ t := by
    rw [hte]
    exact List.mem_append_right u List.mem_cons_self
  exact absurd (ht.sublist.subset hmem) hy

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.runConvex_of_eq_of_infix

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **The environment of a cell pocket.** -/
theorem petalTurnEnv_of_cellPocket {D : RelGenSet G Lambda} {eps : ℕ}
    {X : DiscDiagram.{u, w, v} W} {i j : Fin X.rCellCount} (K : CellPocketFaceSet D eps X i j)
    (hw : IsNoncrossingClosedWalk X.toCombMap K.boundary.cycle) :
    PetalTurnEnv X K.boundary.cycle (invDarts X K.firstArc.darts)
      (invDarts X K.secondArc.darts) :=
  { nodup := K.boundary.cycle_nodup
    infix₁ := ⟨K.firstSide, K.secondSide ++ invDarts X K.secondArc.darts, by
      rw [K.decomposition]
      simp only [List.append_assoc]⟩
    infix₂ := ⟨K.firstSide ++ invDarts X K.firstArc.darts ++ K.secondSide, [], by
      rw [K.decomposition, List.append_nil]⟩
    chain₁ := SectorNoninterleaving.isChain_sigma_invDarts
      (P07InnerPocket.PocketRun.arcDarts_isChain (X.faceBoundary (cell X i).face) K.firstArc)
    chain₂ := SectorNoninterleaving.isChain_sigma_invDarts
      (P07InnerPocket.PocketRun.arcDarts_isChain (X.faceBoundary (cell X j).face) K.secondArc)
    no_bridge := hw.alpha_not_mem }

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.petalTurnEnv_of_cellPocket

/-- **The initial walk**: the boundary read backwards. -/
theorem petalTurnInv_initial {X : DiscDiagram.{u, w, v} W} {T t₁ t₂ : List X.toCombMap.Dart}
    {x₀ : X.toCombMap.Dart} (hE : PetalTurnEnv X T t₁ t₂)
    (hw : IsNoncrossingClosedWalk X.toCombMap T)
    (hs : X.toCombMap.faceOf x₀ ∈ sideFaces X.toCombMap T) :
    PetalTurnInv X T t₁ t₂ x₀ (invDarts X T) := by
  have hTT : invDarts X (invDarts X T) = T := Petal.petal_invDarts_invDarts X T
  have hne : invDarts X T ≠ [] := fun h =>
    hw.ne_nil (List.reverse_eq_nil_iff.mp (List.map_eq_nil_iff.mp h))
  have hc : T.IsChain fun a b =>
      X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha b)) =
        X.toCombMap.vertexOf (X.toCombMap.alpha a) :=
    hw.chain.imp fun a b h => by
      show X.toCombMap.vertexOf (X.toCombMap.alpha (X.toCombMap.alpha b)) =
        X.toCombMap.vertexOf (X.toCombMap.alpha a)
      rw [X.toCombMap.alpha_involutive b]
      exact h.symm
  have hch : (invDarts X T).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e := by
    show (T.reverse.map X.toCombMap.alpha).IsChain fun d e =>
      X.toCombMap.vertexOf (X.toCombMap.alpha d) = X.toCombMap.vertexOf e
    exact (List.isChain_map X.toCombMap.alpha).mpr (List.isChain_reverse.mpr hc)
  have hcl : ∀ a ∈ (invDarts X T).getLast?, ∀ b ∈ (invDarts X T).head?,
      X.toCombMap.vertexOf (X.toCombMap.alpha a) = X.toCombMap.vertexOf b := by
    intro a ha b hb
    rw [Option.mem_def, getLast?_invDarts, List.head?_eq_some_head hw.ne_nil, Option.map_some,
      Option.some.injEq] at ha
    rw [Option.mem_def, head?_invDarts, List.getLast?_eq_some_getLast hw.ne_nil, Option.map_some,
      Option.some.injEq] at hb
    rw [← ha, ← hb, X.toCombMap.alpha_involutive]
    exact hw.closes.symm
  have hside : X.toCombMap.faceOf x₀ ∈ sideFaces X.toCombMap (invDarts X (invDarts X T)) := by
    rw [hTT]
    exact hs
  exact
    { ne_nil := hne
      chain := hch
      closes := hcl
      sublist := sublist_of_eq_self hTT
      conv₁ := runConvex_of_eq_of_infix hTT hE.infix₁
      conv₂ := runConvex_of_eq_of_infix hTT hE.infix₂
      side := hside }

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.petalTurnInv_initial

/-- **The petal search terminates** in a walk turning to its successors. -/
theorem exists_succTurn_of_inv {X : DiscDiagram.{u, w, v} W} {T t₁ t₂ : List X.toCombMap.Dart}
    {x₀ : X.toCombMap.Dart} (hE : PetalTurnEnv X T t₁ t₂) :
    ∀ (n : ℕ) (W₀ : List X.toCombMap.Dart), W₀.length ≤ n → PetalTurnInv X T t₁ t₂ x₀ W₀ →
      ∃ W₁ : List X.toCombMap.Dart, PetalTurnInv X T t₁ t₂ x₀ W₁ ∧ PetalSucc.SuccTurn X W₁ := by
  intro n
  induction n with
  | zero =>
    intro W₀ hn hI
    exact absurd (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hn)) hI.ne_nil
  | succ n ih =>
    intro W₀ hn hI
    rcases succTurn_or_cut hI.chain hI.closes with hS | ⟨u, y, B, y', v, rfl, hv, hbad⟩
    · exact ⟨W₀, hI, hS⟩
    · obtain ⟨hl₁, hl₂⟩ := length_cut_lt u B v y y'
      rcases petalTurnInv_cut hE hI hv hbad with hI' | hI'
      · exact ih (y :: B) (by omega) hI'
      · exact ih (u ++ y' :: v) (by omega) hI'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.exists_succTurn_of_inv

/-- **The cactus petal as a turning walk on `∂K`** (lane gl-p06-18b). -/
theorem cellPocketLakeFreePetalTurn : CellPocketLakeFreePetalTurnStatement.{u, w, v} := by
  intro G _ Lambda W D eps X i j K _hij _hlabel _hW hw _hfree C _hC hCK
  have hE := petalTurnEnv_of_cellPocket K hw
  obtain ⟨x₀, hx₀⟩ := Quotient.exists_rep C.face
  have hx₀' : X.toCombMap.faceOf x₀ = C.face := hx₀
  have hs : X.toCombMap.faceOf x₀ ∈ sideFaces X.toCombMap K.boundary.cycle := by
    rw [sideFaces_boundaryCycle_eq (X.toCombMap.connected_of_planar X.planar) K.boundary
      K.outerFace_not_mem, hx₀']
    exact hCK
  obtain ⟨W₁, hI, hS⟩ := exists_succTurn_of_inv hE (invDarts X K.boundary.cycle).length
    (invDarts X K.boundary.cycle) (Nat.le_refl _) (petalTurnInv_initial hE hw hs)
  refine ⟨W₁, hI.ne_nil, hS, ?_, 0, ?_, ?_, ?_⟩
  · rw [← hx₀']
    exact hI.side
  · rw [List.rotate_zero]
    exact hI.sublist
  · rw [List.rotate_zero]
    exact hI.conv₁
  · rw [List.rotate_zero]
    exact hI.conv₂

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.cellPocketLakeFreePetalTurn

/-- **The lake-free enclosed face set statement holds.** -/
theorem cellPocketFaceSetLakeFreeEnclosed : CellPocketFaceSetLakeFreeEnclosedStatement.{u, w, v} :=
  cellPocketFaceSetLakeFreeEnclosed_of_petalTurn cellPocketLakeFreePetalTurn

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.cellPocketFaceSetLakeFreeEnclosed

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn
