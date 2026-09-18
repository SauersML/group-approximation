import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.TwoComplex.Homotopy
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.Setting
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown bridge I: typed edge paths as vertex lists (lane sk-leavitt-20)

Two independently authored path notions coexist under `LeavittK2`:

* lane 06, `OrderedTwoComplex.EdgePath : W → W → Type` (constructors `nil`/`fwd`/`bwd`) with
  `EdgePath.Move` (`backtrackFwd`, `backtrackBwd`, `triangle`) and `EdgePath.Homotopic`;
* lane 12, `BrownInjective.BrownSetting.IsPath a l` for lists `l` of successive vertices, with
  `BrownSetting.Move a` (`back`, `tri`) and `BrownSetting.Homotopic a`.

Route.  Along a map `f : W → V` sending edges to edges and triangles to triangles, a typed path
`p` becomes the list `toList f p` of the images of its successive vertices (`fwd` and `bwd`
steps both append the next vertex; lane 12's edges are symmetric by `edge_symm`).  The list is
a lane-12 path with the right endpoint (`toList_spec`), `toList` turns `append` into `++`
(`toList_append`), and every lane-06 move becomes a lane-12 move (`move_toList`): a backtrack
`c → w → c` is `Move.back`, a triangle passage is `Move.tri`.  Hence `toList` preserves
homotopy (`homotopic_toList`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective

variable {G V W : Type*} [Group G] [MulAction G V] {X : OrderedTwoComplex W}

/-- Lane 12's edges are symmetric: transport the base edge by `g τ`. -/
theorem edge_symm (S : BrownSetting G V) {a b : V} (hab : S.edge a b) : S.edge b a := by
  obtain ⟨g, hg0, hg1⟩ := S.edge_transitive a b hab
  have h := S.edge_smul (g * S.tau) S.v0 S.v1 S.edge_base
  rwa [mul_smul, mul_smul, S.tau_v0, S.tau_v1, hg0, hg1] at h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.edge_symm

theorem isPath_cons (S : BrownSetting G V) (a b : V) (l : List V) :
    S.IsPath a (b :: l) ↔ S.edge a b ∧ S.IsPath b l :=
  Iff.rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.isPath_cons

theorem endpoint_cons (S : BrownSetting G V) (a b : V) (l : List V) :
    S.endpoint a (b :: l) = S.endpoint b l :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.endpoint_cons

/-- The list of images of the successive vertices of a typed edge path. -/
def toList (f : W → V) : {a c : W} → X.EdgePath a c → List V
  | _, _, .nil _ => []
  | _, _, @OrderedTwoComplex.EdgePath.fwd _ _ _ b _ _ p => f b :: toList f p
  | _, _, @OrderedTwoComplex.EdgePath.bwd _ _ _ b _ _ p => f b :: toList f p

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.toList

theorem toList_nil (f : W → V) (a : W) :
    toList f (OrderedTwoComplex.EdgePath.nil (X := X) a) = [] :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.toList_nil

theorem toList_fwd (f : W → V) {a b c : W} (e : X.edge a b) (p : X.EdgePath b c) :
    toList f (OrderedTwoComplex.EdgePath.fwd e p) = f b :: toList f p :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.toList_fwd

theorem toList_bwd (f : W → V) {a b c : W} (e : X.edge b a) (p : X.EdgePath b c) :
    toList f (OrderedTwoComplex.EdgePath.bwd e p) = f b :: toList f p :=
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.toList_bwd

theorem toList_append (f : W → V) :
    ∀ {a b c : W} (p : X.EdgePath a b) (q : X.EdgePath b c),
      toList f (p.append q) = toList f p ++ toList f q
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .fwd _ p, q => congrArg (List.cons _) (toList_append f p q)
  | _, _, _, .bwd _ p, q => congrArg (List.cons _) (toList_append f p q)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.toList_append

/-- The image list of a typed path is a lane-12 path with the image endpoint. -/
theorem toList_spec (S : BrownSetting G V) (f : W → V)
    (hedge : ∀ u w : W, X.edge u w → S.edge (f u) (f w)) :
    ∀ {a c : W} (p : X.EdgePath a c),
      S.IsPath (f a) (toList f p) ∧ S.endpoint (f a) (toList f p) = f c
  | _, _, .nil _ => ⟨trivial, rfl⟩
  | _, _, .fwd e p => by
    rw [toList_fwd, isPath_cons, endpoint_cons]
    exact ⟨⟨hedge _ _ e, (toList_spec S f hedge p).1⟩, (toList_spec S f hedge p).2⟩
  | _, _, .bwd e p => by
    rw [toList_bwd, isPath_cons, endpoint_cons]
    exact ⟨⟨edge_symm S (hedge _ _ e), (toList_spec S f hedge p).1⟩,
      (toList_spec S f hedge p).2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.toList_spec

/-- Every lane-06 elementary move becomes a lane-12 elementary move. -/
theorem move_toList (S : BrownSetting G V) (f : W → V)
    (hedge : ∀ u w : W, X.edge u w → S.edge (f u) (f w))
    (htri : ∀ u v w : W, X.tri u v w → S.tri (f u) (f v) (f w))
    {a d : W} {p q : X.EdgePath a d} (hm : OrderedTwoComplex.EdgePath.Move p q) :
    S.Move (f a) (toList f p) (toList f q) := by
  cases hm with
  | @backtrackFwd _ c s e r =>
    obtain ⟨hs, hend⟩ := toList_spec S f hedge s
    have hr := (toList_spec S f hedge r).1
    have hp : S.IsPath (f a)
        (toList f s ++ f c :: S.endpoint (f a) (toList f s) :: toList f r) := by
      rw [BrownSetting.isPath_append, hend, isPath_cons, isPath_cons]
      exact ⟨hs, hedge _ _ e, edge_symm S (hedge _ _ e), hr⟩
    have hmv := BrownSetting.Move.back (S := S) (a := f a) (toList f s) (toList f r) (f c) hp
    rw [hend] at hmv
    rw [toList_append, toList_append, toList_fwd, toList_bwd]
    exact hmv
  | @backtrackBwd _ c s e r =>
    obtain ⟨hs, hend⟩ := toList_spec S f hedge s
    have hr := (toList_spec S f hedge r).1
    have hp : S.IsPath (f a)
        (toList f s ++ f c :: S.endpoint (f a) (toList f s) :: toList f r) := by
      rw [BrownSetting.isPath_append, hend, isPath_cons, isPath_cons]
      exact ⟨hs, edge_symm S (hedge _ _ e), hedge _ _ e, hr⟩
    have hmv := BrownSetting.Move.back (S := S) (a := f a) (toList f s) (toList f r) (f c) hp
    rw [hend] at hmv
    rw [toList_append, toList_append, toList_bwd, toList_fwd]
    exact hmv
  | @triangle _ b₁ b₂ s t r =>
    obtain ⟨hs, hend⟩ := toList_spec S f hedge s
    have hr := (toList_spec S f hedge r).1
    have hp : S.IsPath (f a) (toList f s ++ f b₁ :: f b₂ :: toList f r) := by
      rw [BrownSetting.isPath_append, hend, isPath_cons, isPath_cons]
      exact ⟨hs, hedge _ _ (X.tri_edge01 t), hedge _ _ (X.tri_edge12 t), hr⟩
    have ht : S.tri (S.endpoint (f a) (toList f s)) (f b₁) (f b₂) := by
      rw [hend]
      exact htri _ _ _ t
    have hmv := BrownSetting.Move.tri (S := S) (a := f a) (toList f s) (toList f r)
      (f b₁) (f b₂) hp ht
    rw [toList_append, toList_append, toList_fwd, toList_fwd, toList_fwd]
    exact hmv

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.move_toList

/-- `toList` sends lane-06 homotopies to lane-12 homotopies. -/
theorem homotopic_toList (S : BrownSetting G V) (f : W → V)
    (hedge : ∀ u w : W, X.edge u w → S.edge (f u) (f w))
    (htri : ∀ u v w : W, X.tri u v w → S.tri (f u) (f v) (f w))
    {a d : W} {p q : X.EdgePath a d} (h : OrderedTwoComplex.EdgePath.Homotopic p q) :
    S.Homotopic (f a) (toList f p) (toList f q) := by
  have h' : Relation.EqvGen OrderedTwoComplex.EdgePath.Move p q := h
  clear h
  induction h' with
  | rel _ _ hm => exact Relation.EqvGen.rel _ _ (move_toList S f hedge htri hm)
  | refl _ => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.homotopic_toList

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge
