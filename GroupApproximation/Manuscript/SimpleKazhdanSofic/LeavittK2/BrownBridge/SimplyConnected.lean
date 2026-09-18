import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.Paths
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective.Injective
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown bridge II: simple connectivity transfers, Brown's map is bijective (lane sk-leavitt-20)

Endpoint (a).  Let `X : OrderedTwoComplex W` (lane 06) and `S : BrownSetting G V` (lane 12),
identified by a vertex bijection `e : W ≃ V` with `X.edge u w ↔ S.edge (e u) (e w)` and
triangles of `X` mapped to triangles of `S`.

Route.
* `exists_ofList`: every lane-12 path `l` from `e a` is `toList e p` of a typed path `p` from
  `a` (walk forwards, using the edge equivalence).
* `simplyConnected_of_twoComplex`: `X.SimplyConnected → S.SimplyConnected`.  A closed list path
  at `a` is `toList e p` for a loop `p` at `e.symm a`; `p` is null-homotopic in `X`, and
  `homotopic_toList` carries the homotopy to lane 12.
* `reflTransGen_of_twoComplex`: `X.Connected` gives `S`-connectivity in `ReflTransGen` form.
* `brownMap_surjective_of_connected`: lane 11's `surjective_of_brownEncodes` applied to
  `S.p`, `S.incl`, `S.T`.
* `brownMap_bijective_of_twoComplex`: lane 12's `brownMap_injective` plus surjectivity.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownInjective

variable {G V W : Type*} [Group G] [MulAction G V] {X : OrderedTwoComplex W}

/-- Every lane-12 list path from `e a` comes from a typed path from `a`. -/
theorem exists_ofList (S : BrownSetting G V) (e : W ≃ V)
    (hedge : ∀ u w : W, S.edge (e u) (e w) → X.edge u w) :
    ∀ (l : List V) (a : W), S.IsPath (e a) l →
      ∃ (b : W) (p : X.EdgePath a b), e b = S.endpoint (e a) l ∧ toList e p = l
  | [], a, _ => ⟨a, .nil a, rfl, rfl⟩
  | v :: l, a, hp => by
    rw [isPath_cons] at hp
    obtain ⟨hv, hl⟩ := hp
    have hv' : X.edge a (e.symm v) := hedge _ _ (by rw [e.apply_symm_apply]; exact hv)
    have hl' : S.IsPath (e (e.symm v)) l := by
      rw [e.apply_symm_apply]
      exact hl
    obtain ⟨b, p, hb, hpl⟩ := exists_ofList S e hedge l (e.symm v) hl'
    refine ⟨b, .fwd hv' p, ?_, ?_⟩
    · rw [endpoint_cons, hb, e.apply_symm_apply]
    · rw [toList_fwd, e.apply_symm_apply, hpl]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.exists_ofList

/-- **Endpoint (a).**  Lane-06 simple connectivity implies lane-12 simple connectivity. -/
theorem simplyConnected_of_twoComplex (S : BrownSetting G V) (e : W ≃ V)
    (hedge : ∀ u w : W, X.edge u w ↔ S.edge (e u) (e w))
    (htri : ∀ u v w : W, X.tri u v w → S.tri (e u) (e v) (e w))
    (hX : X.SimplyConnected) : S.SimplyConnected := by
  intro a l hp hend
  have hp' : S.IsPath (e (e.symm a)) l := by
    rw [e.apply_symm_apply]
    exact hp
  obtain ⟨b, p, hb, hpl⟩ := exists_ofList S e (fun u w => (hedge u w).2) l (e.symm a) hp'
  rw [e.apply_symm_apply, hend] at hb
  have hb' : b = e.symm a := by rw [← hb, e.symm_apply_apply]
  subst hb'
  have hh := homotopic_toList S e (fun u w => (hedge u w).1) htri (hX.2 (e.symm a) p)
  rw [hpl, toList_nil, e.apply_symm_apply] at hh
  exact hh

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.simplyConnected_of_twoComplex

theorem reflTransGen_of_isPath (S : BrownSetting G V) :
    ∀ (l : List V) (a : V), S.IsPath a l →
      Relation.ReflTransGen (fun x y => S.edge x y ∨ S.edge y x) a (S.endpoint a l)
  | [], _, _ => Relation.ReflTransGen.refl
  | v :: l, _, hp => by
    rw [isPath_cons] at hp
    rw [endpoint_cons]
    exact Relation.ReflTransGen.head (Or.inl hp.1) (reflTransGen_of_isPath S l v hp.2)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.reflTransGen_of_isPath

/-- Lane-06 connectivity gives lane-12 connectivity in `ReflTransGen` form. -/
theorem reflTransGen_of_twoComplex (S : BrownSetting G V) (e : W ≃ V)
    (hedge : ∀ u w : W, X.edge u w → S.edge (e u) (e w)) (hX : X.Connected) (a b : V) :
    Relation.ReflTransGen (fun x y => S.edge x y ∨ S.edge y x) a b := by
  obtain ⟨p⟩ := hX (e.symm a) (e.symm b)
  obtain ⟨hp, hend⟩ := toList_spec S e hedge p
  have h := reflTransGen_of_isPath S _ _ hp
  rwa [hend, e.apply_symm_apply, e.apply_symm_apply] at h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.reflTransGen_of_twoComplex

/-- Brown's map is surjective when the complex is connected. -/
theorem brownMap_surjective_of_connected (S : BrownSetting G V)
    (hconn : ∀ u : V, Relation.ReflTransGen (fun x y => S.edge x y ∨ S.edge y x) S.v0 u) :
    Function.Surjective S.brownMap :=
  surjective_of_brownEncodes (φ := S.p) (jOf := fun j : S.J => S.incl j) (t := S.T)
    (edge := S.edge) (v₀ := S.v0) (v₁ := S.v1) S.edge_smul
    (fun j => by
      show S.p (S.incl j) • S.v0 = S.v0
      rw [S.p_incl]
      exact MulAction.mem_stabilizer_iff.mp j.2)
    (fun g hg => ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hg⟩, S.p_incl _⟩)
    S.edge_transitive
    (by
      rw [S.p_T]
      exact S.tau_v0)
    (by
      rw [S.p_T]
      exact S.tau_v1)
    hconn

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.brownMap_surjective_of_connected

/-- Brown's map `Π → G` is bijective for a group acting on a simply connected lane-06 complex
presented as a lane-12 setting. -/
theorem brownMap_bijective_of_twoComplex (S : BrownSetting G V) (e : W ≃ V)
    (hedge : ∀ u w : W, X.edge u w ↔ S.edge (e u) (e w))
    (htri : ∀ u v w : W, X.tri u v w → S.tri (e u) (e v) (e w))
    (hX : X.SimplyConnected) : Function.Bijective S.brownMap :=
  ⟨S.brownMap_injective (simplyConnected_of_twoComplex S e hedge htri hX),
    brownMap_surjective_of_connected S
      (reflTransGen_of_twoComplex S e (fun u w => (hedge u w).1) hX.1 S.v0)⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.brownMap_bijective_of_twoComplex

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge
