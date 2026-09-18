import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.RegionMoveLooseResidual
import GroupApproximation.Meta.AxiomGuard

/-!
# A loose crossing has a second loose crosser

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): the subdiagram `Γ_1` with
`∂Γ_1 = s_1 t_1 s_2 t_2`.  Lane gl-p10-23.

Write `σ` for the rotation and `α` for the reversal.  A passage `p → next p` of the pocket boundary
*crosses* the turn `d₀` when exactly one of `α p` and `next p` lies strictly inside the rotation
sector from `α d₀` to `next d₀`.

## Route

* `regionMoveLooseSide_false_of_unique_crosser`: if the passage `d ≠ d₀` crosses the turn `d₀`,
  some passage other than `d₀` and `d` crosses it too.  This is `regionMoveLoose_false_of_pair`
  with the weaker hypothesis "no other passage crosses" in place of "every other passage is
  tight".  Same proof: `regionMoveLoose_even_crossers` says the crossers are even in number, and
  `d₀` does not cross its own sector.
* `regionMoveLooseSide_exists_second_crosser`: that second crosser `e`, which is loose
  (`regionMoveCoreClose_not_crossed_of_tight`).
* `regionMoveLooseSide_sameCycle_of_crosses`: a crosser of the turn `d₀` has `α e` in the rotation
  orbit of `α d₀`.  One of `α e`, `next e` lies in the sector, and `α e`, `next e` share a vertex
  because the boundary is a closed walk.
* `regionMoveLooseSide_mem_side_of_three`: among three distinct loose passages, one starts in a side
  `s₁` or `s₂`.  Every loose passage starts in a side or at one of the two junctions
  (`regionMoveLoose_tight_or_junction`).

## Truth check

Proved lemmas.  Python model `scratchpad/gl-p10-23/model.py`: at one vertex, all corner-bit patterns
and all walk matchings with at most 10 rotation darts.  It confirms that crossers are even, tight
passages cross nothing, and each loose crossing `(d₀, d)` has a second loose crosser `e`
(12200 loose crossings checked, no failure).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

universe u w v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides
open scoped Classical

section Pocket

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {X : DiscDiagram.{u, w, v} W} {lo hi : ℕ}

/-- **A crossing is never the only crossing**: in a pocket with a closed boundary walk, if the
passage `d` crosses the turn at `d₀`, some passage other than `d₀` and `d` crosses it too. -/
theorem regionMoveLooseSide_false_of_unique_crosser (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) {d₀ d : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hd : d ∈ K.boundary.cycle)
    (hcross : ¬(RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (X.toCombMap.alpha d) ↔
      RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (K.boundary.cycle.next d hd)))
    (hnc : ∀ (e : X.toCombMap.Dart) (he : e ∈ K.boundary.cycle), e ≠ d₀ → e ≠ d →
      (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha e) ↔
        RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (K.boundary.cycle.next e he))) : False := by
  have hxy : X.toCombMap.alpha d₀ ≠ K.boundary.cycle.next d₀ hd₀ := by
    intro h
    apply K.boundary_alpha_not_mem hd₀
    rw [h]
    exact List.next_mem hd₀
  have hv : X.toCombMap.vertexOf (X.toCombMap.alpha d₀) =
      X.toCombMap.vertexOf (K.boundary.cycle.next d₀ hd₀) :=
    OuterPinchIsolated.rel_next_of_isChain K.boundary.cycle_nonempty K.boundary.cycle_nodup
      hK.1 hK.2 hd₀
  have hsc : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀)
      (K.boundary.cycle.next d₀ hd₀) := (X.toCombMap.vertexOf_eq_iff _ _).mp hv
  obtain ⟨k, hk0, hk, hmin⟩ := OuterPinchCorners.exists_firstArrival hsc hxy
  have hP : ∀ z, X.toCombMap.faceOf (X.toCombMap.sigma z) ∈ K.faces ↔
      X.toCombMap.faceOf (X.toCombMap.alpha z) ∈ K.faces := by
    intro z
    rw [← OuterPinchCornerFix.facePerm_alpha, X.toCombMap.faceOf_facePerm]
  have hx : X.toCombMap.faceOf (X.toCombMap.alpha (X.toCombMap.alpha d₀)) ∈ K.faces := by
    rw [X.toCombMap.alpha_involutive d₀]
    exact ((K.boundary.cycle_mem_iff d₀).mp hd₀).1
  have hy : X.toCombMap.faceOf (K.boundary.cycle.next d₀ hd₀) ∈ K.faces :=
    ((K.boundary.cycle_mem_iff _).mp (List.next_mem hd₀)).1
  have hE := regionMoveLoose_even_crossers K.boundary.cycle_nodup
    (fun z => X.toCombMap.faceOf z ∈ K.faces) (fun z => K.boundary.cycle_mem_iff z) hP hk0 hk
    hmin hx hy
  have hq : ∀ b ∈ K.boundary.cycle.attach,
      (decide (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha b.1)) !=
        decide (RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
          (K.boundary.cycle.next d₀ hd₀) (K.boundary.cycle.next b.1 b.2))) = true ↔
        b = ⟨d, hd⟩ := by
    intro b _
    rw [regionMoveLoose_bne_true_iff]
    constructor
    · intro hb
      by_contra hbd
      by_cases hb0 : b.1 = d₀
      · apply hb
        have hxx : ¬RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
            (K.boundary.cycle.next d₀ hd₀) (X.toCombMap.alpha b.1) := by
          rw [hb0]
          exact regionMoveLoose_not_rotationBetween_self hk0 hk hmin
        have hyy : ¬RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
            (K.boundary.cycle.next d₀ hd₀) (K.boundary.cycle.next b.1 b.2) := by
          rw [regionMoveLoose_next_congr hd₀ b.1 b.2 hb0]
          exact regionMoveLoose_not_rotationBetween_end
        exact iff_of_false hxx hyy
      · have hbd' : b.1 ≠ d := fun h => hbd (Subtype.ext h)
        exact hb (hnc b.1 b.2 hb0 hbd')
    · intro hbd
      subst hbd
      exact hcross
  have h1 : K.boundary.cycle.attach.countP (fun b =>
      decide (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha b.1)) !=
        decide (RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
          (K.boundary.cycle.next d₀ hd₀) (K.boundary.cycle.next b.1 b.2))) = 1 :=
    regionMoveLoose_countP_eq_one (List.nodup_attach.mpr K.boundary.cycle_nodup)
      (List.mem_attach K.boundary.cycle ⟨d, hd⟩) _ hq
  rw [h1] at hE
  exact Nat.not_even_one hE

/-- **A crossing has a second, loose crosser**: if the passage `d` crosses the turn at `d₀`, some
passage `e ∉ {d₀, d}` crosses it too, and `e` is not tight. -/
theorem regionMoveLooseSide_exists_second_crosser (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) {d₀ d : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hd : d ∈ K.boundary.cycle)
    (hcross : ¬(RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (X.toCombMap.alpha d) ↔
      RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (K.boundary.cycle.next d hd))) :
    ∃ (e : X.toCombMap.Dart) (he : e ∈ K.boundary.cycle), e ≠ d₀ ∧ e ≠ d ∧
      ¬RegionMoveCoreCloseTight K e he ∧
      ¬(RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha e) ↔
        RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (K.boundary.cycle.next e he)) := by
  have hex : ∃ (e : X.toCombMap.Dart) (he : e ∈ K.boundary.cycle), e ≠ d₀ ∧ e ≠ d ∧
      ¬(RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (X.toCombMap.alpha e) ↔
        RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
          (K.boundary.cycle.next e he)) := by
    by_contra hno
    apply regionMoveLooseSide_false_of_unique_crosser K hK hd₀ hd hcross
    intro e he h0 h1
    by_contra hc
    exact hno ⟨e, he, h0, h1, hc⟩
  obtain ⟨e, he, h0, h1, hc⟩ := hex
  exact ⟨e, he, h0, h1, fun ht => hc (regionMoveCoreClose_not_crossed_of_tight K hd₀ he ht), hc⟩

/-- **A crosser lives at the vertex of the turn**: if the passage `e` crosses the turn at `d₀`,
then `α e` is in the rotation orbit of `α d₀`. -/
theorem regionMoveLooseSide_sameCycle_of_crosses (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) {d₀ e : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (he : e ∈ K.boundary.cycle)
    (hc : ¬(RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (X.toCombMap.alpha e) ↔
      RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
        (K.boundary.cycle.next e he))) :
    X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha e) := by
  have hv : X.toCombMap.vertexOf (X.toCombMap.alpha e) =
      X.toCombMap.vertexOf (K.boundary.cycle.next e he) :=
    OuterPinchIsolated.rel_next_of_isChain K.boundary.cycle_nonempty K.boundary.cycle_nodup
      hK.1 hK.2 he
  have hse : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha e) (K.boundary.cycle.next e he) :=
    (X.toCombMap.vertexOf_eq_iff _ _).mp hv
  have key : ∀ z, RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
      (K.boundary.cycle.next d₀ hd₀) z →
        X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) z := by
    rintro z ⟨a, -, rfl, -⟩
    exact Equiv.Perm.sameCycle_pow_right.mpr (Equiv.Perm.SameCycle.refl _ _)
  by_cases h1 : RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
      (K.boundary.cycle.next d₀ hd₀) (X.toCombMap.alpha e)
  · exact key _ h1
  · have h2 : RotationBetween X.toCombMap (X.toCombMap.alpha d₀)
        (K.boundary.cycle.next d₀ hd₀) (K.boundary.cycle.next e he) := by
      by_contra h2
      exact hc (iff_of_false h1 h2)
    exact (key _ h2).trans hse.symm

/-- **Three loose passages reach a side**: among three distinct passages that are not tight, one
starts in `s₁` or in `s₂`, since the other loose passages start at one of two junctions. -/
theorem regionMoveLooseSide_mem_side_of_three (K : PocketFaceSet D eps X lo hi)
    {a b c : X.toCombMap.Dart} (ha : a ∈ K.boundary.cycle) (hb : b ∈ K.boundary.cycle)
    (hc : c ∈ K.boundary.cycle) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hna : ¬RegionMoveCoreCloseTight K a ha) (hnb : ¬RegionMoveCoreCloseTight K b hb)
    (hnc : ¬RegionMoveCoreCloseTight K c hc) :
    (a ∈ K.firstSide ∨ a ∈ K.secondSide) ∨ (b ∈ K.firstSide ∨ b ∈ K.secondSide) ∨
      (c ∈ K.firstSide ∨ c ∈ K.secondSide) := by
  rcases regionMoveLoose_tight_or_junction K ha with h | h | h | ja
  · exact absurd h hna
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  rcases regionMoveLoose_tight_or_junction K hb with h | h | h | jb
  · exact absurd h hnb
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr h))
  rcases regionMoveLoose_tight_or_junction K hc with h | h | h | jc
  · exact absurd h hnc
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  exfalso
  rcases ja with ⟨_, e₀⟩ | ⟨_, e₀⟩ <;> rcases jb with ⟨_, e₁⟩ | ⟨_, e₁⟩ <;>
    rcases jc with ⟨_, e₂⟩ | ⟨_, e₂⟩ <;>
    first
      | exact hab (e₀.trans e₁.symm)
      | exact hac (e₀.trans e₂.symm)
      | exact hbc (e₁.trans e₂.symm)

/-- **A loose crossing with a second loose crosser at the same vertex, reaching a side**: the data
of `RegionMoveCoreCloseLooseCross` (the turn `d₀`, its loose crosser `d`), together with a second
loose crosser `e ∉ {d₀, d}` of the same turn, with `α e` at the vertex of the turn, and one of
`d₀, d, e` starting in a side `s₁` or `s₂`. -/
def RegionMoveLooseSideCross (K : PocketFaceSet D eps X lo hi) : Prop :=
  ∃ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle) (d : X.toCombMap.Dart)
    (hd : d ∈ K.boundary.cycle) (e : X.toCombMap.Dart) (he : e ∈ K.boundary.cycle),
    P10ChordLift.NonFirstTurn K d₀ hd₀ ∧ ¬RegionMoveCoreCloseTight K d₀ hd₀ ∧ d ≠ d₀ ∧
      ¬RegionMoveCoreCloseTight K d hd ∧
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) ∧
      ¬ (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (K.boundary.cycle.next d hd)) ∧
      e ≠ d₀ ∧ e ≠ d ∧ ¬RegionMoveCoreCloseTight K e he ∧
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha e) ∧
      ¬ (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (X.toCombMap.alpha e) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) (K.boundary.cycle.next d₀ hd₀)
            (K.boundary.cycle.next e he)) ∧
      ((d₀ ∈ K.firstSide ∨ d₀ ∈ K.secondSide) ∨ (d ∈ K.firstSide ∨ d ∈ K.secondSide) ∨
        (e ∈ K.firstSide ∨ e ∈ K.secondSide))

/-- **A loose crossing refines to a side crossing.** -/
theorem regionMoveLooseSide_cross_of_looseCross (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) (h : RegionMoveCoreCloseLooseCross K) : RegionMoveLooseSideCross K := by
  obtain ⟨d₀, hd₀, d, hd, hnf, hnt₀, hne, hnt, hsc, hcross⟩ := h
  obtain ⟨e, he, h0, h1, hnte, hce⟩ :=
    regionMoveLooseSide_exists_second_crosser K hK hd₀ hd hcross
  exact ⟨d₀, hd₀, d, hd, e, he, hnf, hnt₀, hne, hnt, hsc, hcross, h0, h1, hnte,
    regionMoveLooseSide_sameCycle_of_crosses K hK hd₀ he hce, hce,
    regionMoveLooseSide_mem_side_of_three K hd₀ hd he (Ne.symm hne) (Ne.symm h0) (Ne.symm h1)
      hnt₀ hnt hnte⟩

/-- **A side crossing has a third loose passage.** -/
theorem regionMoveLooseSide_three_of_cross (K : PocketFaceSet D eps X lo hi)
    (h : RegionMoveLooseSideCross K) : RegionMoveLooseThree K := by
  obtain ⟨d₀, hd₀, d, hd, e, he, hnf, hnt₀, hne, hnt, hsc, hcross, h0, h1, hnte, -⟩ := h
  exact ⟨d₀, hd₀, d, hd, hnf, hnt₀, hne, hnt, hsc, hcross, e, he, h0, h1, hnte⟩

/-- **A side crossing is a loose crossing.** -/
theorem regionMoveLooseSide_looseCross_of_cross (K : PocketFaceSet D eps X lo hi)
    (h : RegionMoveLooseSideCross K) : RegionMoveCoreCloseLooseCross K := by
  obtain ⟨d₀, hd₀, d, hd, _e, _he, hnf, hnt₀, hne, hnt, hsc, hcross, -⟩ := h
  exact ⟨d₀, hd₀, d, hd, hnf, hnt₀, hne, hnt, hsc, hcross⟩

end Pocket

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_false_of_unique_crosser
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_exists_second_crosser
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_sameCycle_of_crosses
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_mem_side_of_three
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.RegionMoveLooseSideCross
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_cross_of_looseCross
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_three_of_cross
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RegionMove.regionMoveLooseSide_looseCross_of_cross
