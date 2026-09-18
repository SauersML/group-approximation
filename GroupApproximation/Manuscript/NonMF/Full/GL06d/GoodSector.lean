import GroupApproximation.Manuscript.NonMF.Full.GL06d.Refinement
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-rose step: the step at an uncrossed non-first turn with a good sector

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Let `c = K.boundary.cycle` be the boundary
of a pocket `K` in walk order, and `d₀ → e₀ = next d₀` an uncrossed non-first turn.

* `exists_step_of_goodSector`: when the rotation from `e₀` to `x` and from `y` to `alpha d₀` meets
  no edge of `c`, and the corner faces at `x` and `y` are distinct, off the exterior and off the
  relator cells, the section pinch at `x`, `y` lowers the repeated visits
  (`PocketFaceSet.exists_pinchStepSection_of_uncrossedTurn`).  The corner faces lie off `K.faces`
  (`faceOf_alpha_sectorAfter_not_mem`, `faceOf_alpha_before_not_mem`).
* `exists_step_of_refinement`: the same across a rotation refinement `R : X → X'` and a pocket `K'`
  with `K'.boundary.cycle = c.map R.map` and the same repeated visits, with the sectors in `X'`
  passing new darts only (`RefinedGoodSector`).  The turn stays non-first and uncrossed
  (`not_firstTurn_of_refinement`, `huncross_of_refinement`).

## Manuscript status

Infrastructure for `thm:hull` (`non_mf_groups_exist.tex`; Hull's small cancellation theorem,
through Osin's Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.Full.GL06d

universe u w v

open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.Surgery.MapCollapse
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.OuterPinchIsolated
open GroupApproximation.GGT.VanKampen.OuterPinchCorners
open GroupApproximation.GGT.VanKampen.OuterPinchCornerFix
open scoped Classical

/-- The corner before `z` lies on the face of `z`: `face (α (σ⁻¹ z)) = face z`. -/
theorem faceOf_alpha_sigma_symm (M : CombMap.{v}) (z : M.Dart) :
    M.faceOf (M.alpha (M.sigma.symm z)) = M.faceOf z := by
  rw [← M.faceOf_facePerm (M.alpha (M.sigma.symm z)), facePerm_alpha, Equiv.apply_symm_apply]

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lo hi : ℕ}

section Good

variable {X : DiscDiagram.{u, w, v} W}

/-- **A split input from good corners.** -/
theorem exists_input {x y : X.toCombMap.Dart} (hsame : X.toCombMap.sigma.SameCycle x y)
    (hne : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.toCombMap.faceOf (X.toCombMap.alpha y))
    (hxout : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.outerFace)
    (hyout : X.toCombMap.faceOf (X.toCombMap.alpha y) ≠ X.outerFace)
    (hxcell : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha x))
    (hycell : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha y)) :
    ∃ I : PinchSplit.Input X, I.x = x ∧ I.y = y :=
  ⟨⟨x, y, hsame, (PinchSplit.exists_cycles hne).some, hxout, hyout, hxcell, hycell⟩, rfl, rfl⟩

/-- **The corners after `e₀` lie off the face set**, up to the first edge of the cycle. -/
theorem faceOf_alpha_sectorAfter_not_mem (K : PocketFaceSet D eps X lo hi)
    {e₀ : X.toCombMap.Dart} (he₀ : e₀ ∈ K.boundary.cycle) {m : ℕ}
    (hkeepm : ∀ t, 0 < t → t ≤ m →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) e₀)) :
    ∀ t, t ≤ m →
      X.toCombMap.faceOf (X.toCombMap.alpha ((X.toCombMap.sigma ^ t) e₀)) ∉ K.faces := by
  intro t
  induction t with
  | zero =>
    intro _
    rw [pow_zero, Equiv.Perm.one_apply]
    exact ((K.boundary.cycle_mem_iff e₀).mp he₀).2
  | succ t ih =>
    intro ht hmem
    have hprev : X.toCombMap.faceOf ((X.toCombMap.sigma ^ (t + 1)) e₀) ∉ K.faces := by
      rw [pow_succ', Equiv.Perm.mul_apply, ← facePerm_alpha ((X.toCombMap.sigma ^ t) e₀),
        X.toCombMap.faceOf_facePerm]
      exact ih (Nat.le_of_succ_le ht)
    refine hkeepm (t + 1) (Nat.succ_pos t) ht (Or.inr ?_)
    refine (K.boundary.cycle_mem_iff _).mpr ⟨hmem, ?_⟩
    rw [X.toCombMap.alpha_involutive]
    exact hprev

/-- **The faces before `alpha d₀` lie off the face set**, back to the last edge of the cycle. -/
theorem faceOf_sectorBefore_not_mem (K : PocketFaceSet D eps X lo hi)
    {d₀ y : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) {q : ℕ}
    (hq : (X.toCombMap.sigma ^ q) y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) y)) :
    ∀ n, n < q → X.toCombMap.faceOf ((X.toCombMap.sigma ^ (q - n)) y) ∉ K.faces := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [Nat.sub_zero, hq]
    exact ((K.boundary.cycle_mem_iff d₀).mp hd₀).2
  | succ n ih =>
    intro hn hmem
    have hs : q - n = q - (n + 1) + 1 := by omega
    have h := ih (Nat.lt_of_succ_lt hn)
    rw [hs, pow_succ', Equiv.Perm.mul_apply,
      ← facePerm_alpha ((X.toCombMap.sigma ^ (q - (n + 1))) y), X.toCombMap.faceOf_facePerm] at h
    refine hkeepq (q - (n + 1)) (by omega) (by omega) (Or.inl ?_)
    exact (K.boundary.cycle_mem_iff _).mpr ⟨hmem, h⟩

/-- **The corner at `y` lies off the face set.** -/
theorem faceOf_alpha_before_not_mem (K : PocketFaceSet D eps X lo hi)
    {d₀ y : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle) {q : ℕ}
    (hq : (X.toCombMap.sigma ^ q) y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) y)) (hq0 : 0 < q) :
    X.toCombMap.faceOf (X.toCombMap.alpha y) ∉ K.faces := by
  have h := faceOf_sectorBefore_not_mem K hd₀ hq hkeepq (q - 1) (by omega)
  rw [show q - (q - 1) = 1 by omega, pow_one, ← facePerm_alpha y, X.toCombMap.faceOf_facePerm] at h
  exact h

/-- **One step of the section pinch at an uncrossed non-first turn with a good sector.** -/
theorem exists_step_of_goodSector
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hprop : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd)))
    {x y : X.toCombMap.Dart} {m q : ℕ} (hm : (X.toCombMap.sigma ^ m) e₀ = x)
    (hkeepm : ∀ t, 0 < t → t ≤ m →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) e₀))
    (hq0 : 0 < q) (hq : (X.toCombMap.sigma ^ q) y = X.toCombMap.alpha d₀)
    (hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X.toCombMap K.boundary.cycle ((X.toCombMap.sigma ^ t) y))
    (hne : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.toCombMap.faceOf (X.toCombMap.alpha y))
    (hxout : X.toCombMap.faceOf (X.toCombMap.alpha x) ≠ X.outerFace)
    (hyout : X.toCombMap.faceOf (X.toCombMap.alpha y) ≠ X.outerFace)
    (hxcell : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha x))
    (hycell : ∀ C ∈ X.relatorCells, C.face ≠ X.toCombMap.faceOf (X.toCombMap.alpha y)) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
        K'.targetArc.length < (outerDarts X').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  have hc : ∀ d ∈ K.boundary.cycle, X.toCombMap.alpha d ∉ K.boundary.cycle :=
    fun d hd => K.boundary_alpha_not_mem hd
  have he₀ : e₀ ∈ K.boundary.cycle := by
    rw [← hnext₀]
    exact List.next_mem ..
  have hαe : X.toCombMap.alpha d₀ ≠ e₀ := fun h => hc d₀ hd₀ (by rw [h]; exact he₀)
  have hvert : X.toCombMap.vertexOf (X.toCombMap.alpha d₀) = X.toCombMap.vertexOf e₀ := by
    have h := rel_next_of_isChain K.boundary.cycle_nonempty K.boundary.cycle_nodup hK.1 hK.2 hd₀
    rwa [hnext₀] at h
  have hsame : X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) e₀ :=
    (X.toCombMap.vertexOf_eq_iff _ _).mp hvert
  obtain ⟨k₀, -, hk₀, hk₀min⟩ := exists_firstArrival hsame hαe
  obtain ⟨z₀, hz₀, hz₀v, hz₀e, hz₀out⟩ := exists_outside_of_not_firstTurn K.boundary.cycle_nonempty
    K.boundary.cycle_nodup hc hK.1 hK.2 hd₀ hnext₀ huncross hk₀ hk₀min hnot
  have hxy : X.toCombMap.sigma.SameCycle x y :=
    (sameCycle_of_pow_eq hm).symm.trans (hsame.symm.trans (sameCycle_of_pow_eq hq).symm)
  have hxs : X.toCombMap.faceOf (X.toCombMap.alpha x) ∉ K.faces := by
    have h := faceOf_alpha_sectorAfter_not_mem K he₀ hkeepm m le_rfl
    rwa [hm] at h
  have hys := faceOf_alpha_before_not_mem K hd₀ hq hkeepq hq0
  obtain ⟨I, hx, hy⟩ := exists_input hxy hne hxout hyout hxcell hycell
  subst hx hy
  exact PocketFaceSet.exists_pinchStepSection_of_uncrossedTurn hlabel K hK hprop htgt I ⟨hxs, hys⟩
    hd₀ hnext₀ huncross hk₀ hk₀min hm hkeepm hq0 hq hkeepq hz₀ hz₀v hz₀e hz₀out

end Good

/-- **A good sector through a refinement**: from `e e₀` to `x`, and from `y` to `e (α d₀)`, past new
darts only, with corner faces distinct, off the exterior and off the relator cells. -/
def RefinedGoodSector (X X' : DiscDiagram.{u, w, v} W)
    (R : RotationRefinement X.toCombMap X'.toCombMap) (d₀ e₀ : X.toCombMap.Dart) : Prop :=
  ∃ (x y : X'.toCombMap.Dart) (m q : ℕ), (X'.toCombMap.sigma ^ m) (R.map e₀) = x ∧
    (∀ t, 0 < t → t ≤ m → ∀ w, (X'.toCombMap.sigma ^ t) (R.map e₀) ≠ R.map w) ∧ 0 < q ∧
    (X'.toCombMap.sigma ^ q) y = R.map (X.toCombMap.alpha d₀) ∧
    (∀ t, 0 < t → t < q → ∀ w, (X'.toCombMap.sigma ^ t) y ≠ R.map w) ∧
    X'.toCombMap.faceOf (X'.toCombMap.alpha x) ≠ X'.toCombMap.faceOf (X'.toCombMap.alpha y) ∧
    X'.toCombMap.faceOf (X'.toCombMap.alpha x) ≠ X'.outerFace ∧
    X'.toCombMap.faceOf (X'.toCombMap.alpha y) ≠ X'.outerFace ∧
    (∀ C ∈ X'.relatorCells, C.face ≠ X'.toCombMap.faceOf (X'.toCombMap.alpha x)) ∧
    ∀ C ∈ X'.relatorCells, C.face ≠ X'.toCombMap.faceOf (X'.toCombMap.alpha y)

section Transport

variable {X X' : DiscDiagram.{u, w, v} W}
  (K : PocketFaceSet D eps X lo hi) (K' : PocketFaceSet D eps X' lo hi)
  (R : RotationRefinement X.toCombMap X'.toCombMap)

/-- The turn stays non-first across a refinement. -/
theorem not_firstTurn_of_refinement (hcycle : K'.boundary.cycle = K.boundary.cycle.map R.map)
    {d₀ e₀ : X.toCombMap.Dart}
    (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀)) :
    ¬ FirstTurn X'.toCombMap (K'.boundary.cycle.reverse.map X'.toCombMap.alpha)
      (X'.toCombMap.alpha (R.map e₀)) (X'.toCombMap.alpha (R.map d₀)) := by
  intro h
  rw [R.alpha_map, R.alpha_map] at h
  have h₁ : FirstTurn X'.toCombMap (K.boundary.cycle.map R.map)
      (R.map (X.toCombMap.alpha e₀)) (R.map (X.toCombMap.alpha d₀)) :=
    FirstTurn.mono (fun z hz => by
      rw [FirstTurnWalk.walkKeep_reverse_map_alpha, hcycle]
      exact hz) h
  have h₂ := R.firstTurn_of_map h₁
  exact hnot (FirstTurn.mono (fun z hz => by
    rwa [FirstTurnWalk.walkKeep_reverse_map_alpha] at hz) h₂)

/-- The turn stays uncrossed across a refinement. -/
theorem huncross_of_refinement (hcycle : K'.boundary.cycle = K.boundary.cycle.map R.map)
    {d₀ e₀ : X.toCombMap.Dart}
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd))) :
    ∀ d (hd : d ∈ K'.boundary.cycle), d ≠ R.map d₀ →
      X'.toCombMap.sigma.SameCycle (X'.toCombMap.alpha (R.map d₀)) (X'.toCombMap.alpha d) →
        (RotationBetween X'.toCombMap (X'.toCombMap.alpha (R.map d₀)) (R.map e₀)
            (X'.toCombMap.alpha d) ↔
          RotationBetween X'.toCombMap (X'.toCombMap.alpha (R.map d₀)) (R.map e₀)
            (K'.boundary.cycle.next d hd)) := by
  intro d hd hdne hsame
  have hd₁ := hd
  rw [hcycle] at hd₁
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd₁
  rw [R.alpha_map, R.alpha_map, R.sameCycle_map_iff] at hsame
  rw [next_map_of_eq R.injective hcycle K.boundary.cycle_nodup hb hd, R.alpha_map, R.alpha_map,
    R.rotationBetween_map_iff, R.rotationBetween_map_iff]
  exact huncross b hb (fun h => hdne (by rw [h])) hsame

/-- **One step of the section pinch through a rotation refinement with a good refined sector.** -/
theorem exists_step_of_refinement (hE : Nonempty (OEquivalentDiscDiagram X X'))
    (hlabel' : ∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d))
    (hK' : K'.ClosedWalk) (hprop' : K'.sourceArc.length < (cellDarts X' K'.source).length)
    (htgt' : K'.targetArc.length < (outerDarts X').length)
    (hvisits : K'.repeatedVisits = K.repeatedVisits)
    (hcycle : K'.boundary.cycle = K.boundary.cycle.map R.map)
    {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd)))
    (hsector : RefinedGoodSector X X' R d₀ e₀) :
    ∃ (X'' : DiscDiagram.{u, w, v} W) (K'' : PocketFaceSet D eps X'' lo hi),
      Nonempty (OEquivalentDiscDiagram X X'') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X''.label d)) ∧
        K''.ClosedWalk ∧ K''.sourceArc.length < (cellDarts X'' K''.source).length ∧
        K''.targetArc.length < (outerDarts X'').length ∧
        K''.repeatedVisits < K.repeatedVisits := by
  obtain ⟨x, y, m, q, hm, hnewm, hq0, hq, hnewq, hne, hxout, hyout, hxcell, hycell⟩ := hsector
  have hd₀' : R.map d₀ ∈ K'.boundary.cycle := by
    rw [hcycle]
    exact R.mem_map_iff.mpr hd₀
  have hnext' : K'.boundary.cycle.next (R.map d₀) hd₀' = R.map e₀ := by
    rw [next_map_of_eq R.injective hcycle K.boundary.cycle_nodup hd₀ hd₀', hnext₀]
  have hkeepm : ∀ t, 0 < t → t ≤ m →
      ¬ walkKeep X'.toCombMap K'.boundary.cycle ((X'.toCombMap.sigma ^ t) (R.map e₀)) := by
    intro t ht htm
    rw [hcycle]
    exact R.not_walkKeep_map_of_new _ (hnewm t ht htm)
  have hkeepq : ∀ t, 0 < t → t < q →
      ¬ walkKeep X'.toCombMap K'.boundary.cycle ((X'.toCombMap.sigma ^ t) y) := by
    intro t ht htq
    rw [hcycle]
    exact R.not_walkKeep_map_of_new _ (hnewq t ht htq)
  have hq' : (X'.toCombMap.sigma ^ q) y = X'.toCombMap.alpha (R.map d₀) := by
    rw [R.alpha_map]
    exact hq
  obtain ⟨X'', K'', ⟨e₂⟩, hlabel'', hK'', hprop'', htgt'', hlt⟩ :=
    exists_step_of_goodSector hlabel' K' hK' hprop' htgt' hd₀' hnext'
      (not_firstTurn_of_refinement K K' R hcycle hnot) (huncross_of_refinement K K' R hcycle huncross)
      hm hkeepm hq0 hq' hkeepq hne hxout hyout hxcell hycell
  obtain ⟨e₁⟩ := hE
  exact ⟨X'', K'', ⟨OEquivalentDiscDiagram.trans e₁ e₂⟩, hlabel'', hK'', hprop'', htgt'',
    lt_of_lt_of_eq hlt hvisits⟩

end Transport

end GroupApproximation.Full.GL06d

#audit_axioms GroupApproximation.Full.GL06d.faceOf_alpha_sigma_symm
#audit_axioms GroupApproximation.Full.GL06d.exists_input
#audit_axioms GroupApproximation.Full.GL06d.faceOf_alpha_sectorAfter_not_mem
#audit_axioms GroupApproximation.Full.GL06d.faceOf_alpha_before_not_mem
#audit_axioms GroupApproximation.Full.GL06d.exists_step_of_goodSector
#audit_axioms GroupApproximation.Full.GL06d.not_firstTurn_of_refinement
#audit_axioms GroupApproximation.Full.GL06d.huncross_of_refinement
#audit_axioms GroupApproximation.Full.GL06d.exists_step_of_refinement
