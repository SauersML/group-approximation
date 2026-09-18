import GroupApproximation.Manuscript.NonMF.Full.GL06d.OuterMonogon
import GroupApproximation.Manuscript.NonMF.Full.GL06.Waist
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-rose step: the outer-pinch step at an uncrossed non-first turn

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b) (`thm:hull`).  Outside the rose
configuration (`¬ Full.GL06f.AllNonFirstTurnsCrossed K`) some non-first turn `d₀ → e₀ = next d₀`
of the boundary cycle `c = K.boundary.cycle` is crossed by no other passage.  Both corners of the
turn become G-digons off the face set, and the split at the turn performs the step (`nonRose`).
This proves `Full.GL06.NonRoseStepStatement` (`nonRoseStep`).

## Proof

1. **The turn.**  `σ e₀ ≠ α d₀` since the turn is not first, and `d₀ ≠ e₀`
   (`ne_next_of_not_firstTurn`): some cycle dart `z₀ ≠ e₀` exists, so if `d₀ = e₀` the cycle
   has two distinct members and `next d₀ ≠ d₀`.
2. **First corner** at `e₀`: `face (α e₀) ∉ K.faces` and (H2) holds (`hone_start`), so
   `cornerDigon_of_hone` gives `R₁ : X → X₁` and a G-digon `g₁ = face₁ (α₁ x₁)`,
   `x₁ = σ₁^m₁ (R₁ e₀)`, whose old darts are among `α e₀` and `σ e₀`.
3. **Second corner** at `z = σ₁⁻¹ (R₁ (α d₀))` (`notMem_faces_second`, `hone_second`):
   `R₂ : X₁ → X₂` and a G-digon `g₂ = face₂ (α₂ y)`, `y = σ₂^m₂ (R₂ z)`, whose old darts are
   among `α₁ z` and `σ₁ z`.
4. **The first digon survives** (`corner_faces_ne`): `g₁ ≠ face₁ (α₁ z)`, so `g₁` stays a G-face.
5. **Sector** for `R₁.comp R₂` (`refinedGoodSector_of_twoDigons`, with `first_newDarts`).
6. **The step**: `exists_step_of_refinement` in `X₂`.

The thresholds are `ε₀ = 0` and `ρ₀ = 2`, so relator words have at least two letters.

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

section Powers

variable (M : CombMap.{v})

/-- Rotation powers add (`thm:hull`). -/
theorem sigma_pow_add_apply (t m : ℕ) (x : M.Dart) :
    (M.sigma ^ (t + m)) x = (M.sigma ^ t) ((M.sigma ^ m) x) := by
  rw [pow_add, Equiv.Perm.mul_apply]

/-- Rotation powers subtract (`thm:hull`). -/
theorem sigma_pow_sub_apply {p m : ℕ} (hmp : m < p) (x : M.Dart) :
    (M.sigma ^ (p - m)) ((M.sigma ^ m) x) = (M.sigma ^ p) x := by
  rw [← sigma_pow_add_apply, Nat.sub_add_cancel hmp.le]

end Powers

/-- **The darts up to the lifted first corner are new** (`thm:hull`). -/
theorem first_newDarts {M M₁ M₂ : CombMap.{v}} (R₁ : RotationRefinement M M₁)
    (R₂ : RotationRefinement M₁ M₂) {e : M.Dart} {p m Kl : ℕ} (hmp : m < p)
    (hpmid : ∀ t, 0 < t → t < p → ∀ w, (M₁.sigma ^ t) (R₁.map e) ≠ R₁.map w)
    (hKpos : 0 < Kl → 0 < m)
    (hKeq : (M₂.sigma ^ Kl) (R₂.map (R₁.map e)) = R₂.map ((M₁.sigma ^ m) (R₁.map e)))
    (hKmid : ∀ b, 0 < b → b < Kl → ∀ w, (M₂.sigma ^ b) (R₂.map (R₁.map e)) = R₂.map w →
      ∃ t, 0 < t ∧ t < m ∧ (M₁.sigma ^ t) (R₁.map e) = w) :
    ∀ t, 0 < t → t ≤ Kl → ∀ w, (M₂.sigma ^ t) ((R₁.comp R₂).map e) ≠ (R₁.comp R₂).map w := by
  intro t ht htK w hw
  have hw' : (M₂.sigma ^ t) (R₂.map (R₁.map e)) = R₂.map (R₁.map w) := hw
  rcases Nat.lt_or_ge t Kl with htlt | htge
  · obtain ⟨s, hs, hsm, hsw⟩ := hKmid t ht htlt (R₁.map w) hw'
    exact hpmid s hs (Nat.lt_trans hsm hmp) w hsw
  · have htK' : t = Kl := Nat.le_antisymm htK htge
    rw [htK'] at hw'
    exact hpmid m (hKpos (by omega)) hmp w (R₂.injective (hKeq.symm.trans hw'))

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lo hi : ℕ}

/-- **The good refined sector from two corner digons** (`thm:hull`). -/
theorem refinedGoodSector_of_twoDigons {X X₁ X₂ : DiscDiagram.{u, w, v} W}
    (R₁ : RotationRefinement X.toCombMap X₁.toCombMap)
    (R₂ : RotationRefinement X₁.toCombMap X₂.toCombMap) {d₀ e₀ : X.toCombMap.Dart}
    {z : X₁.toCombMap.Dart} {p₁ m₁ Kl p₂ m₂ : ℕ} (hmp₁ : m₁ < p₁)
    (hpmid₁ : ∀ t, 0 < t → t < p₁ → ∀ w, (X₁.toCombMap.sigma ^ t) (R₁.map e₀) ≠ R₁.map w)
    (hKpos : 0 < Kl → 0 < m₁)
    (hKeq : (X₂.toCombMap.sigma ^ Kl) (R₂.map (R₁.map e₀)) =
      R₂.map ((X₁.toCombMap.sigma ^ m₁) (R₁.map e₀)))
    (hKmid : ∀ b, 0 < b → b < Kl → ∀ w,
      (X₂.toCombMap.sigma ^ b) (R₂.map (R₁.map e₀)) = R₂.map w →
        ∃ t, 0 < t ∧ t < m₁ ∧ (X₁.toCombMap.sigma ^ t) (R₁.map e₀) = w)
    (hmp₂ : m₂ < p₂) (hz : X₁.toCombMap.sigma z = R₁.map (X.toCombMap.alpha d₀))
    (hpz₂ : (X₂.toCombMap.sigma ^ p₂) (R₂.map z) = R₂.map (X₁.toCombMap.sigma z))
    (hpmid₂ : ∀ t, 0 < t → t < p₂ → ∀ w, (X₂.toCombMap.sigma ^ t) (R₂.map z) ≠ R₂.map w)
    (hG₂ : IsGFaceOf X₂
      (X₂.toCombMap.faceOf (X₂.toCombMap.alpha ((X₂.toCombMap.sigma ^ m₂) (R₂.map z)))))
    (honly₂ : ∀ w, X₂.toCombMap.faceOf (R₂.map w) =
        X₂.toCombMap.faceOf (X₂.toCombMap.alpha ((X₂.toCombMap.sigma ^ m₂) (R₂.map z))) →
      w = X₁.toCombMap.alpha z ∨ w = X₁.toCombMap.sigma z)
    (hGx : IsGFaceOf X₂ (X₂.toCombMap.faceOf
      (R₂.map (X₁.toCombMap.alpha ((X₁.toCombMap.sigma ^ m₁) (R₁.map e₀))))))
    (hne' : X₁.toCombMap.faceOf (X₁.toCombMap.alpha ((X₁.toCombMap.sigma ^ m₁) (R₁.map e₀))) ≠
      X₁.toCombMap.faceOf (X₁.toCombMap.alpha z)) :
    RefinedGoodSector X X₂ (R₁.comp R₂) d₀ e₀ := by
  have hax : X₂.toCombMap.alpha ((X₂.toCombMap.sigma ^ Kl) (R₂.map (R₁.map e₀))) =
      R₂.map (X₁.toCombMap.alpha ((X₁.toCombMap.sigma ^ m₁) (R₁.map e₀))) :=
    (congrArg X₂.toCombMap.alpha hKeq).trans (R₂.alpha_map _)
  have hfx := congrArg X₂.toCombMap.faceOf hax
  unfold RefinedGoodSector
  refine ⟨(X₂.toCombMap.sigma ^ Kl) (R₂.map (R₁.map e₀)),
    (X₂.toCombMap.sigma ^ m₂) (R₂.map z), Kl, p₂ - m₂, rfl,
    first_newDarts R₁ R₂ hmp₁ hpmid₁ hKpos hKeq hKmid, Nat.sub_pos_of_lt hmp₂,
    (sigma_pow_sub_apply _ hmp₂ _).trans (hpz₂.trans (congrArg R₂.map hz)),
    fun t ht htq w hw => hpmid₂ (t + m₂) (by omega) (by omega) (R₁.map w)
      ((sigma_pow_add_apply _ t m₂ _).trans hw),
    fun h => ?_, fun h => hGx.1 (hfx.symm.trans h), hG₂.1,
    fun C hC h => hGx.2 C hC (h.trans hfx), hG₂.2⟩
  rcases honly₂ _ (hfx.symm.trans h) with h1 | h1
  · exact hne' (congrArg X₁.toCombMap.faceOf h1)
  · exact hne' ((congrArg X₁.toCombMap.faceOf h1).trans (faceOf_sigma_eq_alpha _ z))

/-- (H1) at the second corner (`thm:hull`). -/
theorem notMem_faces_second {X X₁ : DiscDiagram.{u, w, v} W} {K : PocketFaceSet D eps X lo hi}
    {K₁ : PocketFaceSet D eps X₁ lo hi} {R₁ : RotationRefinement X.toCombMap X₁.toCombMap}
    (hcyc₁ : K₁.boundary.cycle = K.boundary.cycle.map R₁.map) {d₀ : X.toCombMap.Dart}
    (hd₀ : d₀ ∈ K.boundary.cycle) :
    X₁.toCombMap.faceOf (X₁.toCombMap.alpha
      (X₁.toCombMap.sigma.symm (R₁.map (X.toCombMap.alpha d₀)))) ∉ K₁.faces := by
  have hd₁ : R₁.map d₀ ∈ K₁.boundary.cycle := by
    rw [hcyc₁]
    exact List.mem_map.mpr ⟨d₀, hd₀, rfl⟩
  obtain ⟨-, hout⟩ := (K₁.boundary.cycle_mem_iff _).mp hd₁
  rw [faceOf_alpha_sigma_symm X₁.toCombMap, ← R₁.alpha_map]
  exact hout

/-- **The first digon is not the second corner face** (`thm:hull`). -/
theorem corner_faces_ne {X X₁ : DiscDiagram.{u, w, v} W}
    (R₁ : RotationRefinement X.toCombMap X₁.toCombMap) {d₀ e₀ : X.toCombMap.Dart}
    (hde : d₀ ≠ e₀) (hne : X.toCombMap.sigma e₀ ≠ X.toCombMap.alpha d₀)
    {x₁ : X₁.toCombMap.Dart}
    (honly₁ : ∀ w, X₁.toCombMap.faceOf (R₁.map w) =
        X₁.toCombMap.faceOf (X₁.toCombMap.alpha x₁) →
      w = X.toCombMap.alpha e₀ ∨ w = X.toCombMap.sigma e₀) :
    X₁.toCombMap.faceOf (X₁.toCombMap.alpha x₁) ≠ X₁.toCombMap.faceOf
      (X₁.toCombMap.alpha (X₁.toCombMap.sigma.symm (R₁.map (X.toCombMap.alpha d₀)))) := by
  intro h
  rcases honly₁ (X.toCombMap.alpha d₀)
      ((faceOf_alpha_sigma_symm X₁.toCombMap _).symm.trans h.symm) with h1 | h1
  · exact hde (X.toCombMap.alpha.injective h1)
  · exact hne h1.symm

/-- **An uncrossed non-first turn is not a loop**: `d₀ ≠ next d₀` (`thm:hull`). -/
theorem ne_next_of_not_firstTurn {X : DiscDiagram.{u, w, v} W} (K : PocketFaceSet D eps X lo hi)
    (hK : K.ClosedWalk) {d₀ e₀ : X.toCombMap.Dart} (hd₀ : d₀ ∈ K.boundary.cycle)
    (hnext₀ : K.boundary.cycle.next d₀ hd₀ = e₀)
    (hnot : ¬ FirstTurn X.toCombMap (K.boundary.cycle.reverse.map X.toCombMap.alpha)
      (X.toCombMap.alpha e₀) (X.toCombMap.alpha d₀))
    (huncross : ∀ d (hd : d ∈ K.boundary.cycle), d ≠ d₀ →
      X.toCombMap.sigma.SameCycle (X.toCombMap.alpha d₀) (X.toCombMap.alpha d) →
        (RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (X.toCombMap.alpha d) ↔
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd))) :
    d₀ ≠ e₀ := by
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
  obtain ⟨z₀, hz₀, -, hz₀e, -⟩ := exists_outside_of_not_firstTurn K.boundary.cycle_nonempty
    K.boundary.cycle_nodup hc hK.1 hK.2 hd₀ hnext₀ huncross hk₀ hk₀min hnot
  intro hde
  have h2 : 1 < K.boundary.cycle.length :=
    one_lt_length_of_mem_ne hd₀ hz₀ (fun h => hz₀e (h.symm.trans hde))
  exact next_ne_self_of_two_le K.boundary.cycle_nodup h2 hd₀ (hnext₀.trans hde.symm)

/-- **The step at an uncrossed non-first turn**, through two corner digons (`thm:hull`). -/
theorem exists_step_at_turn {X : DiscDiagram.{u, w, v} W} (hW : ∀ word ∈ W, 1 < word.length)
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
          RotationBetween X.toCombMap (X.toCombMap.alpha d₀) e₀ (K.boundary.cycle.next d hd))) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
        K'.targetArc.length < (outerDarts X').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  have hinv : PocketInvariants K := ⟨hlabel, hK, hprop, htgt⟩
  have hne := sigma_ne_alpha_of_not_firstTurn hnot
  have hde := ne_next_of_not_firstTurn K hK hd₀ hnext₀ hnot huncross
  have he₀ : e₀ ∈ K.boundary.cycle := by
    rw [← hnext₀]
    exact List.next_mem ..
  obtain ⟨-, hs₁⟩ := (K.boundary.cycle_mem_iff e₀).mp he₀
  obtain ⟨X₁, K₁, R₁, ⟨E₁⟩, hinv₁, hvis₁, hcyc₁, p₁, m₁, hmp₁, hpz₁, hpmid₁, hG₁, honly₁, -⟩ :=
    cornerDigon_of_hone X hW K e₀ hinv hs₁ (hone_start K.boundary.cycle_nodup hd₀ hnext₀ hne)
  obtain ⟨X₂, K₂, R₂, ⟨E₂⟩, ⟨hlabel₂, hK₂, hprop₂, htgt₂⟩, hvis₂, hcyc₂, p₂, m₂, hmp₂, hpz₂,
      hpmid₂, hG₂, honly₂, htr₂⟩ :=
    cornerDigon_of_hone X₁ hW K₁ (X₁.toCombMap.sigma.symm (R₁.map (X.toCombMap.alpha d₀))) hinv₁
      (notMem_faces_second hcyc₁ hd₀)
      (hone_second R₁ hcyc₁ K.boundary.cycle_nodup hd₀ hnext₀ hne
        (Nat.lt_of_le_of_lt (Nat.zero_le _) hmp₁) hpz₁ hpmid₁)
  have hne' := corner_faces_ne R₁ hde hne honly₁
  obtain ⟨Kl, -, hKpos, hKeq, hKmid⟩ := R₂.lift_pow (R₁.map e₀) m₁
  exact exists_step_of_refinement K K₂ (R₁.comp R₂) ⟨OEquivalentDiscDiagram.trans E₁ E₂⟩ hlabel₂
    hK₂ hprop₂ htgt₂ (hvis₂.trans hvis₁)
    (hcyc₂.trans ((congrArg (List.map R₂.map) hcyc₁).trans List.map_map)) hd₀ hnext₀ hnot
    huncross
    (refinedGoodSector_of_twoDigons R₁ R₂ hmp₁ hpmid₁ hKpos hKeq hKmid hmp₂
      (Equiv.apply_symm_apply X₁.toCombMap.sigma (R₁.map (X.toCombMap.alpha d₀)))
      hpz₂ hpmid₂ hG₂ honly₂ (htr₂ _ hG₁ hne') hne')

/-- **Outside the rose configuration some non-first turn is uncrossed** (`thm:hull`). -/
theorem exists_uncrossed_of_not_allCrossed {X : DiscDiagram.{u, w, v} W}
    {K : PocketFaceSet D eps X lo hi} (hnotall : ¬ GL06f.AllNonFirstTurnsCrossed K) :
    ∃ (d₀ : X.toCombMap.Dart) (hd₀ : d₀ ∈ K.boundary.cycle),
      GL06f.NonFirstTurn K d₀ hd₀ ∧ ¬ GL06f.TurnCrossed K d₀ hd₀ := by
  by_contra h
  apply hnotall
  intro d₀ hd₀ hnf
  by_contra hnc
  exact h ⟨d₀, hd₀, hnf, hnc⟩

/-- **The outer-pinch step outside the rose configuration**, for relators of length at least two
(`thm:hull`). -/
theorem nonRose {X : DiscDiagram.{u, w, v} W} (hW : ∀ word ∈ W, 1 < word.length)
    (hlabel : ∀ d, (symmetricLabelAlphabet D).IsLetter (X.label d))
    (K : PocketFaceSet D eps X lo hi) (hK : K.ClosedWalk)
    (hprop : K.sourceArc.length < (cellDarts X K.source).length)
    (htgt : K.targetArc.length < (outerDarts X).length)
    (hnotall : ¬ GL06f.AllNonFirstTurnsCrossed K) :
    ∃ (X' : DiscDiagram.{u, w, v} W) (K' : PocketFaceSet D eps X' lo hi),
      Nonempty (OEquivalentDiscDiagram X X') ∧
        (∀ d, (symmetricLabelAlphabet D).IsLetter (X'.label d)) ∧
        K'.ClosedWalk ∧ K'.sourceArc.length < (cellDarts X' K'.source).length ∧
        K'.targetArc.length < (outerDarts X').length ∧
        K'.repeatedVisits < K.repeatedVisits := by
  obtain ⟨d₀, hd₀, hnot, hnc⟩ := exists_uncrossed_of_not_allCrossed hnotall
  refine exists_step_at_turn hW hlabel K hK hprop htgt hd₀ rfl hnot fun d hd hdne hs => ?_
  by_contra hn
  exact hnc ⟨d, hd, hdne, hs, hn⟩

/-- **`Full.GL06.NonRoseStepStatement`** (Osin, §9, proof of Lemma 9.7(b); `thm:hull`).  With
`ε₀ = 0` and `ρ₀ = 2`, Osin's condition makes every relator word longer than one letter, and
`nonRose` performs the step. -/
theorem nonRoseStep : GroupApproximation.Full.GL06.NonRoseStepStatement.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨0, fun _ _ => ⟨2, by omega, fun _ hrho _ hcondition _ _ _ _ hlabel K hK _ hprop htgt _
    hnotall => nonRose (fun word hword => lt_of_lt_of_le Nat.one_lt_two
      (hrho.trans (hcondition.long word hword))) hlabel K hK hprop htgt hnotall⟩⟩

end GroupApproximation.Full.GL06d

#audit_axioms GroupApproximation.Full.GL06d.sigma_pow_add_apply
#audit_axioms GroupApproximation.Full.GL06d.sigma_pow_sub_apply
#audit_axioms GroupApproximation.Full.GL06d.first_newDarts
#audit_axioms GroupApproximation.Full.GL06d.refinedGoodSector_of_twoDigons
#audit_axioms GroupApproximation.Full.GL06d.notMem_faces_second
#audit_axioms GroupApproximation.Full.GL06d.corner_faces_ne
#audit_axioms GroupApproximation.Full.GL06d.ne_next_of_not_firstTurn
#audit_axioms GroupApproximation.Full.GL06d.exists_step_at_turn
#audit_axioms GroupApproximation.Full.GL06d.exists_uncrossed_of_not_allCrossed
#audit_axioms GroupApproximation.Full.GL06d.nonRose
#audit_axioms GroupApproximation.Full.GL06d.nonRoseStep
