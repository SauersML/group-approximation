import GroupApproximation.Analysis.AmenableExtensionAmenableTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# `prop:locally-rf-by-z-trace`: the printed display, identity and case split

`non_mf_groups_exist.tex`, the proof of Proposition `prop:locally-rf-by-z-trace` (tex 1888–1905 at
origin/main 5b3910136).  `Analysis.AmenableExtensionSentences` carries these sentences by their
conclusions.  This module adds the printed steps themselves.

* `manuscriptSentence_translationFormula`: the display `g σ(x) r_q Λ = σ(ḡx) r_{θ(b(g,x))q} Λ`
  for `ḡx ∈ F`, where `r_{θ(b)q}` is the coset `b r_q Λ` of `N₀/Λ`.
* `manuscriptSentence_defectIsBoundaryCompression`: the identity
  `Φ(u_{gh}) − Φ(u_g)Φ(u_h) = Πλ(g)(1−Π)λ(h)Π`, entrywise on `ℓ²(T)`.  The `(p,q)` entry of the
  right-hand side is `1` exactly when `h` moves the `q`-th selected coset out of `T` and `g` moves
  that translate onto the `p`-th selected coset, and `0` otherwise.
* `manuscriptSentence_printedHSDisplay`: the display
  `‖Φ(u_{gh}) − Φ(u_g)Φ(u_h)‖₂² ≤ |{x ∈ F : h̄x ∉ F}| / |F|`.
* `manuscriptSentence_traceIsFixedPointRatio`: the normalized trace of `Φ(u_g)` is the fraction of
  points of `T` fixed by `g`.
* `manuscriptSentence_traceCaseMovesFolnerCoordinate`, `manuscriptSentence_traceCaseFibre`: the two
  printed cases `ḡ ≠ 1` and `ḡ = 1`.
-/

namespace GroupApproximation
namespace AmenableExtensionPrintedSteps

open Filter Matrix Quasidiagonal ResidualFinitePacket
open LocallyRFByIntAmenableTrace LocallyRFByIntSchedule SoficByAmenablePermanence
open AmenableExtensionTrace

noncomputable section

variable {G : Type} [Group G] [Countable G] (N : Subgroup G) [N.Normal]

/-- **Printed display (tex 1888–1892).**

> This map is u.c.p., and for `g ∈ Σ` and `ḡx ∈ F`,
> `g σ(x) r_q Λ = σ(ḡx) r_{θ(b(g,x))q} Λ ∈ T`.

The fibre coordinate `q` is the coset of `w ∈ N₀`, and `r_{θ(b(g,x))q}` is the coset of `b w` with
`b = b(g,x)` read inside `N₀`. -/
theorem manuscriptSentence_translationFormula (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) {g : G} (hg : g ∈ exhaustion G 1 n)
    (x : ↥(folnerSet N hA n)) (w : ↥(cocycleSubgroup N hA n))
    (hin : (QuotientGroup.mk g : G ⧸ N) * (x : G ⧸ N) ∈ folnerSet N hA n) :
    ∃ b : ↥(cocycleSubgroup N hA n), windowEmb N hA n b = esCocycle N g (x : G ⧸ N) ∧
      g • extCoset N hN hA n (x, QuotientGroup.mk w) =
        extCoset N hN hA n (⟨_, hin⟩, QuotientGroup.mk (b * w)) := by
  refine ⟨⟨esCocycleN N g (x : G ⧸ N),
    mem_cocycleSubgroup N hA (esCocycleN_mem_cocycleWindow N hA hg x.2)⟩, rfl, ?_⟩
  rw [extCoset_mk, extCoset_mk]
  show (QuotientGroup.mk (g * (sect N (x : G ⧸ N) * windowEmb N hA n w)) :
      G ⧸ stageH N hN hA n) =
    QuotientGroup.mk (sect N ((QuotientGroup.mk g : G ⧸ N) * (x : G ⧸ N)) *
      windowEmb N hA n (⟨esCocycleN N g (x : G ⧸ N),
        mem_cocycleSubgroup N hA (esCocycleN_mem_cocycleWindow N hA hg x.2)⟩ * w))
  congr 1
  rw [map_mul]
  show g * (sect N (x : G ⧸ N) * windowEmb N hA n w) =
    sect N ((QuotientGroup.mk g : G ⧸ N) * (x : G ⧸ N)) *
      (esCocycle N g (x : G ⧸ N) * windowEmb N hA n w)
  rw [esCocycle]
  group

/-- **Printed identity (tex 1893–1894).**

> So for `g,h ∈ Σ` the identity `Φ(u_{gh})−Φ(u_g)Φ(u_h) = Πλ(g)(1−Π)λ(h)Π`

entrywise on `ℓ²(T)`: the `(p,q)` entry of `Πλ(g)(1−Π)λ(h)Π` is the number of points `r ∉ T`
with `λ(h)` sending the `q`-th selected coset to `r` and `λ(g)` sending `r` to the `p`-th one. -/
theorem manuscriptSentence_defectIsBoundaryCompression (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) (g h : G) (p q : extModel N hN hA n) :
    ((h • extCoset N hN hA n q ∉ Set.range (extCoset N hN hA n) ∧
        extCoset N hN hA n p = (g * h) • extCoset N hN hA n q) →
      (extMap N hN hA n (maximalGroupCStarGenerator G (g * h)) -
          extMap N hN hA n (maximalGroupCStarGenerator G g) *
            extMap N hN hA n (maximalGroupCStarGenerator G h)) p q = 1) ∧
    (¬ (h • extCoset N hN hA n q ∉ Set.range (extCoset N hN hA n) ∧
        extCoset N hN hA n p = (g * h) • extCoset N hN hA n q) →
      (extMap N hN hA n (maximalGroupCStarGenerator G (g * h)) -
          extMap N hN hA n (maximalGroupCStarGenerator G g) *
            extMap N hN hA n (maximalGroupCStarGenerator G h)) p q = 0) := by
  have hdef : (extMap N hN hA n (maximalGroupCStarGenerator G (g * h)) -
        extMap N hN hA n (maximalGroupCStarGenerator G g) *
          extMap N hN hA n (maximalGroupCStarGenerator G h)) p q =
      QuasiRegularCompression.generatorDefect (stageH N hN hA n) (extModel N hN hA n)
        (extCoset N hN hA n) g h p q := rfl
  rw [hdef]
  constructor
  · rintro ⟨hq, hp⟩
    rw [QuasiRegularCompression.generatorDefect_apply_of_mem_escape _ _ g h p q
      ((QuasiRegularCompression.mem_escape _ _ _ h q).mpr hq)]
    exact QuasiRegularCompression.incidence_eq_one _ _ hp
  · intro hnot
    by_cases hq : h • extCoset N hN hA n q ∈ Set.range (extCoset N hN hA n)
    · exact QuasiRegularCompression.generatorDefect_apply_of_not_mem_escape _ _
        (extCoset_injective N hN hA n) g h p q
        (fun hesc => (QuasiRegularCompression.mem_escape _ _ _ h q).mp hesc hq)
    · rw [QuasiRegularCompression.generatorDefect_apply_of_mem_escape _ _ g h p q
        ((QuasiRegularCompression.mem_escape _ _ _ h q).mpr hq)]
      exact QuasiRegularCompression.incidence_eq_zero _ _ (fun hp => hnot ⟨hq, hp⟩)

/-- **Printed display (tex 1894–1900).**

> and the rank of `(1−Π)λ(h)Π`, at most `|{x∈F : h̄x∉F}| |Δ|`, give
> `‖Φ(u_{gh})−Φ(u_g)Φ(u_h)‖₂² ≤ |{x∈F : h̄x∉F}| / |F|`.

The Følner boundary `AmenableActionSofic.boundary F h̄` is the printed `{x ∈ F : h̄x ∉ F}`. -/
theorem manuscriptSentence_printedHSDisplay (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) (g : G) {h : G}
    (hh : h ∈ exhaustion G 1 n) :
    hsNormSq (extModel N hN hA n)
        (extMap N hN hA n (maximalGroupCStarGenerator G (g * h)) -
          extMap N hN hA n (maximalGroupCStarGenerator G g) *
            extMap N hN hA n (maximalGroupCStarGenerator G h)) ≤
      ((AmenableActionSofic.boundary (folnerSet N hA n) (QuotientGroup.mk h)).card : ℝ) /
        ((folnerSet N hA n).card : ℝ) := by
  have hdef : extMap N hN hA n (maximalGroupCStarGenerator G (g * h)) -
        extMap N hN hA n (maximalGroupCStarGenerator G g) *
          extMap N hN hA n (maximalGroupCStarGenerator G h) =
      QuasiRegularCompression.generatorDefect (stageH N hN hA n) (extModel N hN hA n)
        (extCoset N hN hA n) g h := rfl
  rw [hdef]
  have h1 := QuasiRegularCompression.hsNormSq_generatorDefect_le_escape (stageH N hN hA n)
    (extModel N hN hA n) (extCoset_injective N hN hA n) g h
  have h2 := card_escape_le N hN hA n hh
  have hY : (0 : ℝ) < (Fintype.card (extModel N hN hA n) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hF : (0 : ℝ) < ((folnerSet N hA n).card : ℝ) := by
    exact_mod_cast (folnerSet_nonempty N hA n).card_pos
  refine h1.trans ?_
  rw [div_le_div_iff₀ hY hF, card_extModel N hN hA n]
  have h3 := mul_le_mul_of_nonneg_right h2 hF.le
  nlinarith [h3]

/-- **Printed sentence (tex 1901–1902), first clause.**

> The normalized trace of `Φ(u_g)` is the fraction of points of `T` fixed by `g`

The selected cosets are pairwise distinct (`extCoset_injective`), so the fixed coordinates are the
fixed points of `T`. -/
theorem manuscriptSentence_traceIsFixedPointRatio (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) (g : G) :
    normTrace (extModel N hN hA n) (extMap N hN hA n (maximalGroupCStarGenerator G g)) =
        ((QuasiRegularCompression.fixedPoints (stageH N hN hA n) (extModel N hN hA n)
            (extCoset N hN hA n) g).card : ℂ) / (Fintype.card (extModel N hN hA n) : ℂ) ∧
      ∀ z : extModel N hN hA n, z ∈ QuasiRegularCompression.fixedPoints (stageH N hN hA n)
          (extModel N hN hA n) (extCoset N hN hA n) g ↔
        g • extCoset N hN hA n z = extCoset N hN hA n z :=
  ⟨QuasiRegularCompression.normTrace_compressionMap_generator (stageH N hN hA n)
      (extModel N hN hA n) (extCoset N hN hA n) g,
    fun z => QuasiRegularCompression.mem_fixedPoints (stageH N hN hA n) (extModel N hN hA n)
      (extCoset N hN hA n) g z⟩

/-- **Printed sentence (tex 1902–1903), the case `ḡ ≠ 1`.**

> if `ḡ ≠ 1`, then `g` moves the `F`-coordinate of every point -/
theorem manuscriptSentence_traceCaseMovesFolnerCoordinate (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) {g : G}
    (hbar : (QuotientGroup.mk g : G ⧸ N) ≠ 1) (z : extModel N hN hA n) :
    (QuotientGroup.mk g : G ⧸ N) * (z.1 : G ⧸ N) ≠ (z.1 : G ⧸ N) ∧
      g • extCoset N hN hA n z ≠ extCoset N hN hA n z := by
  obtain ⟨x, q⟩ := z
  have hmove : (QuotientGroup.mk g : G ⧸ N) * (x : G ⧸ N) ≠ (x : G ⧸ N) := by
    intro hq
    have hq2 : (QuotientGroup.mk g : G ⧸ N) * (x : G ⧸ N) = 1 * (x : G ⧸ N) := by
      rw [one_mul]
      exact hq
    exact hbar (mul_right_cancel hq2)
  refine ⟨hmove, ?_⟩
  intro hfix
  set w : G := sect N (x : G ⧸ N) * windowEmb N hA n (Quotient.out q) with hw
  have hfix' : (QuotientGroup.mk (g * w) : G ⧸ stageH N hN hA n) = QuotientGroup.mk w := hfix
  have hmemN : (g * w)⁻¹ * w ∈ N :=
    stageH_le N hN hA n ((QuotientGroup.eq (s := stageH N hN hA n)).mp hfix')
  have hmkw : (QuotientGroup.mk w : G ⧸ N) = (x : G ⧸ N) := by
    rw [hw, QuotientGroup.mk_mul, mk_windowEmb, mul_one, mk_sect]
  have hq : (QuotientGroup.mk (g * w) : G ⧸ N) = QuotientGroup.mk w :=
    (QuotientGroup.eq (s := N)).mpr hmemN
  rw [QuotientGroup.mk_mul, hmkw] at hq
  exact hmove hq

/-- **Printed sentence (tex 1903–1905), the case `ḡ = 1`.**

> and if `ḡ = 1`, then `g σ(x) r_q Λ = σ(x) r_{θ(b(g,x))q} Λ` with `b(g,x) = σ(x)⁻¹ g σ(x) ≠ 1`,
> so `θ(b(g,x))q ≠ q`.

Here `b ∈ N₀` is `b(g,x)` read inside `N₀`, the fibre coordinate `q` is the coset of `w`, and
`θ(b(g,x))q` is the coset of `b w`. -/
theorem manuscriptSentence_traceCaseFibre (hN : IsLocallyResiduallyFinite ↥N)
    (hA : Amenability.IsAmenable (G ⧸ N)) (n : ℕ) {g : G} (hg : g ∈ exhaustion G 1 n)
    (hg1 : g ≠ 1) (hbar : (QuotientGroup.mk g : G ⧸ N) = 1)
    (x : ↥(folnerSet N hA n)) (w b : ↥(cocycleSubgroup N hA n))
    (hb : windowEmb N hA n b = esCocycle N g (x : G ⧸ N)) :
    esCocycle N g (x : G ⧸ N) = (sect N (x : G ⧸ N))⁻¹ * g * sect N (x : G ⧸ N) ∧
      g • extCoset N hN hA n (x, QuotientGroup.mk w) =
        extCoset N hN hA n (x, QuotientGroup.mk (b * w)) ∧
      b ≠ 1 ∧
      (QuotientGroup.mk (b * w) : (cocyclePacket N hN hA n).quotientModel) ≠
        QuotientGroup.mk w := by
  have hcoc : esCocycle N g (x : G ⧸ N) =
      (sect N (x : G ⧸ N))⁻¹ * g * sect N (x : G ⧸ N) := by
    rw [esCocycle, hbar, one_mul]
  have hwin : esCocycleN N g (x : G ⧸ N) ∈ cocycleWindow N hA n :=
    esCocycleN_mem_cocycleWindow N hA hg x.2
  have hbeq : b = ⟨esCocycleN N g (x : G ⧸ N), mem_cocycleSubgroup N hA hwin⟩ :=
    windowEmb_injective N hA n hb
  subst hbeq
  have hbne : esCocycleN N g (x : G ⧸ N) ≠ 1 := by
    intro hone
    have h0 : esCocycle N g (x : G ⧸ N) = 1 := congrArg Subtype.val hone
    rw [hcoc] at h0
    have h2 : g = sect N (x : G ⧸ N) *
        ((sect N (x : G ⧸ N))⁻¹ * g * sect N (x : G ⧸ N)) * (sect N (x : G ⧸ N))⁻¹ := by
      group
    rw [h0, mul_one, mul_inv_cancel] at h2
    exact hg1 h2
  refine ⟨hcoc, ?_, fun hone => hbne (congrArg Subtype.val hone), ?_⟩
  · rw [extCoset_mk, extCoset_mk]
    show (QuotientGroup.mk (g * (sect N (x : G ⧸ N) * windowEmb N hA n w)) :
        G ⧸ stageH N hN hA n) =
      QuotientGroup.mk (sect N (x : G ⧸ N) * windowEmb N hA n
        (⟨esCocycleN N g (x : G ⧸ N), mem_cocycleSubgroup N hA hwin⟩ * w))
    congr 1
    rw [map_mul]
    show g * (sect N (x : G ⧸ N) * windowEmb N hA n w) =
      sect N (x : G ⧸ N) * (esCocycle N g (x : G ⧸ N) * windowEmb N hA n w)
    rw [hcoc]
    group
  · intro hfix
    have hmem := (QuotientGroup.eq (s := (cocyclePacket N hN hA n).subgroup)).mp hfix
    have hconj := (cocyclePacket N hN hA n).normal'.conj_mem _ hmem w
    have hrewrite :
        w * ((⟨esCocycleN N g (x : G ⧸ N), mem_cocycleSubgroup N hA hwin⟩ * w)⁻¹ * w) * w⁻¹ =
          (⟨esCocycleN N g (x : G ⧸ N), mem_cocycleSubgroup N hA hwin⟩ :
            ↥(cocycleSubgroup N hA n))⁻¹ := by
      group
    rw [hrewrite] at hconj
    exact (cocyclePacket N hN hA n).avoids _ (mem_cocyclePacketSet N hA hwin hbne)
      ((cocyclePacket N hN hA n).subgroup.inv_mem_iff.mp hconj)

end

end AmenableExtensionPrintedSteps
end GroupApproximation

open GroupApproximation.AmenableExtensionPrintedSteps

#audit_axioms manuscriptSentence_translationFormula
#audit_axioms manuscriptSentence_defectIsBoundaryCompression
#audit_axioms manuscriptSentence_printedHSDisplay
#audit_axioms manuscriptSentence_traceIsFixedPointRatio
#audit_axioms manuscriptSentence_traceCaseMovesFolnerCoordinate
#audit_axioms manuscriptSentence_traceCaseFibre
