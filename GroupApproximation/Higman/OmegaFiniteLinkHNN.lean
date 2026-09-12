import GroupApproximation.Higman.OmegaFiniteLinkGraph
import GroupApproximation.Higman.OmegaTowerStageTwoBritton

/-!
# The finite stage-two HNN extension for Omega

The exact link pairs from `OmegaFiniteLinkGraph` are centralized through their
chosen benign witness.  The second direct-product factor meets the link
trivially, so Britton's lemma embeds the free product of that row factor with
the new stable letter.  This gives an injective rank-three semantic copy and
the required conjugation relation for every block.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

/-- The finitely presented witness base for the exact block-link graph. -/
noncomputable abbrev FatLinkBase (m : ℕ) : Type :=
  (fatBlockLinkWitness m).witness.K

/-- The finite cutter whose centralizer imposes the link relation. -/
noncomputable abbrev fatLinkCutter (m : ℕ) : Subgroup (FatLinkBase m) :=
  (fatBlockLinkWitness m).witness.L

/-- The finite second stage. -/
noncomputable abbrev FatLinkPi (m : ℕ) : Type :=
  CentHNN (fatLinkCutter m)

/-- Embed the semantic direct-product base through its benign witness and
then into the central HNN extension. -/
noncomputable def fatLinkPiBaseEmb (m : ℕ) :
    FatCent3 m × F₃ →* FatLinkPi m :=
  (HNNExtension.of : FatLinkBase m →* FatLinkPi m).comp
    (fatBlockLinkWitness m).witness.emb

theorem fatLinkPiBaseEmb_injective (m : ℕ) :
    Function.Injective (fatLinkPiBaseEmb m) :=
  (of_injective_centHNN (fatLinkCutter m)).comp
    (fatBlockLinkWitness m).witness.emb_injective

/-- The exact link graph meets the second factor trivially.  This is the
graph property needed to embed the new stable letter freely with the row. -/
theorem fatBlockLink_comap_inr_eq_bot (m : ℕ) :
    (fatBlockLink m).comap (MonoidHom.inr (FatCent3 m) F₃) = ⊥ := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨p, hp, hpEq⟩ := hx
    have hfirst : genHom (fatOutside m) (flipAHom p.1) = 1 := by
      exact congrArg Prod.fst hpEq
    have hp1 : p.1 = 1 := by
      apply flipAHom_injective
      apply genHom_injective_generic (fatOutside m)
      simpa using hfirst
    have hpgraph : p ∈ Star.graphSub := (Subgroup.mem_inf.mp hp).1
    obtain ⟨w, hw⟩ := Star.mem_graphSub.mp hpgraph
    have hwone : w = 1 := by
      apply Conj.cbHom_injective
      have := congrArg Prod.fst hw
      rw [Star.graphHom_apply, hp1] at this
      simpa using this
    have hp2 : p.2 = 1 := by
      have := congrArg Prod.snd hw
      rw [Star.graphHom_apply, hwone, map_one] at this
      simpa using this.symm
    have hpx : p.2 = x := congrArg Prod.snd hpEq
    rw [← hpx]
    exact hp2
  · rintro rfl
    exact Subgroup.one_mem _

theorem rowIntoF3_injective : Function.Injective rowIntoF3 := by
  have hcomp : Seq.retract.comp rowIntoF3 = MonoidHom.id Row.F₀ := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    fin_cases i
    · change Seq.retract (rowIntoF3 Row.b) = Row.b
      rw [rowIntoF3_b, Seq.retract_b]
    · change Seq.retract (rowIntoF3 Row.c) = Row.c
      rw [rowIntoF3_c, Seq.retract_c]
  have hleft : Function.LeftInverse Seq.retract rowIntoF3 := by
    intro x
    exact DFunLike.congr_fun hcomp x
  exact hleft.injective

/-- The row factor meets the finite cutting subgroup trivially after passage
through the benign witness. -/
theorem fatLinkCutter_comap_row_eq_bot (m : ℕ) :
    (fatLinkCutter m).comap
        ((fatBlockLinkWitness m).witness.emb.comp
          ((MonoidHom.inr (FatCent3 m) F₃).comp rowIntoF3)) = ⊥ := by
  calc
    _ = ((fatLinkCutter m).comap
          (fatBlockLinkWitness m).witness.emb).comap
            ((MonoidHom.inr (FatCent3 m) F₃).comp rowIntoF3) := by
        rw [Subgroup.comap_comap]
    _ = (fatBlockLink m).comap
          ((MonoidHom.inr (FatCent3 m) F₃).comp rowIntoF3) := by
        rw [(fatBlockLinkWitness m).witness.comap_eq]
    _ = ((fatBlockLink m).comap
          (MonoidHom.inr (FatCent3 m) F₃)).comap rowIntoF3 := by
        rw [Subgroup.comap_comap]
    _ = ⊥ := by
      rw [fatBlockLink_comap_inr_eq_bot]
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_bot]
      constructor
      · intro hx
        apply rowIntoF3_injective
        simpa using hx
      · rintro rfl
        exact map_one rowIntoF3

/-- The row/free-letter construction is a genuine HNN subextension of the
finite link stage. -/
theorem fatRowIsSubextension (m : ℕ) : HNNSubextension.IsSubextension
    (MulEquiv.refl (fatLinkCutter m)) (MulEquiv.refl (⊥ : Subgroup Row.F₀))
    ((fatBlockLinkWitness m).witness.emb.comp
      ((MonoidHom.inr (FatCent3 m) F₃).comp rowIntoF3)) where
  inj := (fatBlockLinkWitness m).witness.emb_injective.comp
    (fun _ _ h => rowIntoF3_injective (congrArg Prod.snd h))
  memA z := by
    have hz : (z : Row.F₀) = 1 := Subgroup.mem_bot.mp z.property
    rw [hz, map_one]
    exact Subgroup.one_mem _
  satA x hx := by
    rw [← Subgroup.mem_comap, fatLinkCutter_comap_row_eq_bot] at hx
    exact hx
  satB x hx := by
    rw [← Subgroup.mem_comap, fatLinkCutter_comap_row_eq_bot] at hx
    exact hx
  compat z hz := by simp

/-- Canonical embedding of the free row HNN into the finite stage. -/
noncomputable def fatRowCanonical (m : ℕ) : RowFreeHNN →* FatLinkPi m :=
  HNNSubextension.canonical (fatRowIsSubextension m)

theorem fatRowCanonical_injective (m : ℕ) :
    Function.Injective (fatRowCanonical m) :=
  HNNSubextension.injective_of_isSubextensionHom (fatRowIsSubextension m)
    (HNNSubextension.isSubextensionHom_canonical (fatRowIsSubextension m))

/-- The injective rank-three semantic copy in the finite stage. -/
noncomputable def fatLinkPiF3Hom (m : ℕ) : F₃ →* FatLinkPi m :=
  (fatRowCanonical m).comp f3ToRowFreeHNN

theorem fatLinkPiF3Hom_injective (m : ℕ) :
    Function.Injective (fatLinkPiF3Hom m) :=
  (fatRowCanonical_injective m).comp f3ToRowFreeHNN_injective

@[simp] theorem fatLinkPiF3Hom_a (m : ℕ) :
    fatLinkPiF3Hom m a = (t : FatLinkPi m) := by
  have hcan := HNNSubextension.isSubextensionHom_canonical
    (fatRowIsSubextension m)
  change fatRowCanonical m (t : RowFreeHNN) = (t : FatLinkPi m)
  exact hcan.map_t

@[simp] theorem fatLinkPiF3Hom_b (m : ℕ) :
    fatLinkPiF3Hom m b =
      fatLinkPiBaseEmb m (1, b) := by
  have hcan := HNNSubextension.isSubextensionHom_canonical
    (fatRowIsSubextension m)
  change fatRowCanonical m (of Row.b) = _
  calc
    _ = of ((fatBlockLinkWitness m).witness.emb (1, rowIntoF3 Row.b)) :=
      hcan.map_of Row.b
    _ = _ := by rw [rowIntoF3_b]; rfl

@[simp] theorem fatLinkPiF3Hom_c (m : ℕ) :
    fatLinkPiF3Hom m c =
      fatLinkPiBaseEmb m (1, c) := by
  have hcan := HNNSubextension.isSubextensionHom_canonical
    (fatRowIsSubextension m)
  change fatRowCanonical m (of Row.c) = _
  calc
    _ = of ((fatBlockLinkWitness m).witness.emb (1, rowIntoF3 Row.c)) :=
      hcan.map_of Row.c
    _ = _ := by rw [rowIntoF3_c]; rfl

/-- The first coordinate's selected block code in the finite stage. -/
noncomputable def fatPiGen (m : ℕ) (beta : E) : FatLinkPi m :=
  fatLinkPiBaseEmb m (fatGenCode m beta, 1)

/-- The row code in the second direct-product coordinate. -/
noncomputable def fatPiRowCode (m : ℕ) (beta : E) : FatLinkPi m :=
  fatLinkPiBaseEmb m (1, bElt beta)

/-- **Finite stage-two relation.**  The benign graph cutter centralizes the
exact pair `(g_beta,b_beta^-1)`, hence conjugation of the new `a` by the two
codes agrees for every block. -/
theorem fat_conj_gen (m : ℕ) (beta : E) (hbeta : beta ∈ blockSet m) :
    (fatPiGen m beta)⁻¹ * fatLinkPiF3Hom m a * fatPiGen m beta =
      (fatPiRowCode m beta)⁻¹ * fatLinkPiF3Hom m a * fatPiRowCode m beta := by
  let w := fatBlockLinkWitness m
  have hp : (fatGenCode m beta, (bElt beta)⁻¹) ∈ fatBlockLink m := by
    apply fat_link_pair_mem
    exact ⟨hbeta, hbeta⟩
  have hL : w.witness.emb (fatGenCode m beta, (bElt beta)⁻¹) ∈ w.witness.L := by
    rw [← Subgroup.mem_comap, w.witness.comap_eq]
    exact hp
  have hc : Commute (t : FatLinkPi m)
      (fatLinkPiBaseEmb m (fatGenCode m beta, (bElt beta)⁻¹)) := by
    exact (commute_t_of_iff (fatLinkCutter m)
      (w.witness.emb (fatGenCode m beta, (bElt beta)⁻¹))).2 hL
  have hsplit : fatLinkPiBaseEmb m (fatGenCode m beta, (bElt beta)⁻¹) =
      fatPiGen m beta * (fatPiRowCode m beta)⁻¹ := by
    rw [fatPiGen, fatPiRowCode, ← map_inv, ← map_mul]
    apply congrArg (fatLinkPiBaseEmb m)
    apply Prod.ext <;> simp
  rw [hsplit] at hc
  have hcentral :
      (fatPiGen m beta * (fatPiRowCode m beta)⁻¹)⁻¹ *
          (t : FatLinkPi m) *
          (fatPiGen m beta * (fatPiRowCode m beta)⁻¹) = t := by
    calc
      _ = (fatPiGen m beta * (fatPiRowCode m beta)⁻¹)⁻¹ *
          ((t : FatLinkPi m) *
            (fatPiGen m beta * (fatPiRowCode m beta)⁻¹)) := by group
      _ = (fatPiGen m beta * (fatPiRowCode m beta)⁻¹)⁻¹ *
          ((fatPiGen m beta * (fatPiRowCode m beta)⁻¹) * t) := by
            rw [hc.eq]
      _ = t := by group
  have ha : fatLinkPiF3Hom m a = (t : FatLinkPi m) := fatLinkPiF3Hom_a m
  rw [ha]
  calc
    (fatPiGen m beta)⁻¹ * (t : FatLinkPi m) * fatPiGen m beta =
        (fatPiRowCode m beta)⁻¹ *
          ((fatPiGen m beta * (fatPiRowCode m beta)⁻¹)⁻¹ *
            (t : FatLinkPi m) *
            (fatPiGen m beta * (fatPiRowCode m beta)⁻¹)) *
          fatPiRowCode m beta := by group
    _ = (fatPiRowCode m beta)⁻¹ * (t : FatLinkPi m) *
          fatPiRowCode m beta := by rw [hcentral]

/-- The finite stage is finitely presented. -/
theorem isFinitelyPresented_fatLinkPi (m : ℕ) :
    Group.IsFinitelyPresented (FatLinkPi m) :=
  isFinitelyPresented_centHNN (fatLinkCutter m)
    (fatBlockLinkWitness m).witness.L_fg

/-- The finite stage remains torsion-free. -/
theorem isPowerTorsionFree_fatLinkPi (m : ℕ) :
    IsPowerTorsionFree (FatLinkPi m) :=
  HNNBritton.isPowerTorsionFree_hnn
    (MulEquiv.refl (fatLinkCutter m)) (fatBlockLinkWitness m).torsionFree

end Omega
end Higman
end GroupApproximation
