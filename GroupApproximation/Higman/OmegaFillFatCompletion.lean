import GroupApproximation.Higman.OmegaFillSlimClosure
import GroupApproximation.Higman.OmegaFatSelectedCutter
import GroupApproximation.Algebra.HNNSubextension

/-!
# The fat completion of the slim tower, from one benign subgroup

`Higman.OmegaFillSlimClosure` reduced Higman's `ωₘ` closure to
`Omega.SlimLinkedBenignTower`: some tower receives the slim tower injectively
and has a benign `W_B`.  This file builds that tower, and it needs exactly one
input --- Mikaelian's Example 3.12,

    `Omega.slimLink m = ⟨g_β b_β⁻¹ : β ∈ ℰ_m⟩ ≤ Cent3 (rowOut m)`  is benign

with a torsion-free witness.  Nothing else is assumed: the first stage does
not have to be replaced, because a benign witness for the *link* already
carries a finitely presented torsion-free group containing the whole slim
first stage.

## The construction

Write `w` for the witness: a finitely presented torsion-free `M = w.K`, an
injection `ι : Σ′ = Cent3 (rowOut m) ↪ M`, and a **finitely generated**
`R = w.L ≤ M` with `R ∩ Σ′ = L` --- Mikaelian's `R`, and his `Σ ∩ R = L`.

* `FillPi w = M ∗_R a`, his `Π = M ∗_R a`.  Finitely presented because `M` is
  and `R` is finitely generated (`Higman.isFinitelyPresented_centHNN`), and
  torsion-free by `HNNBritton.isPowerTorsionFree_hnn`.
* `fillPiCanonical w : Π′ →* Π` is his Lemma 2.4 applied to the identity
  isomorphism: the saturation clauses *are* `R ∩ Σ′ = L`, so
  `HNNSubextension.injective_of_isSubextensionHom` applies verbatim.
* `FillOmega w = Π ∗_ρ r`, the same mapping torus one level up, and Lemma 2.4
  again --- this time the saturation is free, because the associated subgroup
  of the big extension is the image of `F₃`, which already lies in `Π′`.
* `fillTower w` is then the slim tower read inside `Ω`
  (`Omega.Tower.pushforward`), so its three relations are the slim ones and
  its `W_B` is the image of the slim `W_B`.

The benignness of that `W_B` is `Omega.benignTF_W_of_gen`: `Ω` is finitely
presented and torsion-free, and `⟨g_β : β ∈ B ∩ ℰ_m⟩` is the image of
`A_{B ∩ ℰ_m}` under an injective homomorphism out of `F₃`, the four factors
being `Omega.genHom_injective_generic`, the two base embeddings of the
centralizing extensions, and Lemma 2.4 at the top.

So the whole `ωₘ` residue is `∀ m, BenignTF (Omega.slimLink m)`.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

section Fill

variable {m : ℕ} (w : TorsionFreeBenignWitness (slimLink m))

/-! ## 1.  The second fat stage -/

/-- Mikaelian's `Π = M ∗_R a`: the stable letter `a` centralizes the finitely
generated subgroup `R` of the benign witness that cuts out the link. -/
abbrev FillPi : Type := CentHNN w.witness.L

theorem isFinitelyPresented_fillPi : Group.IsFinitelyPresented (FillPi w) :=
  isFinitelyPresented_centHNN w.witness.L w.witness.L_fg

theorem isPowerTorsionFree_fillPi : IsPowerTorsionFree (FillPi w) :=
  HNNBritton.isPowerTorsionFree_hnn (MulEquiv.refl w.witness.L) w.torsionFree

/-- **The second stage is a subextension.**  Both saturation clauses are the
witness equation `R ∩ Σ′ = L`, and the compatibility is trivial because both
associated isomorphisms are the identity. -/
theorem fillIsSubextensionPi : HNNSubextension.IsSubextension
    (MulEquiv.refl w.witness.L) (MulEquiv.refl (slimLink m))
    w.witness.emb where
  inj := w.witness.emb_injective
  memA z := by
    rw [← Subgroup.mem_comap, w.witness.comap_eq]
    exact z.property
  satA z hz := by
    rw [← w.witness.comap_eq]
    exact hz
  satB z hz := by
    rw [← w.witness.comap_eq]
    exact hz
  compat z hz := by simp

/-- The slim second stage inside the fat second stage. -/
noncomputable def fillPiCanonical : SlimPi m →* FillPi w :=
  HNNSubextension.canonical (fillIsSubextensionPi w)

theorem fillPiCanonical_injective : Function.Injective (fillPiCanonical w) :=
  HNNSubextension.injective_of_isSubextensionHom (fillIsSubextensionPi w)
    (HNNSubextension.isSubextensionHom_canonical (fillIsSubextensionPi w))

/-- The copy of `F₃` in the fat second stage. -/
noncomputable def fillPiF3Hom : F₃ →* FillPi w :=
  (fillPiCanonical w).comp (slimPiF3Hom m)

theorem fillPiF3Hom_injective : Function.Injective (fillPiF3Hom w) :=
  (fillPiCanonical_injective w).comp (slimPiF3Hom_injective m)

/-! ## 2.  The third fat stage -/

/-- The `m`-fold shift, transported to the fat second stage. -/
noncomputable def fillShiftEquiv :
    (fillPiF3Hom w).range ≃* (fillPiF3Hom w).range :=
  ((MonoidHom.ofInjective (fillPiF3Hom_injective w)).symm.trans
    ((shiftEquiv : MulAut F₃) ^ m)).trans
      (MonoidHom.ofInjective (fillPiF3Hom_injective w))

theorem fillShiftEquiv_apply (x : F₃) :
    ((fillShiftEquiv w ⟨fillPiF3Hom w x, ⟨x, rfl⟩⟩ :
        (fillPiF3Hom w).range) : FillPi w) =
      fillPiF3Hom w (((shiftEquiv : MulAut F₃) ^ m) x) := by
  have hx : (MonoidHom.ofInjective (fillPiF3Hom_injective w)).symm
      ⟨fillPiF3Hom w x, ⟨x, rfl⟩⟩ = x := by
    apply (MonoidHom.ofInjective (fillPiF3Hom_injective w)).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rfl
  change fillPiF3Hom w (((shiftEquiv : MulAut F₃) ^ m)
      ((MonoidHom.ofInjective (fillPiF3Hom_injective w)).symm
        ⟨fillPiF3Hom w x, ⟨x, rfl⟩⟩)) = _
  rw [hx]

/-- Mikaelian's `Ω = Π ∗_ρ r`. -/
abbrev FillOmega : Type :=
  HNNExtension (FillPi w) (fillPiF3Hom w).range (fillPiF3Hom w).range
    (fillShiftEquiv w)

/-- **The third stage is a subextension too.**  Its associated subgroup is the
image of `F₃`, which lies inside the slim second stage already, so both
saturation clauses reduce to injectivity of the second-stage map. -/
theorem fillIsSubextensionOmega : HNNSubextension.IsSubextension
    (fillShiftEquiv w) (slimShiftRangeEquiv m) (fillPiCanonical w) where
  inj := fillPiCanonical_injective w
  memA z := by
    obtain ⟨x, hx⟩ := z.property
    exact ⟨x, by rw [← hx]; rfl⟩
  satA z hz := by
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    apply fillPiCanonical_injective w
    exact hx
  satB z hz := by
    obtain ⟨x, hx⟩ := hz
    refine ⟨x, ?_⟩
    apply fillPiCanonical_injective w
    exact hx
  compat z hz := by
    obtain ⟨x, hx⟩ := z.property
    have hcoe : (z : SlimPi m) = slimPiF3Hom m x := hx.symm
    have hz' : z = (⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩ : (slimPiF3Hom m).range) :=
      Subtype.ext hcoe
    have hL : fillPiCanonical w
          ((slimShiftRangeEquiv m z : (slimPiF3Hom m).range) : SlimPi m)
        = fillPiF3Hom w (((shiftEquiv : MulAut F₃) ^ m) x) := by
      rw [hz', slimShiftRangeEquiv_apply]
      rfl
    have hsub : (⟨fillPiCanonical w (z : SlimPi m), hz⟩ :
          (fillPiF3Hom w).range) = ⟨fillPiF3Hom w x, ⟨x, rfl⟩⟩ := by
      refine Subtype.ext ?_
      show fillPiCanonical w (z : SlimPi m) = fillPiF3Hom w x
      rw [hcoe]
      rfl
    rw [hL, hsub, fillShiftEquiv_apply]

/-- The slim tower's group inside the fat tower's group. -/
noncomputable def fillOmegaCanonical : SlimOmega m →* FillOmega w :=
  HNNSubextension.canonical (fillIsSubextensionOmega w)

theorem fillOmegaCanonical_injective :
    Function.Injective (fillOmegaCanonical w) :=
  HNNSubextension.injective_of_isSubextensionHom (fillIsSubextensionOmega w)
    (HNNSubextension.isSubextensionHom_canonical (fillIsSubextensionOmega w))

theorem isFinitelyPresented_fillOmega :
    Group.IsFinitelyPresented (FillOmega w) := by
  letI : Group.IsFinitelyPresented (FillPi w) := isFinitelyPresented_fillPi w
  letI : Group.FG F₃ := inferInstance
  letI : Group.FG ↥((fillPiF3Hom w).range) :=
    Group.fg_of_surjective
      (f := (MonoidHom.ofInjective (fillPiF3Hom_injective w)).toMonoidHom)
      (MonoidHom.ofInjective (fillPiF3Hom_injective w)).surjective
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension (fillShiftEquiv w)

theorem isPowerTorsionFree_fillOmega : IsPowerTorsionFree (FillOmega w) :=
  HNNBritton.isPowerTorsionFree_hnn (fillShiftEquiv w)
    (isPowerTorsionFree_fillPi w)

/-! ## 3.  The tower -/

/-- **The fat tower**: the slim tower read inside `Ω`. -/
noncomputable def fillTower : Tower m :=
  (slimTower m).pushforward (fillOmegaCanonical w)
    (fillOmegaCanonical_injective w)

/-- The morphism carrying the slim tower into it. -/
noncomputable def fillTowerHom : TowerHom (slimTower m) (fillTower w) :=
  TowerHom.push (slimTower m) (fillOmegaCanonical w)
    (fillOmegaCanonical_injective w)

@[simp] theorem fillTowerHom_map :
    (fillTowerHom w).map = fillOmegaCanonical w := rfl

/-! ## 4.  `W_B` is benign in it -/

/-- The second copy of the coding, all the way up to `Ω`. -/
noncomputable def fillGenEmb : F₃ →* FillOmega w :=
  (fillOmegaCanonical w).comp
    ((slimOmegaOf m).comp ((slimPiOf m).comp (genHom (rowOut m))))

theorem fillGenEmb_injective : Function.Injective (fillGenEmb w) :=
  ((fillOmegaCanonical_injective w).comp
      ((HNNExtension.of_injective (slimShiftRangeEquiv m)).comp
        (of_injective_centHNN (slimLink m)))).comp
    (genHom_injective_generic (rowOut m))

@[simp] theorem fillTower_gen (β : E) :
    (fillTower w).gen β = fillGenEmb w (aElt β) := rfl

theorem fillGenSub_eq_map (B : Set E) :
    Subgroup.closure ((fillTower w).gen '' (B ∩ blockSet m))
      = (ASub (B ∩ blockSet m)).map (fillGenEmb w) := by
  unfold ASub
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨aElt β, ⟨β, hβ, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
    exact ⟨β, hβ, rfl⟩

/-- **`W_B` is benign in the fat tower.** -/
theorem benignTF_W_fillTower {B : Set E} (hB : BenignTF (ASub B)) :
    BenignTF (W (fillTower w) B) := by
  refine benignTF_W_of_gen (fillTower w) (isFinitelyPresented_fillOmega w)
    (isPowerTorsionFree_fillOmega w) ?_
  letI : Group.IsFinitelyPresented (FillOmega w) := isFinitelyPresented_fillOmega w
  have hinter : BenignTF (ASub (B ∩ blockSet m)) := by
    rw [ASub_inter]
    exact BenignTF.inf hB (benignTF_ASub_blockSet m)
  rw [fillGenSub_eq_map]
  exact BenignTF.mapEmb (isPowerTorsionFree_fillOmega w) hinter (fillGenEmb w)
    (fillGenEmb_injective w)

end Fill

/-! ## 5.  The residue, in its final form -/

/-- **A benign link gives a benign tower receiving the slim one.** -/
theorem slimLinkedBenignTower_of_slimLinkBenign
    (h : ∀ m : ℕ, BenignTF (slimLink m)) : SlimLinkedBenignTower := by
  refine ⟨fun m _ B _ hB => ?_⟩
  obtain ⟨w⟩ := h m
  exact ⟨fillTower w, fillTowerHom w, fillOmegaCanonical_injective w,
    benignTF_W_fillTower w hB⟩

/-- **Higman's `ωₘ` closure, from the slim descent and Example 3.12 alone.**

The two hypotheses are `Omega.slimDescent`, proved in
`Higman.OmegaFillSlimClosureClosed`, and benignness of the link, which is the
only statement of the `ωₘ` lane still owed. -/
theorem omegaInput_of_slimLinkBenign (hd : SlimDescent)
    (h : ∀ m : ℕ, BenignTF (slimLink m)) : OmegaInput :=
  omegaInput_of_slimLinked hd (slimLinkedBenignTower_of_slimLinkBenign h)

end Omega
end Higman
end GroupApproximation
