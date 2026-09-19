import GroupApproximation.Manuscript.MFRecognition.RecognitionInputs
import GroupApproximation.Manuscript.MFRecognition.FiniteRope
import GroupApproximation.Manuscript.MFRecognition.CentralRopeCore

/-!
# From a concrete rope input to the abstract `RecognitionInputs`

`RecognitionInputs` (the hypothesis bundle of the two branch lemmas) speaks
about the *abstract* objects of `eq:central-rope` and `eq:twisted-rope`:
`CentralRope L0 psi`, `ropeSubgroup`, `TwistedHNN S α`.  `RopeObjects` and
`FiniteRope` build the *concrete* ones from a `RopeInput`: `Γ_e` as
`Higman.Rope.Gamma`, `S_e` as `Higman.Rope.Sub`, `α_e` as `Higman.Rope.tau`,
`R_e` as `Higman.Rope.RopeGroup`, and `R̂_e` with its finite presentation.

This module identifies the two readings and produces the abstract bundle from
a concrete input:

* `Γ_e`, `v`, `i(f)` and `v i(f) v⁻¹` coincide definitionally (the abstract
  `ropeEdge` and the concrete `Le` unfold to the same product subgroup);
* `ropeSubgroup_eq_RopeS`: the abstract and concrete `S_e` are the same
  subgroup, so `α_e` transports along `MulEquiv.subgroupCongr`;
* `π₁` — the map `lem:positive-branch` needs, trivial on `i(F)` and `q₊` on
  `v i(F) v⁻¹` — is built by composing `τ` with the automorphism of `Γ_e`
  that exchanges the two copies of `F` in `S_e` (invert the stable letter,
  then conjugate by it);
* `twistedEquiv`: the abstract `TwistedHNN S_e α_e` and the concrete `R_e` are
  isomorphic HNN extensions of the same base, by the two universal maps;
* `recognitionInputsOfRope`: the bundle, with `R̂_e = FiniteRope inp`.

The switch data (`H`, `C_e`, the two embeddings, the `INF` identification
`Q_e = Q₊`) are parameters here and are supplied in `RecognitionAssembly`.
-/

namespace GroupApproximation

/-! ## The swap automorphism of a central HNN extension -/

namespace Higman

open HNNExtension

variable {K : Type} [Group K] (L : Subgroup K)

/-- The endomorphism of `CentHNN L` fixing `K` and inverting the stable
letter.  It is well defined because `t⁻¹` centralizes `L` as `t` does. -/
noncomputable def swapT : CentHNN L →* CentHNN L :=
  HNNExtension.lift (HNNExtension.of) ((HNNExtension.t : CentHNN L)⁻¹) (fun a => by
    have h := conj_eq_self_of_mem L a.2
    show (HNNExtension.t : CentHNN L)⁻¹ * HNNExtension.of (a : K)
      = HNNExtension.of (((MulEquiv.refl L) a : L) : K) * (HNNExtension.t : CentHNN L)⁻¹
    rw [MulEquiv.refl_apply]
    calc (HNNExtension.t : CentHNN L)⁻¹ * HNNExtension.of (a : K)
        = ((HNNExtension.t : CentHNN L)⁻¹ * HNNExtension.of (a : K) * HNNExtension.t)
            * (HNNExtension.t : CentHNN L)⁻¹ := by group
      _ = HNNExtension.of (a : K) * (HNNExtension.t : CentHNN L)⁻¹ := by rw [h])

@[simp] theorem swapT_of (x : K) : swapT L (HNNExtension.of x) = HNNExtension.of x :=
  HNNExtension.lift_of _ _ _ _

@[simp] theorem swapT_t : swapT L (HNNExtension.t : CentHNN L) = (HNNExtension.t : CentHNN L)⁻¹ :=
  HNNExtension.lift_t _ _ _

/-- Invert the stable letter, then conjugate by it: this exchanges the image
of `K` with its conjugate `t⁻¹ K t`. -/
noncomputable def swapConj : CentHNN L →* CentHNN L :=
  (conjT L).toMonoidHom.comp (swapT L)

theorem swapConj_of (x : K) :
    swapConj L (HNNExtension.of x)
      = (HNNExtension.t : CentHNN L)⁻¹ * HNNExtension.of x * HNNExtension.t := by
  simp only [swapConj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, swapT_of,
    conjT_apply, inv_inv]

theorem swapConj_conj (x : K) :
    swapConj L ((HNNExtension.t : CentHNN L)⁻¹ * HNNExtension.of x * HNNExtension.t)
      = HNNExtension.of x := by
  simp only [swapConj, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
    swapT_of, swapT_t, conjT_apply, inv_inv]
  group

/-- The swap preserves the subgroup `⟨Z, t⁻¹ Z t⟩`. -/
theorem swapConj_mem_closure_genSet (Z : Subgroup K) {y : CentHNN L}
    (hy : y ∈ Subgroup.closure (Pinch.genSet L Z Z)) :
    swapConj L y ∈ Subgroup.closure (Pinch.genSet L Z Z) := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨k, hk, rfl⟩ | ⟨y', ⟨k, hk, rfl⟩, rfl⟩
      · rw [swapConj_of]
        refine Subgroup.subset_closure (Or.inr ⟨HNNExtension.of k, ⟨k, hk, rfl⟩, ?_⟩)
        simp [conjT_apply]
      · have hx : (conjT L).toMonoidHom (HNNExtension.of k)
            = (HNNExtension.t : CentHNN L)⁻¹ * HNNExtension.of k * HNNExtension.t := by
          simp [conjT_apply]
        rw [hx, swapConj_conj]
        exact Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩)
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

/-- The swap, restricted to `⟨Z, t⁻¹ Z t⟩`. -/
noncomputable def swapConjSub (Z : Subgroup K) :
    ↥(Subgroup.closure (Pinch.genSet L Z Z)) →*
      ↥(Subgroup.closure (Pinch.genSet L Z Z)) :=
  ((swapConj L).comp (Subgroup.closure (Pinch.genSet L Z Z)).subtype).codRestrict _
    (fun s => swapConj_mem_closure_genSet L Z s.2)

theorem coe_swapConjSub (Z : Subgroup K) (s : ↥(Subgroup.closure (Pinch.genSet L Z Z))) :
    ((swapConjSub L Z s : ↥(Subgroup.closure (Pinch.genSet L Z Z))) : CentHNN L)
      = swapConj L (s : CentHNN L) := rfl

end Higman

/-! ## `π₁` on the rope subgroup -/

namespace Higman
namespace Rope

open HNNExtension

variable {F : Type} [Group F] {N : Subgroup F} [N.Normal] (w : BenignWitness N)

/-- The swap, restricted to `S = ⟨A, Aᵗ⟩`. -/
noncomputable def subSwap : ↥(Sub w) →* ↥(Sub w) := swapConjSub w.L (Aemb w)

omit [N.Normal] in
theorem subSwap_gammaOf (x : F) :
    subSwap w ⟨gammaOf w x, gammaOf_mem_sub w x⟩
      = ⟨gammaConj w x, gammaConj_mem_sub w x⟩ := by
  apply Subtype.ext
  show swapConj w.L (gammaOf w x) = gammaConj w x
  rw [gammaOf, swapConj_of]
  rfl

omit [N.Normal] in
theorem subSwap_gammaConj (x : F) :
    subSwap w ⟨gammaConj w x, gammaConj_mem_sub w x⟩
      = ⟨gammaOf w x, gammaOf_mem_sub w x⟩ := by
  apply Subtype.ext
  show swapConj w.L (gammaConj w x) = gammaOf w x
  rw [gammaConj, swapConj_conj]
  rfl

/-- **The map `π₁` of `lem:positive-branch`**: trivial on the first copy of
`F` in `S`, the quotient map `q₊` on the second.  It is `τ`, precomposed with
the swap of the two copies and followed by `F ⧸ N → Q₊`. -/
noncomputable def piOne {Qplus : Type} [Group Qplus] (qplus : F →* Qplus)
    (hN : N ≤ qplus.ker) : ↥(Sub w) →* Qplus :=
  ((QuotientGroup.lift N qplus hN).comp (tau w)).comp (subSwap w)

theorem piOne_gammaOf {Qplus : Type} [Group Qplus] (qplus : F →* Qplus)
    (hN : N ≤ qplus.ker) (x : F) :
    piOne w qplus hN ⟨gammaOf w x, gammaOf_mem_sub w x⟩ = 1 := by
  simp only [piOne, MonoidHom.comp_apply, subSwap_gammaOf, tau_gammaConj, map_one]

theorem piOne_gammaConj {Qplus : Type} [Group Qplus] (qplus : F →* Qplus)
    (hN : N ≤ qplus.ker) (x : F) :
    piOne w qplus hN ⟨gammaConj w x, gammaConj_mem_sub w x⟩ = qplus x := by
  simp only [piOne, MonoidHom.comp_apply, subSwap_gammaConj, tau_gammaOf]
  rfl

end Rope
end Higman

/-! ## The abstract bundle from a concrete rope input -/

namespace Manuscript
namespace MFRecognition
namespace Rope
namespace RopeInput

open Higman HNNExtension

variable (inp : RopeInput)

noncomputable section

/-- The abstract `S_e` of `RecognitionInputs`, at this input. -/
abbrev SAbs : Subgroup (Recognition.CentralRope (L0 inp) (jq inp)) :=
  Recognition.ropeSubgroup (L0 inp) (jq inp) (i0 inp)

/-- The abstract `v i(f) v⁻¹` is the concrete one. -/
theorem ropeGenConj_eq_gammaConj (f : Fxyt) :
    Recognition.ropeGenConj (L0 inp) (jq inp) (i0 inp) f
      = Higman.Rope.gammaConj (witness inp) f :=
  vConjHom_eq_gammaConj inp f

/-- **The abstract and the concrete `S_e` are the same subgroup of `Γ_e`.** -/
theorem ropeSubgroup_eq_RopeS : SAbs inp = RopeS inp := by
  show Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext y
  constructor
  · rintro (⟨f, rfl⟩ | ⟨f, rfl⟩)
    · exact Or.inl ⟨(witness inp).emb f, ⟨f, Subgroup.mem_top f, rfl⟩, rfl⟩
    · refine Or.inr ⟨HNNExtension.of ((witness inp).emb f),
        ⟨(witness inp).emb f, ⟨f, Subgroup.mem_top f, rfl⟩, rfl⟩, ?_⟩
      show (conjT (witness inp).L) (HNNExtension.of ((witness inp).emb f))
        = Recognition.ropeGenConj (L0 inp) (jq inp) (i0 inp) f
      rw [Higman.Rope.conjT_of_emb]
      exact (ropeGenConj_eq_gammaConj inp f).symm
  · rintro (⟨k, ⟨f, _, rfl⟩, rfl⟩ | ⟨y', ⟨k, ⟨f, _, rfl⟩, rfl⟩, rfl⟩)
    · exact Or.inl ⟨f, rfl⟩
    · refine Or.inr ⟨f, ?_⟩
      show Recognition.ropeGenConj (L0 inp) (jq inp) (i0 inp) f
        = (conjT (witness inp).L) (HNNExtension.of ((witness inp).emb f))
      rw [Higman.Rope.conjT_of_emb]
      exact ropeGenConj_eq_gammaConj inp f

/-- The identification of the two readings of `S_e`. -/
def sCongr : ↥(SAbs inp) ≃* ↥(RopeS inp) :=
  MulEquiv.subgroupCongr (ropeSubgroup_eq_RopeS inp)

theorem sCongr_ropeGenS (f : Fxyt) :
    sCongr inp (Recognition.ropeGenS (L0 inp) (jq inp) (i0 inp) f)
      = ⟨iGammaHom inp f, iGammaHom_mem_RopeS inp f⟩ :=
  Subtype.ext rfl

theorem sCongr_ropeGenConjS (f : Fxyt) :
    sCongr inp (Recognition.ropeGenConjS (L0 inp) (jq inp) (i0 inp) f)
      = ⟨Higman.Rope.gammaConj (witness inp) f, Higman.Rope.gammaConj_mem_sub (witness inp) f⟩ :=
  Subtype.ext (vConjHom_eq_gammaConj inp f)

/-- `α_e`, read on the abstract `S_e`. -/
def alphaAbs : ↥(SAbs inp) →* Qe inp :=
  (alpha inp).comp (sCongr inp).toMonoidHom

theorem alphaAbs_gen (f : Fxyt) :
    alphaAbs inp (Recognition.ropeGenS (L0 inp) (jq inp) (i0 inp) f) = qe inp f := by
  rw [alphaAbs, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sCongr_ropeGenS]
  exact alpha_iGamma inp f

theorem alphaAbs_genConj (f : Fxyt) :
    alphaAbs inp (Recognition.ropeGenConjS (L0 inp) (jq inp) (i0 inp) f) = 1 := by
  rw [alphaAbs, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sCongr_ropeGenConjS]
  exact Higman.Rope.tau_gammaConj (witness inp) f

/-- `π₁`, read on the abstract `S_e`. -/
def piOneAbs : ↥(SAbs inp) →* inp.Qplus :=
  (Higman.Rope.piOne (witness inp) inp.qplus inp.N_le_Nplus).comp (sCongr inp).toMonoidHom

theorem piOneAbs_gen (f : Fxyt) :
    piOneAbs inp (Recognition.ropeGenS (L0 inp) (jq inp) (i0 inp) f) = 1 := by
  rw [piOneAbs, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sCongr_ropeGenS]
  exact Higman.Rope.piOne_gammaOf (witness inp) inp.qplus inp.N_le_Nplus f

theorem piOneAbs_genConj (f : Fxyt) :
    piOneAbs inp (Recognition.ropeGenConjS (L0 inp) (jq inp) (i0 inp) f) = inp.qplus f := by
  rw [piOneAbs, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, sCongr_ropeGenConjS]
  exact Higman.Rope.piOne_gammaConj (witness inp) inp.qplus inp.N_le_Nplus f

/-! ### The two readings of `R_e` -/

/-- The abstract `R_e` of `RecognitionInputs`, at this input. -/
abbrev TwistedAbs : Type := Recognition.TwistedHNN (SAbs inp) (alphaAbs inp)

theorem edgeMulEquiv_rangeRestrict (s : ↥(SAbs inp)) :
    ((Recognition.edgeMulEquiv (SAbs inp) (alphaAbs inp)
        ((Recognition.edgeSource (SAbs inp) (Qe inp)).rangeRestrict s) :
          ↥(Recognition.edgeSubgroupTarget (SAbs inp) (alphaAbs inp))) :
        Recognition.CentralRope (L0 inp) (jq inp) × Qe inp)
      = ((s : Recognition.CentralRope (L0 inp) (jq inp)), alphaAbs inp s) :=
  congrArg Subtype.val
    (OneSidedMFRadical.TensorSynchronizationCore.rangeMulEquivOfKerEq_rangeRestrict
      (Recognition.edgeSource (SAbs inp) (Qe inp))
      (Recognition.edgeTarget (SAbs inp) (alphaAbs inp))
      (Recognition.edgeSource_ker_eq_edgeTarget_ker (SAbs inp) (alphaAbs inp)) s)

/-- The two readings of the base group `Γ_e × Q_e` are the same group; this
identification carries the definitional equality as a typed map so that the
two universal maps below have clean types. -/
def baseEquiv :
    Recognition.CentralRope (L0 inp) (jq inp) × Qe inp ≃* Higman.Rope.Amb (witness inp) :=
  MulEquiv.refl _

@[simp] theorem baseEquiv_apply (x : Recognition.CentralRope (L0 inp) (jq inp) × Qe inp) :
    baseEquiv inp x = x := rfl

@[simp] theorem baseEquiv_symm_apply (x : Higman.Rope.Amb (witness inp)) :
    (baseEquiv inp).symm x = x := rfl

/-- The base inclusion of the concrete `R_e`, read on the abstract base. -/
def fRope : Recognition.CentralRope (L0 inp) (jq inp) × Qe inp →* TwistedRope inp :=
  (HNNExtension.of : Higman.Rope.Amb (witness inp) →* TwistedRope inp).comp
    (baseEquiv inp).toMonoidHom

/-- The base inclusion of the abstract `R_e`, read on the concrete base. -/
def gAbs : Higman.Rope.Amb (witness inp) →* TwistedAbs inp :=
  (HNNExtension.of : Recognition.CentralRope (L0 inp) (jq inp) × Qe inp →* TwistedAbs inp).comp
    (baseEquiv inp).symm.toMonoidHom

theorem fRope_apply (x : Recognition.CentralRope (L0 inp) (jq inp) × Qe inp) :
    fRope inp x = (HNNExtension.of : Higman.Rope.Amb (witness inp) →* TwistedRope inp) x := rfl

theorem gAbs_apply (x : Higman.Rope.Amb (witness inp)) :
    gAbs inp x
      = (HNNExtension.of : Recognition.CentralRope (L0 inp) (jq inp) × Qe inp →* TwistedAbs inp) x :=
  rfl

/-- The defining relation of the concrete `R_e`, read on the abstract `S_e`. -/
theorem twistedRope_conj_abs (s : ↥(SAbs inp)) :
    fRope inp ((s : Recognition.CentralRope (L0 inp) (jq inp)), alphaAbs inp s)
      = (HNNExtension.t : TwistedRope inp)
          * fRope inp ((s : Recognition.CentralRope (L0 inp) (jq inp)), (1 : Qe inp))
          * (HNNExtension.t : TwistedRope inp)⁻¹ :=
  twistedRope_conj inp (sCongr inp s)

/-- The lifting condition for the map from the abstract to the concrete `R_e`. -/
theorem twistedToRope_cond (a : ↥(Recognition.edgeSubgroupSource (SAbs inp) (Qe inp))) :
    (HNNExtension.t : TwistedRope inp) * fRope inp (a : _)
      = fRope inp ((Recognition.edgeMulEquiv (SAbs inp) (alphaAbs inp) a : _) : _)
          * (HNNExtension.t : TwistedRope inp) := by
  obtain ⟨s, hs⟩ := a.2
  have ha : a = (Recognition.edgeSource (SAbs inp) (Qe inp)).rangeRestrict s :=
    Subtype.ext hs.symm
  subst ha
  have h2 := congrArg (fRope inp) (edgeMulEquiv_rangeRestrict inp s)
  rw [h2, twistedRope_conj_abs, inv_mul_cancel_right]
  rfl

/-- The universal map from the abstract to the concrete `R_e`. -/
def twistedToRope : TwistedAbs inp →* TwistedRope inp :=
  HNNExtension.lift (fRope inp) (HNNExtension.t : TwistedRope inp) (twistedToRope_cond inp)

theorem twistedToRope_of (x : Recognition.CentralRope (L0 inp) (jq inp) × Qe inp) :
    twistedToRope inp (HNNExtension.of x) = fRope inp x :=
  HNNExtension.lift_of _ _ _ _

theorem twistedToRope_t :
    twistedToRope inp (HNNExtension.t : TwistedAbs inp) = (HNNExtension.t : TwistedRope inp) :=
  HNNExtension.lift_t _ _ _

/-- The defining relation of the abstract `R_e`, read on the concrete `S_e`. -/
theorem twistedAbs_conj (s : Higman.Rope.Gamma (witness inp)) (hs : s ∈ RopeS inp) :
    (HNNExtension.t : TwistedAbs inp) * gAbs inp ((s, (1 : Qe inp)) : Higman.Rope.Amb (witness inp))
      = gAbs inp ((s, alphaAbs inp ((sCongr inp).symm ⟨s, hs⟩)) : Higman.Rope.Amb (witness inp))
          * (HNNExtension.t : TwistedAbs inp) := by
  have hconj := HNNExtension.t_mul_of
    (φ := Recognition.edgeMulEquiv (SAbs inp) (alphaAbs inp))
    ((Recognition.edgeSource (SAbs inp) (Qe inp)).rangeRestrict
      ((sCongr inp).symm ⟨s, hs⟩))
  rw [edgeMulEquiv_rangeRestrict] at hconj
  exact hconj

/-- The lifting condition for the map from the concrete to the abstract `R_e`. -/
theorem ropeToTwisted_cond (a : ↥(Higman.Rope.AeSub (witness inp))) :
    (HNNExtension.t : TwistedAbs inp) * gAbs inp (a : _)
      = gAbs inp ((Higman.Rope.psi (witness inp) a : _) : _) * (HNNExtension.t : TwistedAbs inp) := by
  obtain ⟨s, hs, hsa⟩ := a.2
  have ha : a = ⟨((s, (1 : Qe inp)) : Higman.Rope.Amb (witness inp)),
      Higman.Rope.pair_mem_ae (witness inp) s hs⟩ := Subtype.ext hsa.symm
  subst ha
  have h2 := congrArg (gAbs inp) (Higman.Rope.coe_psi (witness inp) s hs)
  rw [h2]
  exact twistedAbs_conj inp s hs

/-- The universal map from the concrete to the abstract `R_e`. -/
def ropeToTwisted : TwistedRope inp →* TwistedAbs inp :=
  HNNExtension.lift (gAbs inp) (HNNExtension.t : TwistedAbs inp) (ropeToTwisted_cond inp)

theorem ropeToTwisted_of (x : Higman.Rope.Amb (witness inp)) :
    ropeToTwisted inp (HNNExtension.of x) = gAbs inp x :=
  HNNExtension.lift_of _ _ _ _

theorem ropeToTwisted_t :
    ropeToTwisted inp (HNNExtension.t : TwistedRope inp) = (HNNExtension.t : TwistedAbs inp) :=
  HNNExtension.lift_t _ _ _

theorem ropeToTwisted_comp_twistedToRope :
    (ropeToTwisted inp).comp (twistedToRope inp) = MonoidHom.id (TwistedAbs inp) := by
  apply HNNExtension.hom_ext
  · ext x
    show ropeToTwisted inp (twistedToRope inp (HNNExtension.of x)) = HNNExtension.of x
    rw [twistedToRope_of, fRope_apply, ropeToTwisted_of, gAbs_apply]
  · show ropeToTwisted inp (twistedToRope inp HNNExtension.t) = HNNExtension.t
    rw [twistedToRope_t, ropeToTwisted_t]

theorem twistedToRope_comp_ropeToTwisted :
    (twistedToRope inp).comp (ropeToTwisted inp) = MonoidHom.id (TwistedRope inp) := by
  apply HNNExtension.hom_ext
  · ext x
    show twistedToRope inp (ropeToTwisted inp (HNNExtension.of x)) = HNNExtension.of x
    rw [ropeToTwisted_of, gAbs_apply, twistedToRope_of, fRope_apply]
  · show twistedToRope inp (ropeToTwisted inp HNNExtension.t) = HNNExtension.t
    rw [ropeToTwisted_t, twistedToRope_t]

/-- **The abstract and the concrete `R_e` are isomorphic**, by the two
universal maps. -/
def twistedEquiv : TwistedAbs inp ≃* TwistedRope inp :=
  MonoidHom.toMulEquiv (twistedToRope inp) (ropeToTwisted inp)
    (ropeToTwisted_comp_twistedToRope inp) (twistedToRope_comp_ropeToTwisted inp)

/-- The abstract `R_e` is isomorphic to the finitely presented `R̂_e`. -/
def twistedEquivFiniteRope : TwistedAbs inp ≃* FiniteRope inp :=
  (twistedEquiv inp).trans (finiteRopeEquiv inp).symm

/-! ### The bundle -/

/-- **The abstract bundle of the two branch lemmas, from a concrete rope
input and the switch data.**  Every rope-side field is supplied by the
identifications above; the switch-side fields (`H`, `C_e`, the two
embeddings, the `INF` identification `Q_e = Q₊`) are parameters. -/
def recognitionInputsOfRope (e : Nat.Partrec.Code) {H C : Type} [Group H] [Group C]
    [Countable H] [Countable inp.Qplus]
    (hH : ¬ IsOperatorMF H)
    (hHC : SecondLevelIndexSets.FiniteDomain e → ∃ f : H →* C, Function.Injective f)
    (hCQ : ∃ f : C →* Qe inp, Function.Injective f)
    (hQ : SecondLevelIndexSets.InfiniteDomain e →
      ∃ eQ : Qe inp ≃* inp.Qplus, ∀ f : Fxyt, eQ (qe inp f) = inp.qplus f) :
    Recognition.RecognitionInputs e H C Fxyt Ptarget inp.Qplus (Qe inp) (K0 inp)
      (FiniteRope inp) :=
  haveI : Countable Fxyt := ChiodoBelegradek.countable_of_isFinitelyPresented Fxyt
  haveI : Countable (FreeGroup (Fin 2)) :=
    ChiodoBelegradek.countable_of_isFinitelyPresented (FreeGroup (Fin 2))
  haveI : Group.IsFinitelyPresented (Ke inp) := (witness inp).fp
  haveI : Group.IsFinitelyPresented (CentralRope inp) :=
    centralRope_isFinitelyPresented inp
  haveI : Group.IsFinitelyPresented (FiniteRope inp) :=
    finiteRope_isFinitelyPresented inp
  { countable_H := inferInstance
    not_isOperatorMF_H := hH
    embed_H_C := hHC
    embed_C_Q := hCQ
    qe := qe inp
    qplus := inp.qplus
    j := inp.j
    j_injective := inp.j_injective
    residuallyFinite_P := inferInstance
    countable_P := inferInstance
    countable_Q := (QuotientGroup.mk'_surjective inp.N).countable
    countable_Qplus := inferInstance
    L0 := L0 inp
    i0 := i0 inp
    residuallyFinite_K := inferInstance
    countable_K := ChiodoBelegradek.countable_of_isFinitelyPresented (Ke inp)
    countable_Gamma := ChiodoBelegradek.countable_of_isFinitelyPresented (CentralRope inp)
    alpha := alphaAbs inp
    alpha_gen := alphaAbs_gen inp
    alpha_genConj := alphaAbs_genConj inp
    pi1 := piOneAbs inp
    pi1_gen := piOneAbs_gen inp
    pi1_genConj := piOneAbs_genConj inp
    equiv_Q_Qplus := fun h => (hQ h).choose
    qe_eq_qplus := fun h f => (hQ h).choose_spec f
    equiv_Rhat := twistedEquivFiniteRope inp
    countable_Rhat :=
      ChiodoBelegradek.countable_of_isFinitelyPresented (FiniteRope inp) }

end

end RopeInput
end Rope
end MFRecognition
end Manuscript
end GroupApproximation
