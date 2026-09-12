import GroupApproximation.Higman.CentralHNNFreeLabelKernel
import GroupApproximation.Higman.FreeGroupHall
import GroupApproximation.Sofic.ProfiniteFiniteIndexPromotion
import GroupApproximation.Sofic.ProfiniteFiniteExtensionLERF
import GroupApproximation.Sofic.ProfiniteRetract
import GroupApproximation.Sofic.ProfiniteSplitEmbedding

/-!
# Profinite closure for finite-base HNN subextensions

The finite-cover proof starts with the special free-factor feature exposed by
the free-label action: words supported on a selected set of labels form a
coordinate subgroup of a free group.  Killing every other basis letter is an
explicit retraction, so these coordinate subgroups are profinitely closed.

This is the terminal free-coordinate step in the finite-base HNN
subextension argument.  It is kept separate from any infinite-base lifting
criterion, which additionally has to supply cofinal quotients preserving the
relevant vertex products.
-/

namespace GroupApproximation
namespace Higman
namespace HNNSubextensionFiniteBaseProfinite

noncomputable section

namespace Coordinate

variable {ι : Type} (S : Set ι)

abbrev Sub : Subgroup (FreeGroup ι) :=
  Subgroup.closure (FreeGroup.of '' S)

/-- Killing the complementary basis letters always lands in the selected
coordinate subgroup. -/
theorem killOutside_mem (w : FreeGroup ι) :
    CentralHNNFreeLabel.Coordinate.killOutside S w ∈ Sub S := by
  classical
  induction w using FreeGroup.induction_on with
  | C1 => simp [Sub]
  | of i =>
      by_cases hi : i ∈ S
      · rw [CentralHNNFreeLabel.Coordinate.killOutside_of_mem hi]
        exact Subgroup.subset_closure ⟨i, hi, rfl⟩
      · rw [CentralHNNFreeLabel.Coordinate.killOutside_of_notMem hi]
        exact Subgroup.one_mem _
  | mul x y hx hy =>
      simpa only [map_mul] using (Sub S).mul_mem hx hy
  | inv_of i hi =>
      simpa only [map_inv] using (Sub S).inv_mem hi

/-- The coordinate projection with its codomain restricted to the selected
free factor. -/
def ret : FreeGroup ι →* Sub S :=
  (CentralHNNFreeLabel.Coordinate.killOutside S).codRestrict (Sub S)
    (killOutside_mem S)

theorem ret_comp_subtype :
    (ret S).comp (Sub S).subtype = MonoidHom.id (Sub S) := by
  apply MonoidHom.ext
  intro w
  apply Subtype.ext
  exact CentralHNNFreeLabel.Coordinate.killOutside_fixes w.property

/-- **Coordinate subgroups of a free group are profinitely closed.** -/
theorem profiniteClosure_sub : profiniteClosure (Sub S) = Sub S := by
  have h := profiniteClosure_range_eq_range_of_retraction
    (Sub S).subtype (ret S) (ret_comp_subtype S)
  simpa only [Subgroup.range_subtype] using h

end Coordinate

namespace Central

open HNNExtension

variable {G : Type} [Group G] (M : Subgroup G)

/-- The free stable-conjugate basis, with its codomain restricted to the
kernel of the base retraction. -/
def kernelLift (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeGroup (CentralHNNFreeLabel.Label M d) →*
      (CentralHNNFreeLabel.baseRet M).ker :=
  (CentralHNNFreeLabel.stableConjLift M d).codRestrict _ fun w ↦ by
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      CentralHNNFreeLabel.baseRet_comp_stableConjLift]
    rfl

/-- The kernel restriction of the stable-conjugate lift is an isomorphism. -/
theorem kernelLift_bijective
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    Function.Bijective (kernelLift M d) := by
  constructor
  · intro x y hxy
    apply CentralHNNFreeLabel.stableConjLift_injective M d
    exact Subtype.ext_iff.mp hxy
  · rintro ⟨z, hz⟩
    have hzrange : z ∈ (CentralHNNFreeLabel.stableConjLift M d).range := by
      rw [CentralHNNFreeLabel.range_stableConjLift_eq_ker_baseRet]
      exact hz
    obtain ⟨w, hw⟩ := hzrange
    exact ⟨w, Subtype.ext hw⟩

/-- The free group of stable conjugates is exactly the base-retraction
kernel, intrinsically as a group. -/
noncomputable def kernelEquiv
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    FreeGroup (CentralHNNFreeLabel.Label M d) ≃*
      (CentralHNNFreeLabel.baseRet M).ker :=
  MulEquiv.ofBijective (kernelLift M d) (kernelLift_bijective M d)

theorem kernelEquiv_comp_subtype
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    ((CentralHNNFreeLabel.baseRet M).ker.subtype).comp
        (kernelEquiv M d).toMonoidHom =
      CentralHNNFreeLabel.stableConjLift M d := by
  ext w
  rfl

instance kernel_finiteIndex [Finite G] :
    (CentralHNNFreeLabel.baseRet M).ker.FiniteIndex := by
  exact finiteIndex_comap_of_normal (CentralHNNFreeLabel.baseRet M)
    (⊥ : Subgroup G)

/-- A coordinate subgroup of the stable-conjugate kernel remains closed
after inclusion in a central HNN extension with finite base. -/
theorem profiniteClosure_labelSub_in_extension [Finite G]
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (S : Subgroup G) :
    profiniteClosure
        ((CentralHNNFreeLabel.labelSub M d S).map
          (CentralHNNFreeLabel.stableConjLift M d)) =
      (CentralHNNFreeLabel.labelSub M d S).map
        (CentralHNNFreeLabel.stableConjLift M d) := by
  let K := (CentralHNNFreeLabel.baseRet M).ker
  let e := kernelEquiv M d
  let I : Subgroup K := (CentralHNNFreeLabel.labelSub M d S).map e.toMonoidHom
  haveI : Group.ResiduallyFinite K :=
    residuallyFinite_of_mulEquiv e.symm
  have hI : profiniteClosure I = I := by
    exact profiniteClosure_map_eq_of_split_closed e.toMonoidHom
      e.symm.toMonoidHom (by ext w; simp) _ (Coordinate.profiniteClosure_sub _)
  have hpromoted := profiniteClosure_map_subtype_eq_of_closed K I hI
  have hmap : I.map K.subtype =
      (CentralHNNFreeLabel.labelSub M d S).map
        (CentralHNNFreeLabel.stableConjLift M d) := by
    dsimp [I, K, e]
    rw [Subgroup.map_map]
    exact congrArg
      (fun f : FreeGroup (CentralHNNFreeLabel.Label M d) →* CentHNN M ↦
        (CentralHNNFreeLabel.labelSub M d S).map f)
      (kernelEquiv_comp_subtype M d)
  rwa [hmap] at hpromoted

/-- The trace of the subextension `⟨S,t⟩` on the free kernel is closed in
the whole finite-base central HNN extension. -/
theorem profiniteClosure_subextension_inf_kernel [Finite G]
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (S : Subgroup G) :
    profiniteClosure
        (Subgroup.closure (HNNDescent.genSet (MulEquiv.refl M) S) ⊓
          (CentralHNNFreeLabel.baseRet M).ker) =
      Subgroup.closure (HNNDescent.genSet (MulEquiv.refl M) S) ⊓
        (CentralHNNFreeLabel.baseRet M).ker := by
  rw [CentralHNNFreeLabel.closure_inf_ker_baseRet]
  exact profiniteClosure_labelSub_in_extension M d S

/-- **Finite-base central-HNN subextensions are profinitely closed.** -/
theorem profiniteClosure_subextension [Finite G]
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (S : Subgroup G) :
    profiniteClosure
        (Subgroup.closure (HNNDescent.genSet (MulEquiv.refl M) S)) =
      Subgroup.closure (HNNDescent.genSet (MulEquiv.refl M) S) := by
  let C : Subgroup (CentHNN M) :=
    Subgroup.closure (HNNDescent.genSet (MulEquiv.refl M) S)
  let K : Subgroup (CentHNN M) := CentralHNNFreeLabel.baseRet M |>.ker
  have htrace : profiniteClosure (C ⊓ K) = C ⊓ K :=
    profiniteClosure_subextension_inf_kernel M d S
  apply le_antisymm
  · intro x hx
    have hxbase : CentralHNNFreeLabel.baseRet M x ∈
        C.map (CentralHNNFreeLabel.baseRet M) :=
      hx G (CentralHNNFreeLabel.baseRet M)
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxbase
    let y : CentHNN M := c⁻¹ * x
    have hyK : y ∈ K := by
      change CentralHNNFreeLabel.baseRet M y = 1
      dsimp [y]
      rw [map_mul, map_inv, hcx, inv_mul_cancel]
    have hyClosure : y ∈ profiniteClosure (C ⊓ K) := by
      intro Q _ _ q
      let test : CentHNN M →* G × Q :=
        (CentralHNNFreeLabel.baseRet M).prod q
      have htest : test x ∈ C.map test := hx (G × Q) test
      obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.mp htest
      have hbase := congrArg Prod.fst hhx
      have hq := congrArg Prod.snd hhx
      change CentralHNNFreeLabel.baseRet M h =
        CentralHNNFreeLabel.baseRet M x at hbase
      change q h = q x at hq
      refine ⟨c⁻¹ * h, ?_, ?_⟩
      · constructor
        · exact C.mul_mem (C.inv_mem hc) hh
        · change CentralHNNFreeLabel.baseRet M (c⁻¹ * h) = 1
          rw [map_mul, map_inv, hbase, hcx, inv_mul_cancel]
      · calc
          q (c⁻¹ * h) = (q c)⁻¹ * q h := by rw [map_mul, map_inv]
          _ = (q c)⁻¹ * q x := by rw [hq]
          _ = q (c⁻¹ * x) := by rw [map_mul, map_inv]
          _ = q y := by rfl
    rw [htrace] at hyClosure
    have hxy : x = c * y := by
      dsimp [y]
      group
    rw [hxy]
    exact C.mul_mem hc hyClosure.1
  · exact le_profiniteClosure C

/-- **A central HNN extension of a finite group is LERF.**  Its base
retraction kernel is a free group, so Hall's theorem applies there, and LERF
then promotes through the finite normal extension. -/
theorem profiniteClosure_eq_of_fg [Finite G]
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (H : Subgroup (CentHNN M)) (hH : H.FG) :
    profiniteClosure H = H := by
  let K : Subgroup (CentHNN M) := (CentralHNNFreeLabel.baseRet M).ker
  let e := kernelEquiv M d
  apply profiniteClosure_eq_of_normal_finiteIndex_lerf K ?_ H hH
  intro L hL
  let P : Subgroup (FreeGroup (CentralHNNFreeLabel.Label M d)) :=
    L.map e.symm.toMonoidHom
  have hPfg : P.FG := Higman.fg_map hL e.symm.toMonoidHom
  have hPclosed : profiniteClosure P = P :=
    FreeGroupHall.profiniteClosure_eq_of_fg P hPfg
  haveI : Group.ResiduallyFinite K := residuallyFinite_of_mulEquiv e.symm
  have hmapped := profiniteClosure_map_eq_of_split_closed e.toMonoidHom
    e.symm.toMonoidHom (by ext w; simp) P hPclosed
  have hPe : P.map e.toMonoidHom = L := by
    ext x
    constructor
    · rintro ⟨p, hp, hpx⟩
      obtain ⟨l, hl, hlp⟩ := hp
      subst p
      have hlx : l = x := by simpa using hpx
      rwa [hlx] at hl
    · intro hx
      refine ⟨e.symm x, ⟨x, hx, rfl⟩, ?_⟩
      simp
  rwa [hPe] at hmapped

end Central

end

end HNNSubextensionFiniteBaseProfinite
end Higman
end GroupApproximation
