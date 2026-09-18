import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.Abstract
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.KOne.AllRanksElementaryCore
import GroupApproximation.Leavitt.PrefixCode
import GroupApproximation.Steinberg.Perfect
import GroupApproximation.Meta.AxiomGuard

/-!
# Superperfect units kill the padded rank-three kernel (lane sk-leavitt-04)

Carto `sk-leavitt` §3, lane 04; Khanh (arXiv:2609.08428), proof of Thm 5.1 at `n = 4`.
Here `L = L_{𝔽₂}(1,2)`, `N₃ = K₂(3, L) = ker (St_3(L) → E_3(L))`, and `stab : St_3 → St_4`
pads along `Fin.castSucc`.

## Route

1. `φ : St_3(L) → E_3(L) = GL_3(L) ≅ Lˣ` is surjective with kernel `N₃`
   (`BinaryLeavitt.elementaryGroup_eq_top`, `SteinbergGroup.projection_surjective`,
   `LeavittFamily.prefixUnitsEquiv (leftCombCode 2)`).
2. `St_3(L)` is perfect (`SteinbergGroup.fin_isPerfect`).  So `ker_le_commutator_of_superperfect`
   (sibling module `KernelCommutator.Abstract`, proved) gives `N₃ ≤ ⁅St_3, N₃⁆` from the
   superperfectness of `Lˣ` (`K2_three_le_commutator_of_superperfect`).
3. Then `stab N₃ ≤ stab ⁅St_3, N₃⁆ = ⁅stab St_3, stab N₃⁆ ≤ ⁅St_4, stab N₃⁆`, and the last group
   is trivial once `stab N₃` is central in `St_4(L)`.

## Interfaces used

* `EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement` and
  `EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement` already exist (lane 15), so
  they are imported rather than redefined.  This lane closes
  `EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement` modulo step 3's centrality.
* Padded centrality (lane sk-leavitt-03, Khanh Lemma 5.6) is not on disk.  It is stated here as
  `BinaryLeavittPaddedCentralThreeStatement`, the special case `n = 3`, `R = L` of lane 03's
  `stab_K2_le_center`.  It is strictly weaker than lane 03's theorem (one rank, one ring) and
  true: `stab k` commutes with every `x_{i,last}(a)` and `x_{last,j}(b)` when `projection k = 1`,
  and these generate `St_4(R)` (Khanh Lemma 5.6).  Here it even holds because `K₂(3, L) = ⊥`
  (Khanh Thm 5.4).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.BooneHigman.SteinbergBasic

/-- `GL_3(L) ≃* Lˣ` along the three-leaf left-comb code. -/
noncomputable def glThreeUnitsEquiv :
    (Matrix (Fin 3) (Fin 3)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))ˣ ≃*
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ :=
  (GroupApproximation.BinaryLeavitt.family (ZMod 2)).prefixUnitsEquiv
    (GroupApproximation.leftCombCode 2)
    ((GroupApproximation.BinaryLeavitt.family (ZMod 2)).leftCombCode_complete 2)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.glThreeUnitsEquiv

/-- `E_3(L) → Lˣ`: inclusion into `GL_3(L)` followed by `glThreeUnitsEquiv`. -/
noncomputable def elementaryThreeToUnits :
    GroupApproximation.elementaryGroup (Fin 3)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) →*
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ :=
  glThreeUnitsEquiv.toMonoidHom.comp
    (GroupApproximation.elementaryGroup (Fin 3)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))).subtype

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.elementaryThreeToUnits

theorem elementaryThreeToUnits_injective : Function.Injective elementaryThreeToUnits := by
  intro a b hab
  have hab' : glThreeUnitsEquiv (a : (Matrix (Fin 3) (Fin 3)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))ˣ) =
      glThreeUnitsEquiv (b : (Matrix (Fin 3) (Fin 3)
        (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))ˣ) := hab
  exact Subtype.ext (glThreeUnitsEquiv.injective hab')

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.elementaryThreeToUnits_injective

/-- Surjectivity uses `GL_3(L) = E_3(L)` (Khanh Lemma 5.7, in the corpus). -/
theorem elementaryThreeToUnits_surjective : Function.Surjective elementaryThreeToUnits := by
  intro u
  have hmem : glThreeUnitsEquiv.symm u ∈ GroupApproximation.elementaryGroup (Fin 3)
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) := by
    rw [GroupApproximation.BinaryLeavitt.elementaryGroup_eq_top (ZMod 2) 3 (by omega)]
    exact Subgroup.mem_top _
  refine ⟨⟨glThreeUnitsEquiv.symm u, hmem⟩, ?_⟩
  change glThreeUnitsEquiv (glThreeUnitsEquiv.symm u) = u
  exact glThreeUnitsEquiv.apply_symm_apply u

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.elementaryThreeToUnits_surjective

/-- `φ : St_3(L) → Lˣ`, the Steinberg projection followed by `elementaryThreeToUnits`. -/
noncomputable def steinbergThreeToUnits :
    St 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) →*
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))ˣ :=
  elementaryThreeToUnits.comp
    (GroupApproximation.SteinbergGroup.projection (I := Fin 3)
      (R := GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.steinbergThreeToUnits

theorem steinbergThreeToUnits_surjective : Function.Surjective steinbergThreeToUnits := by
  intro u
  obtain ⟨e, rfl⟩ := elementaryThreeToUnits_surjective u
  obtain ⟨g, rfl⟩ := GroupApproximation.SteinbergGroup.projection_surjective e
  exact ⟨g, rfl⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.steinbergThreeToUnits_surjective

theorem steinbergThreeToUnits_ker :
    steinbergThreeToUnits.ker =
      K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) := by
  ext g
  exact MonoidHom.mem_ker.trans
    ((map_eq_one_iff elementaryThreeToUnits elementaryThreeToUnits_injective
      (x := GroupApproximation.SteinbergGroup.projection g)).trans (mem_K2_iff g).symm)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.steinbergThreeToUnits_ker

/-- **Lane 04, coinvariant form.**  If `Lˣ` is superperfect, then `K₂(3, L) ≤ ⁅St_3(L), K₂(3, L)⁆`. -/
theorem K2_three_le_commutator_of_superperfect
    (hs : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) ≤
      ⁅(⊤ : Subgroup (St 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))),
        K2n 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))⁆ := by
  haveI : Group.IsPerfect
      (St 3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :=
    GroupApproximation.SteinbergGroup.fin_isPerfect (by omega)
  have h := ker_le_commutator_of_superperfect steinbergThreeToUnits
    steinbergThreeToUnits_surjective hs
  rw [steinbergThreeToUnits_ker] at h
  exact h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.K2_three_le_commutator_of_superperfect

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
