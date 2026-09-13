import GroupApproximation.Manuscript.OneSidedMFRadical.TorsionComplementaryIdempotentsDefect
import GroupApproximation.Meta.AxiomGuard

/-!
# `B = ⟨L, W, c, y⟩` and the finite central `⟨z⟩`, as a group-level argument

`non_mf_groups_exist.tex`, proof of Proposition `prop:bilateral-three` (tex 1577–1594):

> Then `c ∈ C_B(L)` and `WcW⁻¹ = e₁₃(f_{0,-2})`, `δ = [WcW⁻¹, ℓ] = e₂₃(-f_{0,-2})`,
> `[y, δ] = z⁻¹`.  Hence `z ∈ 𝔇_B(L)`.  It commutes with `L`, since both its supports lie
> outside `P`; with `W`, since its two levels are fixed; and with `c, y`, by the matrix-unit
> products.  So `⟨z⟩` is a nontrivial finite central subgroup of `B`, of order `char(k)`.
> Theorem `thm:compression-criterion` kills `z` under every MF homomorphism from `B`, hence
> from `GL₃(R_X)`.  The identities `[z, e₃₁(f_{-2,0})] = e₃₁(f_{-1,0})`,
> `[e₂₃(f_{0,-1}), e₃₁(f_{-1,0})] = e₂₁(d)` then kill the defect root.

These sentences use only the displayed group relations, never the ring.  This module proves
them in an arbitrary countable group, with the printed relations as hypotheses; the ring
identities that supply the relations inside `GL₃(R_X)` are the three-coordinate cell.

The compressor `W` need not be elementary (tex 1605–1607), so, unlike the rank-four cell of
`prop:torsion-defect-ring`, the ambient group is not an elementary group: it is any group,
for instance `GL₃(R_X)`.  The commutator convention is the printed one,
`[g, h] = g h g⁻¹ h⁻¹` (tex 156), which is Mathlib's `⁅g, h⁆`.
-/

namespace GroupApproximation
namespace Manuscript
namespace ChainCore
namespace BilateralThree

open GroupApproximation.Manuscript.OneSidedMFRadical
open scoped commutatorElement

/-- **Printed (tex 1589–1594):** once `z` is killed, the identities `[z, g₁] = a` and
`[g₂, a] = b` kill `a` and then `b`.  In the proof, `g₁ = e₃₁(f_{-2,0})`,
`a = e₃₁(f_{-1,0})`, `g₂ = e₂₃(f_{0,-1})` and `b = e₂₁(d)`. -/
theorem killed_of_commutators {G M : Type} [Group G] [Group M] (f : G →* M)
    {z g₁ g₂ a b : G} (hz : f z = 1) (h₁ : ⁅z, g₁⁆ = a) (h₂ : ⁅g₂, a⁆ = b) : f b = 1 := by
  have ha : f a = 1 := by
    rw [← h₁, map_commutatorElement, hz, commutatorElement_one_left]
  rw [← h₂, map_commutatorElement, ha, commutatorElement_one_right]

section GroupKill

variable {G : Type} [Group G] (L : Subgroup G) (W c y : G)

/-- **Printed:** `B = ⟨L, W, c, y⟩`. -/
def bilateralB : Subgroup G :=
  Subgroup.closure ((L : Set G) ∪ {W, c, y})

theorem le_bilateralB : L ≤ bilateralB L W c y := fun _ hg ↦
  Subgroup.subset_closure (Or.inl hg)

theorem W_mem_bilateralB : W ∈ bilateralB L W c y :=
  Subgroup.subset_closure (Or.inr (by simp))

theorem c_mem_bilateralB : c ∈ bilateralB L W c y :=
  Subgroup.subset_closure (Or.inr (by simp))

theorem y_mem_bilateralB : y ∈ bilateralB L W c y :=
  Subgroup.subset_closure (Or.inr (by simp))

/-- **Printed:** `z` commutes with `L`, `W`, `c` and `y`, hence with all of `B`. -/
theorem commute_of_mem_bilateralB {z : G}
    (hzL : ∀ δ ∈ L, Commute z δ) (hzW : Commute z W) (hzc : Commute z c)
    (hzy : Commute z y) : ∀ b ∈ bilateralB L W c y, Commute z b := by
  have hsub : bilateralB L W c y ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [bilateralB, Subgroup.closure_le]
    rintro g (hg | hg)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hzL g hg
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact hzW
      · exact hzc
      · exact hzy
  intro b hb
  have hcent := hsub hb
  rw [Subgroup.mem_centralizer_iff] at hcent
  exact hcent z rfl

/-- **Printed (tex 1577–1588), the kill.**

Let `L ≤ G` have property `(T)`, let `W` compress `L`, let `c` centralize `L`, let `ℓ ∈ L`,
and let `z` satisfy `[y, [WcW⁻¹, ℓ]] = z⁻¹`, commute with `L`, `W`, `c`, `y`, and have finite
order.  Then every homomorphism from `G` to an MF group kills `z`.

The proof is the printed one: `z ∈ B`, `z ∈ 𝔇_B(L)`, `⟨z⟩` is finite (so Kazhdan) and central
(so normal) in `B`, and Theorem `thm:compression-criterion` applied to the countable group `B`
puts `z` in the corona MF residual of `B`, which every MF target kills.  Nothing here needs
`z ≠ 1`. -/
theorem killed_of_finite_central_defect [Countable G]
    (hL : HasKazhdanPropertyT.{0, 0} ↥L) {ℓ z : G}
    (hW : ∀ δ ∈ L, W * δ * W⁻¹ ∈ L) (hc : ∀ δ ∈ L, Commute c δ) (hℓ : ℓ ∈ L)
    (hyz : ⁅y, ⁅W * c * W⁻¹, ℓ⁆⁆ = z⁻¹)
    (hzL : ∀ δ ∈ L, Commute z δ) (hzW : Commute z W) (hzc : Commute z c)
    (hzy : Commute z y) (hfin : IsOfFinOrder z)
    {M : Type} [Group M] (hM : IsOperatorMF M) (f : G →* M) : f z = 1 := by
  set B := bilateralB L W c y
  have hLB : L ≤ B := le_bilateralB L W c y
  have hWB : W ∈ B := W_mem_bilateralB L W c y
  have hcB : c ∈ B := c_mem_bilateralB L W c y
  have hyB : y ∈ B := y_mem_bilateralB L W c y
  have hℓB : ℓ ∈ B := hLB hℓ
  have hxB : W * c * W⁻¹ ∈ B := B.mul_mem (B.mul_mem hWB hcB) (B.inv_mem hWB)
  have hδB : ⁅W * c * W⁻¹, ℓ⁆ ∈ B := by
    rw [commutatorElement_def]
    exact B.mul_mem (B.mul_mem (B.mul_mem hxB hℓB) (B.inv_mem hxB)) (B.inv_mem hℓB)
  have hzB : z ∈ B := by
    have h : ⁅y, ⁅W * c * W⁻¹, ℓ⁆⁆ ∈ B := by
      rw [commutatorElement_def y (⁅W * c * W⁻¹, ℓ⁆)]
      exact B.mul_mem (B.mul_mem (B.mul_mem hyB hδB) (B.inv_mem hyB)) (B.inv_mem hδB)
    rw [hyz] at h
    simpa using B.inv_mem h
  let zB : ↥B := ⟨z, hzB⟩
  let LB : Subgroup ↥B := L.subgroupOf B
  have hcentral : ∀ b : ↥B, Commute zB b := fun b ↦
    Subtype.ext (commute_of_mem_bilateralB L W c y hzL hzW hzc hzy b b.2)
  -- `⟨z⟩` is normal in `B`, being central.
  haveI : (Subgroup.zpowers zB).Normal := by
    constructor
    intro x hx g
    obtain ⟨k, rfl⟩ := hx
    have hck : zB ^ k * g = g * zB ^ k := (hcentral g).zpow_left k
    have hconj : g * zB ^ k * g⁻¹ = zB ^ k := by
      rw [← hck, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  -- `⟨z⟩` is finite, hence Kazhdan.
  haveI : Finite ↥(Subgroup.zpowers zB) := by
    obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    have hpowB : zB ^ m = 1 := Subtype.ext (show z ^ m = 1 from hpow)
    exact Set.Finite.to_subtype
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hpowB⟩).finite_zpowers
  have hKT : HasKazhdanPropertyT.{0, 0} ↥(Subgroup.zpowers zB) :=
    hasKazhdanPropertyT_of_finite _
  have hLBT : HasKazhdanPropertyT.{0, 0} ↥LB :=
    HasKazhdanPropertyT.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLB) hL
  -- `z ∈ 𝔇_B(L)`, from `δ = [WcW⁻¹, ℓ]` and `z⁻¹ = [y, δ]`.
  have hzD : zB ∈ printedDefect LB := by
    let W' : ↥B := ⟨W, hWB⟩
    let c' : ↥B := ⟨c, hcB⟩
    let y' : ↥B := ⟨y, hyB⟩
    let l' : ↥B := ⟨ℓ, hℓB⟩
    have hWcomp : ∀ δ ∈ LB, W' * δ * W'⁻¹ ∈ LB := by
      intro δ hδ
      rw [Subgroup.mem_subgroupOf] at hδ ⊢
      exact hW _ hδ
    have hccomm : ∀ δ ∈ LB, Commute c' δ := by
      intro δ hδ
      rw [Subgroup.mem_subgroupOf] at hδ
      exact Subtype.ext (hc _ hδ)
    have hlmem : l' ∈ LB := by
      rw [Subgroup.mem_subgroupOf]
      exact hℓ
    have hd : ⁅W' * c' * W'⁻¹, l'⁆ ∈ printedDefect LB :=
      printedDefect_generator_mem LB hWcomp hccomm hlmem
    have hyd : y' * ⁅W' * c' * W'⁻¹, l'⁆ * y'⁻¹ * (⁅W' * c' * W'⁻¹, l'⁆)⁻¹
        ∈ printedDefect LB :=
      TorsionComplementaryIdempotents.commutatorRight_mem y' hd
    have hval : y' * ⁅W' * c' * W'⁻¹, l'⁆ * y'⁻¹ * (⁅W' * c' * W'⁻¹, l'⁆)⁻¹ = zB⁻¹ := by
      refine Subtype.ext ?_
      show y * ⁅W * c * W⁻¹, ℓ⁆ * y⁻¹ * (⁅W * c * W⁻¹, ℓ⁆)⁻¹ = z⁻¹
      rw [← commutatorElement_def, hyz]
    rw [hval] at hyd
    simpa using (printedDefect LB).inv_mem hyd
  -- The criterion inside the countable group `B`.
  haveI : Countable ↥B := Subtype.countable
  have hres := (manuscriptOneSidedCompressionCriterion ↥B LB hLBT).1
    (Subgroup.zpowers zB) hKT (Subgroup.zpowers_le.mpr hzD)
  exact TorsionComplementaryIdempotents.killed_of_mem_manuscriptCoronaMFResidual hM
    (f.comp B.subtype) (hres (Subgroup.mem_zpowers _))

/-- **Printed (tex 1577–1594), the kill carried to the defect root.**  Under the hypotheses of
`killed_of_finite_central_defect`, and the two printed commutator identities
`[z, g₁] = a`, `[g₂, a] = b`, every homomorphism from `G` to an MF group kills `b`. -/
theorem root_killed_of_finite_central_defect [Countable G]
    (hL : HasKazhdanPropertyT.{0, 0} ↥L) {ℓ z g₁ g₂ a b : G}
    (hW : ∀ δ ∈ L, W * δ * W⁻¹ ∈ L) (hc : ∀ δ ∈ L, Commute c δ) (hℓ : ℓ ∈ L)
    (hyz : ⁅y, ⁅W * c * W⁻¹, ℓ⁆⁆ = z⁻¹)
    (hzL : ∀ δ ∈ L, Commute z δ) (hzW : Commute z W) (hzc : Commute z c)
    (hzy : Commute z y) (hfin : IsOfFinOrder z) (h₁ : ⁅z, g₁⁆ = a) (h₂ : ⁅g₂, a⁆ = b)
    {M : Type} [Group M] (hM : IsOperatorMF M) (f : G →* M) : f b = 1 :=
  killed_of_commutators f
    (killed_of_finite_central_defect L W c y hL hW hc hℓ hyz hzL hzW hzc hzy hfin hM f) h₁ h₂

end GroupKill

end BilateralThree
end ChainCore
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_axioms GroupApproximation.Manuscript.ChainCore.BilateralThree.killed_of_commutators
#audit_axioms GroupApproximation.Manuscript.ChainCore.BilateralThree.killed_of_finite_central_defect
#audit_axioms GroupApproximation.Manuscript.ChainCore.BilateralThree.root_killed_of_finite_central_defect
