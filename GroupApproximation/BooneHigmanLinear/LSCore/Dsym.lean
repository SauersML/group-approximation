import GroupApproximation.BooneHigmanLinear.LSCore.ZStable
import GroupApproximation.BooneHigmanLinear.LSCore.Symbols
import GroupApproximation.Meta.AxiomGuard

/-!
# Dennis–Stein symbols lie in `Z_α(A, M)` (towards Lavrenov–Sinchuk, Remarks 5.6 and 5.11)

For `α = (i, j)`, `a ∈ A`, `m ∈ M` and `u = 1 + a m` a unit, `⟨a, m⟩_α ∈ Z_α(A, M)`
(`dsym_mem_zAlpha`), when `|I| ≥ 5`. The inputs are:
* `DsymRootIndep` (k2-hl4c's `Symbols.lean`): `⟨a, m⟩_α = ⟨a, m⟩_γ` for a root `γ = (k, l)`
  disjoint from `α`;
* Theorem 4.2 (`RelGen.Thm42Statement`, lane bh-pal-wire) for the index set
  `Compl2 i j = I ∖ {i, j}`.

The proof: `⟨a, m⟩_γ` is the image of the symbol of `St_{I ∖ {i, j}}(A)` under the index
inclusion. That symbol dies modulo `M`, since `⟨ā, 0⟩ = 1`. So by Theorem 4.2 it is a product of
`z_{γ'}(m', ζ)` with `γ'` inside `I ∖ {i, j}`, and those map to generators of `Z_α(A, M)`
(roots `⊥ α`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace LSCore

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.RelGen (zElt relKer zSet ThirdIndex Thm42Statement)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h)

/-- The index set `I ∖ {i, j}`. -/
abbrev Compl2 {I : Type*} (i j : I) : Type _ := {p : I // p ≠ i ∧ p ≠ j}

/-- The inclusion `I ∖ {i, j} ↪ I`. -/
def compl2Emb {I : Type*} (i j : I) : Compl2 i j ↪ I := Function.Embedding.subtype _

@[simp] theorem compl2Emb_apply {I : Type*} {i j : I} (p : Compl2 i j) :
    compl2Emb i j p = p.1 :=
  rfl

section Index

variable {I J R : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [CommRing R]

theorem indexMap_zElt (e : I ↪ J) {p q : I} (hpq : p ≠ q) (s ξ : R) :
    indexMap e (zElt p q hpq s ξ) = zElt (e p) (e q) (e.injective.ne hpq) s ξ := by
  simp only [zElt, map_mul, indexMap_x]

theorem indexMap_dsym (e : I ↪ J) {p q : I} (hpq : p ≠ q) (a b : R) (u : Rˣ) :
    indexMap e (dsym p q hpq a b u) = dsym (e p) (e q) (e.injective.ne hpq) a b u := by
  simp only [dsym, h, w, map_mul, map_inv, indexMap_x]

theorem dsym_zero_right {p q : I} (hpq : p ≠ q) (a : R) {u : Rˣ} (hu : (u : R) = 1) :
    dsym p q hpq a 0 u = 1 := by
  have hu' : u = 1 := Units.ext hu
  subst hu'
  simp only [dsym, zero_mul, neg_zero, x_zero, one_mul, mul_one, inv_one, Units.val_one,
    h_one, x_mul, add_neg_cancel]

end Index

variable {I : Type} [Fintype I] [DecidableEq I] {A : Type} [CommRing A]

/-- **Dennis–Stein symbols lie in `Z_α(A, M)`**, for `|I| ≥ 5`. -/
theorem dsym_mem_zAlpha (h42 : Thm42Statement) (hind : DsymRootIndep I A)
    (h5 : 5 ≤ Fintype.card I) {M : Ideal A} {i j : I} (hij : i ≠ j) (a m : A) (hm : m ∈ M)
    (u : Aˣ) (hu : (u : A) = 1 + a * m) : dsym i j hij a m u ∈ zAlpha M i j := by
  obtain ⟨k, hki, hkj, -, -⟩ := exists_ne4 h5 i j i j
  obtain ⟨l, hli, hlj, hlk, -⟩ := exists_ne4 h5 i j k k
  have h3 : ThirdIndex (Compl2 i j) := by
    intro a' b'
    obtain ⟨r, hri, hrj, hra, hrb⟩ := exists_ne4 h5 i j a'.1 b'.1
    exact ⟨⟨r, hri, hrj⟩, fun h => hra (congrArg Subtype.val h).symm,
      fun h => hrb (congrArg Subtype.val h).symm⟩
  have hkl' : (⟨k, hki, hkj⟩ : Compl2 i j) ≠ ⟨l, hli, hlj⟩ :=
    fun h => hlk (congrArg Subtype.val h).symm
  have hd : dsym i j hij a m u = indexMap (compl2Emb i j) (dsym _ _ hkl' a m u) := by
    rw [indexMap_dsym]
    exact hind i j k l hij (fun h => hlk h.symm) (fun h => hki h.symm) (fun h => hli h.symm)
      (fun h => hkj h.symm) (fun h => hlj h.symm) a m u hu
  have hker : dsym (⟨k, hki, hkj⟩ : Compl2 i j) ⟨l, hli, hlj⟩ hkl' a m u ∈
      relKer (Compl2 i j) M := by
    change _ ∈ K2Found.relSt (Compl2 i j) (Ideal.Quotient.mk M)
    rw [K2Found.mem_relSt, ringMap_dsym, Ideal.Quotient.eq_zero_iff_mem.mpr hm]
    refine dsym_zero_right _ _ ?_
    simp only [Units.coe_map, MonoidHom.coe_coe, hu, map_add, map_one, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr hm, mul_zero, add_zero]
  rw [h42 (Compl2 i j) h3 A M] at hker
  rw [hd]
  have hle : (Subgroup.closure (zSet (Compl2 i j) M fun _ _ => True)).map
      (indexMap (R := A) (compl2Emb i j)) ≤ zAlpha M i j := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨p, q, hpq, s, ξ, -, hs, rfl⟩, rfl⟩
    rw [indexMap_zElt]
    exact zA_z _ ⟨p.2.1, p.2.2, q.2.1, q.2.2⟩ hs ξ
  exact hle (Subgroup.mem_map_of_mem _ hker)

#audit_axioms dsym_mem_zAlpha

end LSCore
end BooneHigmanLinear
end GroupApproximation
