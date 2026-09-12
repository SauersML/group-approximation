import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite
import GroupApproximation.Algebra.GroupTorsionFree
import GroupApproximation.Kazhdan.CCKWFiniteSubgroupsStatement
import GroupApproximation.Kazhdan.GHBQuotientMatrices

/-!
# The quotient `ψ : GHB(7) → GL₄(F₇)` on the three vertex groups

`Kazhdan/GHBQuotientMatrices.lean` defines `ψ` (CCKW Proposition 7.15, `k = 1`).  This
module computes its restriction to the vertex groups `⟨a,b⟩`, `⟨c,b⟩`, `⟨c,a⟩` by
normal forms, and draws the two consequences the lattice route needs.

**Normal forms.**  The images are `{V'a^i V'b^j [V'a,V'b]^k}` (343 matrices) and
`{V'c^i V'y^j [V'c,V'y]^k [V'c,V'y,V'y]^l}` for `y = b, a` (2401 matrices each).  Each
normal form comes with a readout from four or three matrix entries, and the kernel
checks (`decide +kernel`): the readout inverts the normal form; left multiplication
by a generator or its inverse stays in the normal form; and every normal form has
seventh power `1`.  The readout formulas were found and checked on all 343/2401 inputs
by `experiments/kms_ghb7_quotient/` (lane kh-cckw model tests).

**Injectivity on the vertex groups.**  The normal forms give `7³` resp. `7⁴` distinct
elements in the image, so `U₃(7) → GL₄(F₇)` and `U₄(7) → GL₄(F₇)` are injective as soon
as the presentations bound the orders (CCKW Proposition 7.2: `|U₃(7)| ≤ 7³`,
`|U₄(7)| ≤ 7⁴`, lane kh-hyperbolic module 2).  So `ψ` kills no nontrivial element of a
vertex group.

**Consequences.**  Over CCKW Theorem 3.1(ii) in its cyclic case
(`CCKWFiniteOrderConjugateIntoVertex`):
* `psiKer` is torsion-free (`isPowerTorsionFree_psiKer`): a torsion element of the
  kernel is conjugate into a vertex group, where `ψ` is injective;
* `GHB(7)` is infinite (`infinite_ghb7`): otherwise `abc` has finite order, so a
  conjugate lies in a vertex group, whose image has exponent `7`, while
  `(V'a V'b V'c)⁷ ≠ 1` (the product has order `42`).  This half does not use the order
  bounds of the vertex groups.
-/

namespace GroupApproximation
namespace KMSGroup
namespace GHBQuotient

/-! ## Conjugation -/

theorem pow_eq_one_of_conj_pow_eq_one {G : Type*} [Group G] {x g : G} {n : ℕ}
    (h : (x⁻¹ * g * x) ^ n = 1) : g ^ n = 1 := by
  have h' : (x⁻¹ * g * x⁻¹⁻¹) ^ n = 1 := by simpa only [inv_inv] using h
  rw [conj_pow] at h'
  exact conj_eq_one_iff.mp h'

theorem eq_one_of_conj_eq_one {G : Type*} [Group G] {x g : G} (h : x⁻¹ * g * x = 1) :
    g = 1 := by
  have h' : x⁻¹ * g * x⁻¹⁻¹ = 1 := by simpa only [inv_inv] using h
  exact conj_eq_one_iff.mp h'

/-! ## The commutators of the generators -/

/-- `[V'a, V'b]`. -/
def uAB : GL4 := comm uA uB

/-- `[V'c, V'b]`. -/
def uCB : GL4 := comm uC uB

/-- `[V'c, V'b, V'b]`. -/
def uCBB : GL4 := comm3 uC uB uB

/-- `[V'c, V'a]`. -/
def uCA : GL4 := comm uC uA

/-- `[V'c, V'a, V'a]`. -/
def uCAA : GL4 := comm3 uC uA uA

/-! ## The vertex group `⟨a, b⟩ ≅ U₃(7)` -/

/-- The normal form `V'a^i V'b^j [V'a,V'b]^k`. -/
def wordAB (t : ZMod 7 × ZMod 7 × ZMod 7) : GL4 :=
  uA ^ t.1.val * uB ^ t.2.1.val * uAB ^ t.2.2.val

/-- Its readout: `i = M₀₃`, `j = M₁₀`, `k = 4 (−M₁₃ − M₀₃ M₁₀)`. -/
def readAB (M : GL4) : ZMod 7 × ZMod 7 × ZMod 7 :=
  (M.val 0 3, M.val 1 0, 4 * (-(M.val 1 3) - M.val 0 3 * M.val 1 0))

theorem readAB_wordAB : ∀ t, readAB (wordAB t) = t := by decide +kernel

theorem wordAB_zero : wordAB 0 = 1 := by decide +kernel

theorem wordAB_uA_mul : ∀ t, wordAB (readAB (uA * wordAB t)) = uA * wordAB t := by
  decide +kernel

theorem wordAB_uA_inv_mul : ∀ t, wordAB (readAB (uA⁻¹ * wordAB t)) = uA⁻¹ * wordAB t := by
  decide +kernel

theorem wordAB_uB_mul : ∀ t, wordAB (readAB (uB * wordAB t)) = uB * wordAB t := by
  decide +kernel

theorem wordAB_uB_inv_mul : ∀ t, wordAB (readAB (uB⁻¹ * wordAB t)) = uB⁻¹ * wordAB t := by
  decide +kernel

theorem wordAB_pow_seven : ∀ t, wordAB t ^ 7 = 1 := by decide +kernel

/-! ## The vertex group `⟨c, b⟩ ≅ U₄(7)` -/

/-- The normal form `V'c^i V'b^j [V'c,V'b]^k [V'c,V'b,V'b]^l`. -/
def wordCB (t : ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7) : GL4 :=
  uC ^ t.1.val * uB ^ t.2.1.val * uCB ^ t.2.2.1.val * uCBB ^ t.2.2.2.val

/-- Its readout: `i = M₃₁`, `j = M₁₀`, `k = M₂₁`, `l = 4 (M₂₀ − M₂₁ + M₁₀ M₂₁)`. -/
def readCB (M : GL4) : ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 :=
  (M.val 3 1, M.val 1 0, M.val 2 1, 4 * (M.val 2 0 - M.val 2 1 + M.val 1 0 * M.val 2 1))

theorem readCB_wordCB : ∀ t, readCB (wordCB t) = t := by decide +kernel

theorem wordCB_zero : wordCB 0 = 1 := by decide +kernel

theorem wordCB_uC_mul : ∀ t, wordCB (readCB (uC * wordCB t)) = uC * wordCB t := by
  decide +kernel

theorem wordCB_uC_inv_mul : ∀ t, wordCB (readCB (uC⁻¹ * wordCB t)) = uC⁻¹ * wordCB t := by
  decide +kernel

theorem wordCB_uB_mul : ∀ t, wordCB (readCB (uB * wordCB t)) = uB * wordCB t := by
  decide +kernel

theorem wordCB_uB_inv_mul : ∀ t, wordCB (readCB (uB⁻¹ * wordCB t)) = uB⁻¹ * wordCB t := by
  decide +kernel

theorem wordCB_pow_seven : ∀ t, wordCB t ^ 7 = 1 := by decide +kernel

/-! ## The vertex group `⟨c, a⟩ ≅ U₄(7)` -/

/-- The normal form `V'c^i V'a^j [V'c,V'a]^k [V'c,V'a,V'a]^l`. -/
def wordCA (t : ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7) : GL4 :=
  uC ^ t.1.val * uA ^ t.2.1.val * uCA ^ t.2.2.1.val * uCAA ^ t.2.2.2.val

/-- Its readout: `i = M₃₁`, `j = M₀₃`, `k = 6 M₀₁`, `l = 3 (M₀₂ + 6 M₀₁ − M₀₃ · 6 M₀₁)`. -/
def readCA (M : GL4) : ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7 :=
  (M.val 3 1, M.val 0 3, 6 * M.val 0 1,
    3 * (M.val 0 2 + 6 * M.val 0 1 - M.val 0 3 * (6 * M.val 0 1)))

theorem readCA_wordCA : ∀ t, readCA (wordCA t) = t := by decide +kernel

theorem wordCA_zero : wordCA 0 = 1 := by decide +kernel

theorem wordCA_uC_mul : ∀ t, wordCA (readCA (uC * wordCA t)) = uC * wordCA t := by
  decide +kernel

theorem wordCA_uC_inv_mul : ∀ t, wordCA (readCA (uC⁻¹ * wordCA t)) = uC⁻¹ * wordCA t := by
  decide +kernel

theorem wordCA_uA_mul : ∀ t, wordCA (readCA (uA * wordCA t)) = uA * wordCA t := by
  decide +kernel

theorem wordCA_uA_inv_mul : ∀ t, wordCA (readCA (uA⁻¹ * wordCA t)) = uA⁻¹ * wordCA t := by
  decide +kernel

theorem wordCA_pow_seven : ∀ t, wordCA t ^ 7 = 1 := by decide +kernel

/-- `(V'a V'b V'c)⁷ ≠ 1`: the product has order `42`. -/
theorem uABC_pow_seven_ne_one : (uA * uB * uC) ^ 7 ≠ 1 := by decide +kernel

/-! ## Every element of an image vertex group is a normal form -/

theorem exists_wordAB_of_mem_closure {x : GL4} (hx : x ∈ Subgroup.closure ({uA, uB} : Set GL4)) :
    ∃ t, x = wordAB t := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, wordAB_zero.symm⟩
  | mul_left g hg y _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases hg with rfl | rfl
    · exact ⟨readAB (uA * wordAB t), (wordAB_uA_mul t).symm⟩
    · exact ⟨readAB (uB * wordAB t), (wordAB_uB_mul t).symm⟩
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases hg with rfl | rfl
    · exact ⟨readAB (uA⁻¹ * wordAB t), (wordAB_uA_inv_mul t).symm⟩
    · exact ⟨readAB (uB⁻¹ * wordAB t), (wordAB_uB_inv_mul t).symm⟩

theorem exists_wordCB_of_mem_closure {x : GL4} (hx : x ∈ Subgroup.closure ({uC, uB} : Set GL4)) :
    ∃ t, x = wordCB t := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, wordCB_zero.symm⟩
  | mul_left g hg y _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases hg with rfl | rfl
    · exact ⟨readCB (uC * wordCB t), (wordCB_uC_mul t).symm⟩
    · exact ⟨readCB (uB * wordCB t), (wordCB_uB_mul t).symm⟩
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases hg with rfl | rfl
    · exact ⟨readCB (uC⁻¹ * wordCB t), (wordCB_uC_inv_mul t).symm⟩
    · exact ⟨readCB (uB⁻¹ * wordCB t), (wordCB_uB_inv_mul t).symm⟩

theorem exists_wordCA_of_mem_closure {x : GL4} (hx : x ∈ Subgroup.closure ({uC, uA} : Set GL4)) :
    ∃ t, x = wordCA t := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, wordCA_zero.symm⟩
  | mul_left g hg y _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases hg with rfl | rfl
    · exact ⟨readCA (uC * wordCA t), (wordCA_uC_mul t).symm⟩
    · exact ⟨readCA (uA * wordCA t), (wordCA_uA_mul t).symm⟩
  | inv_mul_cancel g hg y _ ih =>
    obtain ⟨t, rfl⟩ := ih
    rcases hg with rfl | rfl
    · exact ⟨readCA (uC⁻¹ * wordCA t), (wordCA_uC_inv_mul t).symm⟩
    · exact ⟨readCA (uA⁻¹ * wordCA t), (wordCA_uA_inv_mul t).symm⟩

/-! ## The image of a vertex group has exponent seven -/

theorem psi_mem_closure_ab {h : GHB 7} (hh : h ∈ Subgroup.closure {a 7, b 7}) :
    psi h ∈ Subgroup.closure ({uA, uB} : Set GL4) := by
  have h' := Subgroup.mem_map_of_mem psi hh
  rwa [MonoidHom.map_closure, Set.image_pair, psi_a, psi_b] at h'

theorem psi_mem_closure_cb {h : GHB 7} (hh : h ∈ Subgroup.closure {c 7, b 7}) :
    psi h ∈ Subgroup.closure ({uC, uB} : Set GL4) := by
  have h' := Subgroup.mem_map_of_mem psi hh
  rwa [MonoidHom.map_closure, Set.image_pair, psi_c, psi_b] at h'

theorem psi_mem_closure_ca {h : GHB 7} (hh : h ∈ Subgroup.closure {c 7, a 7}) :
    psi h ∈ Subgroup.closure ({uC, uA} : Set GL4) := by
  have h' := Subgroup.mem_map_of_mem psi hh
  rwa [MonoidHom.map_closure, Set.image_pair, psi_c, psi_a] at h'

/-- **The image of every vertex group has exponent seven.** -/
theorem psi_pow_seven_of_mem_vertex {h : GHB 7}
    (hh : h ∈ Subgroup.closure {a 7, b 7} ∨ h ∈ Subgroup.closure {c 7, b 7} ∨
      h ∈ Subgroup.closure {c 7, a 7}) : psi h ^ 7 = 1 := by
  rcases hh with hh | hh | hh
  · obtain ⟨t, ht⟩ := exists_wordAB_of_mem_closure (psi_mem_closure_ab hh)
    rw [ht]
    exact wordAB_pow_seven t
  · obtain ⟨t, ht⟩ := exists_wordCB_of_mem_closure (psi_mem_closure_cb hh)
    rw [ht]
    exact wordCB_pow_seven t
  · obtain ⟨t, ht⟩ := exists_wordCA_of_mem_closure (psi_mem_closure_ca hh)
    rw [ht]
    exact wordCA_pow_seven t

/-- **`GHB(7)` is infinite**, over CCKW Theorem 3.1(ii) in its cyclic case. -/
theorem infinite_ghb7 (hconj : CCKWFiniteOrderConjugateIntoVertex) : Infinite (GHB 7) := by
  by_contra hinf
  have hfin : Finite (GHB 7) := not_infinite_iff_finite.mp hinf
  obtain ⟨x, hx⟩ := hconj (a 7 * b 7 * c 7) (isOfFinOrder_of_finite _)
  have h7 := psi_pow_seven_of_mem_vertex hx
  have hmap : psi (x⁻¹ * (a 7 * b 7 * c 7) * x) = (psi x)⁻¹ * (uA * uB * uC) * psi x := by
    simp only [map_mul, map_inv, psi_a, psi_b, psi_c]
  rw [hmap] at h7
  exact uABC_pow_seven_ne_one (pow_eq_one_of_conj_pow_eq_one h7)

/-! ## Injectivity on the vertex groups, from the order bounds -/

theorem psi_u3ToAB_of_zero : psi (u3ToAB 7 (PresentedGroup.of 0)) = uA := by
  rw [u3ToAB, PresentedGroup.toGroup.of]
  exact psi_a

theorem psi_u3ToAB_of_one : psi (u3ToAB 7 (PresentedGroup.of 1)) = uB := by
  rw [u3ToAB, PresentedGroup.toGroup.of]
  exact psi_b

theorem psi_u4ToCB_of_zero : psi (u4ToCB 7 (PresentedGroup.of 0)) = uC := by
  rw [u4ToCB, PresentedGroup.toGroup.of]
  exact psi_c

theorem psi_u4ToCB_of_one : psi (u4ToCB 7 (PresentedGroup.of 1)) = uB := by
  rw [u4ToCB, PresentedGroup.toGroup.of]
  exact psi_b

theorem psi_u4ToCA_of_zero : psi (u4ToCA 7 (PresentedGroup.of 0)) = uC := by
  rw [u4ToCA, PresentedGroup.toGroup.of]
  exact psi_c

theorem psi_u4ToCA_of_one : psi (u4ToCA 7 (PresentedGroup.of 1)) = uA := by
  rw [u4ToCA, PresentedGroup.toGroup.of]
  exact psi_a

theorem wordAB_mem_range (t : ZMod 7 × ZMod 7 × ZMod 7) :
    wordAB t ∈ (psi.comp (u3ToAB 7)).range := by
  rw [MonoidHom.mem_range]
  refine ⟨(PresentedGroup.of 0 : U3 7) ^ t.1.val * (PresentedGroup.of 1 : U3 7) ^ t.2.1.val *
    comm (PresentedGroup.of 0 : U3 7) (PresentedGroup.of 1) ^ t.2.2.val, ?_⟩
  simp only [MonoidHom.comp_apply, map_mul, map_pow, GroupApproximation.KMSGroup.map_comm,
    psi_u3ToAB_of_zero, psi_u3ToAB_of_one]
  rfl

theorem wordCB_mem_range (t : ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7) :
    wordCB t ∈ (psi.comp (u4ToCB 7)).range := by
  rw [MonoidHom.mem_range]
  refine ⟨(PresentedGroup.of 0 : U4 7) ^ t.1.val * (PresentedGroup.of 1 : U4 7) ^ t.2.1.val *
    comm (PresentedGroup.of 0 : U4 7) (PresentedGroup.of 1) ^ t.2.2.1.val *
    comm3 (PresentedGroup.of 0 : U4 7) (PresentedGroup.of 1) (PresentedGroup.of 1) ^ t.2.2.2.val,
    ?_⟩
  simp only [MonoidHom.comp_apply, map_mul, map_pow, GroupApproximation.KMSGroup.map_comm,
    GroupApproximation.KMSGroup.map_comm3, psi_u4ToCB_of_zero, psi_u4ToCB_of_one]
  rfl

theorem wordCA_mem_range (t : ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7) :
    wordCA t ∈ (psi.comp (u4ToCA 7)).range := by
  rw [MonoidHom.mem_range]
  refine ⟨(PresentedGroup.of 0 : U4 7) ^ t.1.val * (PresentedGroup.of 1 : U4 7) ^ t.2.1.val *
    comm (PresentedGroup.of 0 : U4 7) (PresentedGroup.of 1) ^ t.2.2.1.val *
    comm3 (PresentedGroup.of 0 : U4 7) (PresentedGroup.of 1) (PresentedGroup.of 1) ^ t.2.2.2.val,
    ?_⟩
  simp only [MonoidHom.comp_apply, map_mul, map_pow, GroupApproximation.KMSGroup.map_comm,
    GroupApproximation.KMSGroup.map_comm3, psi_u4ToCA_of_zero, psi_u4ToCA_of_one]
  rfl

/-- A surjection from a finite group of order at most `N` onto a set containing `N`
distinct elements is injective. -/
theorem injective_of_card_le_of_injective_words {H : Type*} [Group H] [Finite H] {N : ℕ}
    {T : Type*} (f : H →* GL4) (w : T → GL4) (hw : ∀ t, w t ∈ f.range)
    (read : GL4 → T) (hread : ∀ t, read (w t) = t) (hT : Nat.card T = N)
    (hcard : Nat.card H ≤ N) : Function.Injective f := by
  have hword : Function.Injective (fun t : T => (⟨w t, hw t⟩ : f.range)) := by
    intro s t hst
    have h := congrArg (fun x : f.range => read (x : GL4)) hst
    simpa only [hread] using h
  have hle : N ≤ Nat.card f.range := by
    rw [← hT]
    exact Nat.card_le_card_of_injective _ hword
  have hbij := f.rangeRestrict_surjective.bijective_of_nat_card_le (hcard.trans hle)
  intro x y hxy
  exact hbij.1 (Subtype.ext hxy)

theorem injective_psi_comp_u3ToAB [Finite (U3 7)] (hcard : Nat.card (U3 7) ≤ 7 ^ 3) :
    Function.Injective (psi.comp (u3ToAB 7)) :=
  injective_of_card_le_of_injective_words _ wordAB wordAB_mem_range readAB readAB_wordAB
    (by simp [Nat.card_prod, Nat.card_zmod]) hcard

theorem injective_psi_comp_u4ToCB [Finite (U4 7)] (hcard : Nat.card (U4 7) ≤ 7 ^ 4) :
    Function.Injective (psi.comp (u4ToCB 7)) :=
  injective_of_card_le_of_injective_words _ wordCB wordCB_mem_range readCB readCB_wordCB
    (by simp [Nat.card_prod, Nat.card_zmod]) hcard

theorem injective_psi_comp_u4ToCA [Finite (U4 7)] (hcard : Nat.card (U4 7) ≤ 7 ^ 4) :
    Function.Injective (psi.comp (u4ToCA 7)) :=
  injective_of_card_le_of_injective_words _ wordCA wordCA_mem_range readCA readCA_wordCA
    (by simp [Nat.card_prod, Nat.card_zmod]) hcard

/-- **`ψ` kills no nontrivial element of a vertex group**, over the order bounds. -/
theorem eq_one_of_mem_vertex_of_psi_eq_one [Finite (U3 7)] [Finite (U4 7)]
    (h3 : Nat.card (U3 7) ≤ 7 ^ 3) (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {h : GHB 7}
    (hh : h ∈ Subgroup.closure {a 7, b 7} ∨ h ∈ Subgroup.closure {c 7, b 7} ∨
      h ∈ Subgroup.closure {c 7, a 7}) (h1 : psi h = 1) : h = 1 := by
  rcases hh with hh | hh | hh
  · rw [← range_u3ToAB] at hh
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hh
    have hy : y = 1 := injective_psi_comp_u3ToAB h3 (by simpa using h1)
    simp [hy]
  · rw [← range_u4ToCB] at hh
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hh
    have hy : y = 1 := injective_psi_comp_u4ToCB h4 (by simpa using h1)
    simp [hy]
  · rw [← range_u4ToCA] at hh
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hh
    have hy : y = 1 := injective_psi_comp_u4ToCA h4 (by simpa using h1)
    simp [hy]

/-! ## The kernel of `ψ` -/

/-- **`psiKer` is torsion-free**, over CCKW Theorem 3.1(ii) (cyclic case) and the order
bounds of the vertex groups. -/
theorem isPowerTorsionFree_psiKer (hconj : CCKWFiniteOrderConjugateIntoVertex)
    [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) : IsPowerTorsionFree ↥psiKer := by
  intro g n hn hgn
  have hgn' : (g : GHB 7) ^ n = 1 := by
    simpa using congrArg Subtype.val hgn
  obtain ⟨x, hx⟩ := hconj (g : GHB 7) (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hgn'⟩)
  have hg1 : psi (g : GHB 7) = 1 := MonoidHom.mem_ker.mp g.2
  have hpsi : psi (x⁻¹ * (g : GHB 7) * x) = 1 := by
    simp only [map_mul, map_inv, hg1, mul_one, inv_mul_cancel]
  exact Subtype.ext (eq_one_of_conj_eq_one (eq_one_of_mem_vertex_of_psi_eq_one h3 h4 hx hpsi))

/-- **`psiKer` is infinite**, being of finite index in the infinite group `GHB(7)`. -/
theorem infinite_psiKer (hconj : CCKWFiniteOrderConjugateIntoVertex) : Infinite ↥psiKer := by
  haveI := infinite_ghb7 hconj
  by_contra hinf
  have hfin : Finite ↥psiKer := not_infinite_iff_finite.mp hinf
  have h := Subgroup.card_mul_index psiKer
  rw [Nat.card_eq_zero_of_infinite (α := GHB 7)] at h
  have hS : Nat.card ↥psiKer ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
  exact mul_ne_zero hS (Subgroup.index_ne_zero_of_finite) h

end GHBQuotient
end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.readAB_wordAB
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.readCB_wordCB
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.readCA_wordCA
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.uABC_pow_seven_ne_one
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.psi_pow_seven_of_mem_vertex
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.infinite_ghb7
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.eq_one_of_mem_vertex_of_psi_eq_one
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.isPowerTorsionFree_psiKer
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.infinite_psiKer
