import GroupApproximation.BooneHigmanLinear.PaninAffine.TulX
import GroupApproximation.Meta.AxiomGuard
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Commutative algebra for Zariski patching (lane k2-panin, F.4)

This module holds the ring-level facts behind Tulenbaev's Prop 1.4(b) (`PaninAffine.Patching`).
* **Vectors under ring maps.** How `f ∘ -` meets `•`, `⬝ᵥ`, `*ᵥ` and `ᵥ*`. Also the coordinate
  ideal `I(v)` and how it changes under `M *ᵥ -`.
* **The Zariski square.** Here `A_a → A_{ab} ← A_b`, with `a, b` comaximal non-zero-divisors:
  - `zariski_pullback`: `A = A_a ×_{A_{ab}} A_b`;
  - `zariski_diff`: an element of `A_a` that equals `jb (aᴺ y)` lies in `ιa (aᴺ A)`;
  - `zariski_split`: every `c ∈ A_{ab}` is `ja c' + jb (aᴺ s)`, for every `N`, with a
    denominator bound `q` for `c'` that does not depend on `N`;
  - `ja_mul_jb`: a mixed product `ja c' · jb (a^q y)` lies in the image of `jb`.

Not root-wired.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace PaninAffine

open Matrix

section Vectors

variable {r : ℕ} {B C : Type*} [CommRing B] [CommRing C]

theorem comp_smul' (f : B →+* C) (c : B) (v : Fin r → B) : f ∘ (c • v) = f c • (f ∘ v) :=
  funext fun k => map_mul f c (v k)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.comp_smul'

theorem comp_add' (f : B →+* C) (v v' : Fin r → B) : f ∘ (v + v') = f ∘ v + f ∘ v' :=
  funext fun k => map_add f (v k) (v' k)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.comp_add'

theorem comp_dotProduct (f : B →+* C) (u v : Fin r → B) : (f ∘ u) ⬝ᵥ (f ∘ v) = f (u ⬝ᵥ v) :=
  (RingHom.map_dotProduct f u v).symm

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.comp_dotProduct

theorem comp_mulVec (f : B →+* C) (M : Matrix (Fin r) (Fin r) B) (v : Fin r → B) :
    f ∘ (M *ᵥ v) = f.mapMatrix M *ᵥ (f ∘ v) :=
  funext fun k => RingHom.map_mulVec f M v k

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.comp_mulVec

theorem comp_vecMul (f : B →+* C) (w : Fin r → B) (M : Matrix (Fin r) (Fin r) B) :
    f ∘ (w ᵥ* M) = (f ∘ w) ᵥ* f.mapMatrix M :=
  funext fun k => RingHom.map_vecMul f M w k

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.comp_vecMul

theorem comp_single_one (f : B →+* C) (k : Fin r) : f ∘ Pi.single k (1 : B) = Pi.single k 1 := by
  funext l
  by_cases h : l = k
  · subst h
    simp only [Function.comp_apply, Pi.single_eq_same, map_one]
  · simp only [Function.comp_apply, Pi.single_eq_of_ne h, map_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.comp_single_one

theorem comp_injective {f : B →+* C} (hf : Function.Injective f) :
    Function.Injective (fun v : Fin r → B => f ∘ v) :=
  fun _ _ h => funext fun k => hf (congrFun h k)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.comp_injective

theorem mapMatrix_injective {f : B →+* C} (hf : Function.Injective f) :
    Function.Injective (f.mapMatrix : Matrix (Fin r) (Fin r) B → Matrix (Fin r) (Fin r) C) :=
  fun _ _ h => Matrix.ext fun k l => hf (congrFun (congrFun h k) l)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.mapMatrix_injective

theorem dotProduct_mem_coordIdeal (u v : Fin r → B) : u ⬝ᵥ v ∈ coordIdeal v :=
  sum_mem fun k _ => Ideal.mul_mem_left _ (u k) (mem_coordIdeal k)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.dotProduct_mem_coordIdeal

theorem coordIdeal_mulVec_le (M : Matrix (Fin r) (Fin r) B) (v : Fin r → B) :
    coordIdeal (M *ᵥ v) ≤ coordIdeal v := by
  rw [coordIdeal, Ideal.span_le]
  rintro _ ⟨k, rfl⟩
  exact dotProduct_mem_coordIdeal (fun l => M k l) v

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.coordIdeal_mulVec_le

theorem mem_coordIdeal_mulVec {M M' : Matrix (Fin r) (Fin r) B} (h : M' * M = 1) {v : Fin r → B}
    {x : B} (hx : x ∈ coordIdeal v) : x ∈ coordIdeal (M *ᵥ v) := by
  have h1 : coordIdeal v = coordIdeal (M' *ᵥ (M *ᵥ v)) := by
    rw [mulVec_mulVec, h, one_mulVec]
  exact coordIdeal_mulVec_le M' (M *ᵥ v) (h1 ▸ hx)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.mem_coordIdeal_mulVec

end Vectors

section Zariski

variable {A : Type} [CommRing A]

/-- `A → A[1/x]`. -/
noncomputable abbrev loc (x : A) : A →+* Localization.Away x :=
  algebraMap A (Localization.Away x)

/-- `A_a → A_{ab}`. -/
noncomputable abbrev ja (a b : A) : Localization.Away a →+* Localization.Away (a * b) :=
  IsLocalization.Away.awayToAwayRight a b

/-- `A_b → A_{ab}`. -/
noncomputable abbrev jb (a b : A) : Localization.Away b →+* Localization.Away (a * b) :=
  IsLocalization.Away.awayToAwayLeft b a

variable {a b : A}

theorem ja_loc (x : A) : ja a b (loc a x) = loc (a * b) x :=
  IsLocalization.Away.awayToAwayRight_eq a b x

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.ja_loc

theorem jb_loc (x : A) : jb a b (loc b x) = loc (a * b) x :=
  IsLocalization.Away.awayToAwayLeft_eq b a x

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.jb_loc

theorem loc_injective {x : A} (hx : x ∈ nonZeroDivisors A) : Function.Injective (loc x) :=
  IsLocalization.injective (S := Localization.Away x) (M := Submonoid.powers x)
    (Submonoid.powers_le.mpr hx)

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.loc_injective

theorem isUnit_loc_self (x : A) : IsUnit (loc x x) :=
  IsLocalization.Away.algebraMap_isUnit x

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isUnit_loc_self

theorem isUnit_loc_left (a b : A) : IsUnit (loc (a * b) a) := by
  have h := isUnit_loc_self (a * b)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isUnit_loc_left

theorem isUnit_loc_right (a b : A) : IsUnit (loc (a * b) b) := by
  have h := isUnit_loc_self (a * b)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.isUnit_loc_right

/-- In `A_b`, multiplication by the image of a non-zero-divisor `a` is injective. -/
theorem loc_mul_left_injective (hb : b ∈ nonZeroDivisors A) (ha : a ∈ nonZeroDivisors A) (N : ℕ)
    {y y' : Localization.Away b} (h : loc b a ^ N * y = loc b a ^ N * y') : y = y' := by
  rw [← sub_eq_zero]
  have h0 : loc b a ^ N * (y - y') = 0 := by rw [mul_sub, h, sub_self]
  obtain ⟨n, z, hz⟩ := IsLocalization.Away.surj b (y - y')
  have h1 : loc b (a ^ N * z) = 0 := by
    rw [map_mul, map_pow, ← hz, ← mul_assoc, h0, zero_mul]
  have h2 : a ^ N * z = 0 := loc_injective hb (h1.trans (map_zero _).symm)
  have h3 : z = 0 :=
    (mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem ha N)).mp (by rw [mul_comm]; exact h2)
  rw [h3, map_zero] at hz
  exact ((isUnit_loc_self b).pow n).mul_left_eq_zero.mp hz

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.loc_mul_left_injective

/-- **`A = A_a ×_{A_{ab}} A_b`.** -/
theorem zariski_pullback (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (hab : IsCoprime a b) {z : Localization.Away a} {z' : Localization.Away b}
    (h : ja a b z = jb a b z') : ∃ l : A, z = loc a l ∧ z' = loc b l := by
  obtain ⟨n, κ, hz⟩ := IsLocalization.Away.surj a z
  obtain ⟨m, ν, hz'⟩ := IsLocalization.Away.surj b z'
  have hL : Function.Injective (loc (a * b)) := loc_injective (mul_mem ha hb)
  have e1 : ja a b z * loc (a * b) a ^ n = loc (a * b) κ := by
    rw [← ja_loc, ← ja_loc, ← map_pow, ← map_mul, hz]
  have e2 : jb a b z' * loc (a * b) b ^ m = loc (a * b) ν := by
    rw [← jb_loc, ← jb_loc, ← map_pow, ← map_mul, hz']
  have e3 : κ * b ^ m = ν * a ^ n := by
    apply hL
    rw [map_mul, map_mul, map_pow, map_pow, ← e1, ← e2, h]
    ring
  obtain ⟨x, y, hxy⟩ := (hab.pow (m := n) (n := m))
  refine ⟨x * κ + y * ν, ?_, ?_⟩
  · have hk : κ = a ^ n * (x * κ + y * ν) := by
      linear_combination (-κ) * hxy + y * e3
    rw [hk, map_mul, map_pow] at hz
    rw [mul_comm (loc a a ^ n)] at hz
    exact ((isUnit_loc_self a).pow n).mul_left_inj.mp hz
  · have hn : ν = b ^ m * (x * κ + y * ν) := by
      linear_combination (-ν) * hxy - x * e3
    rw [hn, map_mul, map_pow] at hz'
    rw [mul_comm (loc b b ^ m)] at hz'
    exact ((isUnit_loc_self b).pow m).mul_left_inj.mp hz'

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.zariski_pullback

/-- In `A_b`: if `ιb l = aᴺ y`, then `l = aᴺ μ` and `y = ιb μ`. -/
theorem zariski_div (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (hab : IsCoprime a b) {l : A} {N : ℕ} {y : Localization.Away b}
    (h : loc b l = loc b a ^ N * y) : ∃ μ : A, l = a ^ N * μ ∧ y = loc b μ := by
  obtain ⟨m, ν, hy⟩ := IsLocalization.Away.surj b y
  have e1 : l * b ^ m = a ^ N * ν := by
    apply loc_injective hb
    rw [map_mul, map_mul, map_pow, map_pow, h, mul_assoc, hy]
  obtain ⟨x, x', hxx⟩ := (hab.pow (m := N) (n := m))
  refine ⟨x * l + x' * ν, ?_, ?_⟩
  · linear_combination (-l) * hxx + x' * e1
  · have e2 : ((x * l + x' * ν) * b ^ m - ν) * a ^ N = 0 := by
      linear_combination (x * a ^ N) * e1 + (a ^ N * ν) * hxx
    have e3 : (x * l + x' * ν) * b ^ m = ν :=
      sub_eq_zero.mp ((mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem ha N)).mp e2)
    have e4 : loc b (x * l + x' * ν) * loc b b ^ m = y * loc b b ^ m := by
      rw [hy, ← map_pow, ← map_mul, e3]
    exact ((isUnit_loc_self b).pow m).mul_left_inj.mp e4.symm

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.zariski_div

/-- **Differences of splittings.** If `ja z = jb (aᴺ y)` then `z = ιa (aᴺ μ)` and `y = ιb μ`. -/
theorem zariski_diff (ha : a ∈ nonZeroDivisors A) (hb : b ∈ nonZeroDivisors A)
    (hab : IsCoprime a b) {z : Localization.Away a} {N : ℕ} {y : Localization.Away b}
    (h : ja a b z = jb a b (loc b a ^ N * y)) :
    ∃ μ : A, z = loc a (a ^ N * μ) ∧ y = loc b μ := by
  obtain ⟨l, hz, hl⟩ := zariski_pullback ha hb hab h
  obtain ⟨μ, rfl, hy⟩ := zariski_div ha hb hab hl.symm
  exact ⟨μ, hz, hy⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.zariski_diff

/-- **Splitting along `A_a + A_b = A_{ab}`.** For `c ∈ A_{ab}` there is `q` such that, for every
`N`, `c = ja c' + jb (aᴺ s)` with `c' aᵠ ∈ ιa(A)`. -/
theorem zariski_split (hab : IsCoprime a b) (c : Localization.Away (a * b)) :
    ∃ q : ℕ, ∀ N : ℕ, ∃ (c' : Localization.Away a) (s : Localization.Away b) (κ : A),
      c = ja a b c' + jb a b (loc b a ^ N * s) ∧ c' * loc a a ^ q = loc a κ := by
  obtain ⟨k, l, hl⟩ := IsLocalization.Away.surj (a * b) c
  refine ⟨k, fun N => ?_⟩
  obtain ⟨x, y, hxy⟩ := (hab.pow (m := N + k) (n := k))
  set ua : Localization.Away a := ↑(isUnit_loc_self a).unit⁻¹
  set ub : Localization.Away b := ↑(isUnit_loc_self b).unit⁻¹
  have hua1 : ua * loc a a = 1 := (isUnit_loc_self a).val_inv_mul
  have hub1 : ub * loc b b = 1 := (isUnit_loc_self b).val_inv_mul
  refine ⟨loc a (l * y) * ua ^ k, loc b (l * x) * ub ^ k, l * y, ?_, ?_⟩
  · have hU : ja a b ua ^ k * loc (a * b) a ^ k = 1 := by
      rw [← mul_pow, ← ja_loc, ← map_mul, hua1, map_one, one_pow]
    have hW : jb a b ub ^ k * loc (a * b) b ^ k = 1 := by
      rw [← mul_pow, ← jb_loc, ← map_mul, hub1, map_one, one_pow]
    have hx1 : loc (a * b) x * loc (a * b) a ^ (N + k) + loc (a * b) y * loc (a * b) b ^ k = 1 := by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_add, hxy, map_one]
    have hl' : c * (loc (a * b) a * loc (a * b) b) ^ k = loc (a * b) l := by
      rw [← map_mul, hl]
    have hu : IsUnit ((loc (a * b) a * loc (a * b) b) ^ k) :=
      ((isUnit_loc_left a b).mul (isUnit_loc_right a b)).pow k
    apply hu.mul_left_inj.mp
    simp only [map_mul, map_pow, ja_loc, jb_loc]
    linear_combination hl' - (loc (a * b) l * loc (a * b) y * loc (a * b) b ^ k) * hU
      - (loc (a * b) l * loc (a * b) x * loc (a * b) a ^ (N + k)) * hW
      - loc (a * b) l * hx1
  · rw [mul_assoc, ← mul_pow, hua1, one_pow, mul_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.zariski_split

/-- **A mixed product.** If `c' aᵠ = ιa κ`, then `ja c' · jb (aᵠ y) = jb (ιb κ · y)`. -/
theorem ja_mul_jb {c' : Localization.Away a} {q : ℕ} {κ : A} (hc : c' * loc a a ^ q = loc a κ)
    (y : Localization.Away b) :
    ja a b c' * jb a b (loc b a ^ q * y) = jb a b (loc b κ * y) := by
  have h1 : ja a b c' * loc (a * b) a ^ q = loc (a * b) κ := by
    rw [← ja_loc, ← ja_loc, ← map_pow, ← map_mul, hc]
  rw [map_mul, map_mul, map_pow, jb_loc, jb_loc, ← mul_assoc, h1]

#audit_axioms GroupApproximation.BooneHigmanLinear.PaninAffine.ja_mul_jb

end Zariski

end PaninAffine
end BooneHigmanLinear
end GroupApproximation
