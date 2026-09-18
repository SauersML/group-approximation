import GroupApproximation.GroupTheory.LevelCommutatorWords
import Mathlib.Data.Countable.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.Tactic.Linarith
import GroupApproximation.Meta.AxiomGuard

/-!
# Every countable group lies in the commutator subgroup of a 2-generated infinite group

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row `fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

This file is the first half of the route to the first and third clauses. The second half, the
host `G_Δ`, is in `SimpleHosts/Host.lean`. The route is the Neumann–Neumann embedding, in the
level-and-power-of-2 form the manuscript prints for LEF groups (tex l.336–348,
`GroupTheory/LevelCommutatorWords.lean`). Here the finite moduli are replaced by `ℤ`, so no LEF
input is needed.

## Plan

For a group `G` and an enumeration `g : ℕ → G` hitting every element at some index `j ≥ 1`:

* `tPermZ` adds `1` to the level of `G × ℤ`, and `fPermZ x` multiplies the first coordinate of
  `(y, i)` by `x ^ i`. Then `⁅fPermZ x, tPermZ⁆` multiplies the first coordinate by `x`
  (`commutator_fPermZ_tPermZ`).
* On `(G × ℤ) × ℤ`, `bPermZ` adds `1` to the last coordinate. `aPermZ` acts on the level `2^r`,
  `r ≥ 1`, by `fPermZ (g j)` if `r = 2j − 1` and by `tPermZ` if `r = 2j`, and trivially on the
  other levels. `b^{−n} a b^n` acts on the level `i` as `a` acts on the level `i + n`
  (`conjPow_aPermZ_bPermZ`).
* Distinct pairs of powers of `2` have distinct differences (`two_pow_sub_two_pow_inj`), so
  `w_j(a, b)` is `levelZeroMulZ (g j)`: it multiplies the first coordinate by `g j` on the
  level `0` and acts trivially elsewhere (`level_difference_zeroZ`, `word_aPermZ_bPermZ`).
* `levelZeroMulZ` is an injective homomorphism `G →* Perm ((G × ℤ) × ℤ)` (`levelZeroHom`).
  Its image lies in `[Δ, Δ]` for `Δ = ⟨a, b⟩`, as every element is some `g j` and
  `w_j` is a commutator of two elements of `Δ`.
* `exists_twoGenerated_commutator_embedding`: apply this to `G = Γ × ℤ` for a countable `Γ`,
  so that `Δ` is infinite as well as `2`-generated.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace SimpleHosts
namespace NeumannNeumann

open Equiv LevelCommutatorWords
open scoped commutatorElement

section Letters

variable (G : Type*) [Group G]

/-- `t`: add `1` to the level of `G × ℤ`. -/
def tPermZ : Perm (G × ℤ) :=
  shift 1

/-- `f_x`: multiply the first coordinate of `(y, i)` from the left by `x ^ i`. -/
def fPermZ (x : G) : Perm (G × ℤ) :=
  levelwise fun i : ℤ => Equiv.mulLeft (x ^ i)

/-- **`[f_x, t]` multiplies the first coordinate by `x`.** -/
theorem commutator_fPermZ_tPermZ (x : G) :
    ⁅fPermZ G x, tPermZ G⁆ = levelwise fun _ : ℤ => Equiv.mulLeft x := by
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  refine Equiv.ext fun z => Prod.ext ?_ rfl
  simp only [Perm.mul_apply, fPermZ, tPermZ, levelwise_apply, shift_apply, Equiv.coe_mulLeft]
  rw [← mul_assoc, ← zpow_one_add, add_comm]

end Letters

/-! ## Levels -/

/-- The level `v` is `2^r` with `1 ≤ r`, so it carries a letter of `a`. -/
abbrev IsLevelZ (v : ℤ) : Prop :=
  1 ≤ Nat.log 2 v.toNat ∧ v = ((2 ^ Nat.log 2 v.toNat : ℕ) : ℤ)

theorem isLevelZ_exists {v : ℤ} (h : IsLevelZ v) : ∃ r : ℕ, 1 ≤ r ∧ v = ((2 ^ r : ℕ) : ℤ) :=
  ⟨Nat.log 2 v.toNat, h.1, h.2⟩

theorem isLevelZ_two_pow {r : ℕ} (h1 : 1 ≤ r) : IsLevelZ ((2 ^ r : ℕ) : ℤ) := by
  have h := Nat.log_pow (by norm_num : 1 < 2) r
  refine ⟨?_, ?_⟩
  · rw [Int.toNat_natCast, h]
    exact h1
  · rw [Int.toNat_natCast, h]

/-- **The difference argument**: if the levels `i + 2^{2j−1}` and `i + 4^j` both carry letters,
then `i = 0`. Over `ℤ` there is no modulus, so no bound on the levels is needed. -/
theorem level_difference_zeroZ {j : ℕ} (hj : 1 ≤ j) {i : ℤ}
    (hx : IsLevelZ (i + ((2 ^ (2 * j - 1) : ℕ) : ℤ)))
    (hy : IsLevelZ (i + ((2 ^ (2 * j) : ℕ) : ℤ))) : i = 0 := by
  obtain ⟨r, -, hxv⟩ := isLevelZ_exists hx
  obtain ⟨s, -, hyv⟩ := isLevelZ_exists hy
  push_cast at hxv hyv
  have hZ : ((2 ^ s + 2 ^ (2 * j - 1) : ℕ) : ℤ) = ((2 ^ (2 * j) + 2 ^ r : ℕ) : ℤ) := by
    push_cast
    linarith
  have heq : 2 ^ s + 2 ^ (2 * j - 1) = 2 ^ (2 * j) + 2 ^ r := Nat.cast_injective hZ
  have hpq : 2 ^ (2 * j) = 2 ^ (2 * j - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hp1 : 1 ≤ 2 ^ (2 * j - 1) := Nat.one_le_two_pow
  have hrs : 2 ^ r < 2 ^ s := by omega
  have hrs' : r < s := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hrs
  have hdiff : 2 ^ s - 2 ^ r = 2 ^ (2 * j) - 2 ^ (2 * j - 1) := by omega
  obtain ⟨hr, -⟩ := two_pow_sub_two_pow_inj r s (2 * j - 1) (2 * j) hrs' (by omega) hdiff
  subst hr
  linarith

/-! ## Letters on levels -/

section Words

variable (G : Type*) [Group G] (g : ℕ → G)

/-- The letter on the level `2^r`: `f_{g j}` if `r = 2j − 1`, and `t` if `r = 2j`. -/
def letterZ (r : ℕ) : Perm (G × ℤ) :=
  if Even r then tPermZ G else fPermZ G (g ((r + 1) / 2))

theorem letterZ_odd {j : ℕ} (hj : 1 ≤ j) : letterZ G g (2 * j - 1) = fPermZ G (g j) := by
  have h1 : ¬ Even (2 * j - 1) := by rw [Nat.even_iff]; omega
  have h2 : (2 * j - 1 + 1) / 2 = j := by omega
  rw [letterZ, if_neg h1, h2]

theorem letterZ_even (j : ℕ) : letterZ G g (2 * j) = tPermZ G := by
  rw [letterZ, if_pos (even_two_mul j)]

/-- `a` on the level `i`: the letter on the levels `2^r`, `r ≥ 1`, and trivial elsewhere. -/
def levelActionZ (i : ℤ) : Perm (G × ℤ) :=
  if IsLevelZ i then letterZ G g (Nat.log 2 i.toNat) else 1

/-- `a` on `(G × ℤ) × ℤ`. -/
def aPermZ : Perm ((G × ℤ) × ℤ) :=
  levelwise (levelActionZ G g)

/-- `b`: add `1` to the last coordinate. -/
def bPermZ : Perm ((G × ℤ) × ℤ) :=
  shift 1

/-- Multiply the first coordinate on the level `0` by `x`, and act trivially elsewhere. -/
def levelZeroMulZ (x : G) : Perm ((G × ℤ) × ℤ) :=
  levelwise fun i : ℤ => if i = 0 then levelwise (fun _ : ℤ => Equiv.mulLeft x) else 1

theorem levelZeroMulZ_mul (x y : G) :
    levelZeroMulZ G (x * y) = levelZeroMulZ G x * levelZeroMulZ G y := by
  refine Equiv.ext fun z => ?_
  by_cases hi : z.2 = 0
  · simp [levelZeroMulZ, hi, Equiv.coe_mulLeft, mul_assoc]
  · simp [levelZeroMulZ, hi]

theorem eq_one_of_levelZeroMulZ_eq_one {x : G} (h : levelZeroMulZ G x = 1) : x = 1 := by
  have h1 := Equiv.congr_fun h ((1, 0), 0)
  simpa [levelZeroMulZ, Equiv.coe_mulLeft] using congrArg (fun z => z.1.1) h1

theorem levelActionZ_two_pow {r : ℕ} (h1 : 1 ≤ r) :
    levelActionZ G g ((2 ^ r : ℕ) : ℤ) = letterZ G g r := by
  rw [levelActionZ, if_pos (isLevelZ_two_pow h1), Int.toNat_natCast,
    Nat.log_pow (by norm_num : 1 < 2)]

theorem levelActionZ_eq_one {i : ℤ} (h : ¬ IsLevelZ i) : levelActionZ G g i = 1 := by
  rw [levelActionZ, if_neg h]

/-- **`b^{−n} a b^n` acts on the level `i` as `a` acts on the level `i + n`.** -/
theorem conjPow_aPermZ_bPermZ (n : ℕ) :
    conjPow (aPermZ G g) (bPermZ G) n = levelwise fun i => levelActionZ G g (i + (n : ℤ)) := by
  rw [conjPow, bPermZ, shift_pow, Nat.smul_one_eq_cast, aPermZ, shift_inv_mul_levelwise_mul_shift]

/-- The commutator of the two conjugates on the level `i`. -/
theorem levelActionZ_commutator {j : ℕ} (hj : 1 ≤ j) (i : ℤ) :
    ⁅levelActionZ G g (i + ((2 ^ (2 * j - 1) : ℕ) : ℤ)),
      levelActionZ G g (i + ((2 ^ (2 * j) : ℕ) : ℤ))⁆ =
      if i = 0 then levelwise (fun _ : ℤ => Equiv.mulLeft (g j)) else 1 := by
  by_cases hi : i = 0
  · rw [if_pos hi, hi, zero_add, zero_add,
      levelActionZ_two_pow G g (r := 2 * j - 1) (by omega),
      levelActionZ_two_pow G g (r := 2 * j) (by omega), letterZ_odd G g hj,
      letterZ_even G g j, commutator_fPermZ_tPermZ]
  · rw [if_neg hi]
    by_cases hx : IsLevelZ (i + ((2 ^ (2 * j - 1) : ℕ) : ℤ))
    · by_cases hy : IsLevelZ (i + ((2 ^ (2 * j) : ℕ) : ℤ))
      · exact absurd (level_difference_zeroZ hj hx hy) hi
      · rw [levelActionZ_eq_one G g hy, commutatorElement_one_right]
    · rw [levelActionZ_eq_one G g hx, commutatorElement_one_left]

/-- **`w_j(a, b)` multiplies the first coordinate by `g j` on the level `0` and acts trivially
elsewhere.** -/
theorem word_aPermZ_bPermZ {j : ℕ} (hj : 1 ≤ j) :
    word j (aPermZ G g) (bPermZ G) = levelZeroMulZ G (g j) := by
  rw [word, conjPow_aPermZ_bPermZ, conjPow_aPermZ_bPermZ, levelwise_commutator, four_pow_eq j]
  exact congrArg levelwise (funext fun i => levelActionZ_commutator G g hj i)

end Words

/-! ## The embedding into `[Δ, Δ]` -/

section Embedding

variable (G : Type) [Group G] (g : ℕ → G)

/-- `x ↦ levelZeroMulZ x`, as a homomorphism. -/
def levelZeroHom : G →* Perm ((G × ℤ) × ℤ) :=
  MonoidHom.mk' (levelZeroMulZ G) (levelZeroMulZ_mul G)

theorem levelZeroHom_injective : Function.Injective (levelZeroHom G) :=
  (injective_iff_map_eq_one _).2 fun _ hx => eq_one_of_levelZeroMulZ_eq_one G hx

/-- `Δ`, the subgroup generated by `a` and `b`. -/
def Delta : Subgroup (Perm ((G × ℤ) × ℤ)) :=
  Subgroup.closure {aPermZ G g, bPermZ G}

theorem conjPow_mem_delta (n : ℕ) : conjPow (aPermZ G g) (bPermZ G) n ∈ Delta G g := by
  have ha : aPermZ G g ∈ Delta G g := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : bPermZ G ∈ Delta G g := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  unfold conjPow
  exact (Delta G g).mul_mem ((Delta G g).mul_mem ((Delta G g).inv_mem ((Delta G g).pow_mem hb n)) ha)
    ((Delta G g).pow_mem hb n)

theorem levelZeroHom_mem_delta (hsurj : ∀ x : G, ∃ j, 1 ≤ j ∧ g j = x) (x : G) :
    levelZeroHom G x ∈ Delta G g := by
  obtain ⟨j, hj, rfl⟩ := hsurj x
  have hp := conjPow_mem_delta G g (2 ^ (2 * j - 1))
  have hq := conjPow_mem_delta G g (4 ^ j)
  have he : levelZeroHom G (g j) = ⁅conjPow (aPermZ G g) (bPermZ G) (2 ^ (2 * j - 1)),
      conjPow (aPermZ G g) (bPermZ G) (4 ^ j)⁆ :=
    (word_aPermZ_bPermZ G g hj).symm
  rw [he, commutatorElement_def]
  exact (Delta G g).mul_mem ((Delta G g).mul_mem ((Delta G g).mul_mem hp hq) ((Delta G g).inv_mem hp))
    ((Delta G g).inv_mem hq)

/-- The homomorphism into `Δ`. -/
def embeddingΔ (hsurj : ∀ x : G, ∃ j, 1 ≤ j ∧ g j = x) : G →* Delta G g :=
  (levelZeroHom G).codRestrict (Delta G g) (levelZeroHom_mem_delta G g hsurj)

theorem embeddingΔ_injective (hsurj : ∀ x : G, ∃ j, 1 ≤ j ∧ g j = x) :
    Function.Injective (embeddingΔ G g hsurj) :=
  fun _ _ h => levelZeroHom_injective G (congrArg Subtype.val h)

/-- **`G ≤ [Δ, Δ]`**: every element is some `g j`, and `w_j(a, b)` is a commutator in `Δ`. -/
theorem embeddingΔ_mem_commutator (hsurj : ∀ x : G, ∃ j, 1 ≤ j ∧ g j = x) (x : G) :
    embeddingΔ G g hsurj x ∈ commutator (Delta G g) := by
  obtain ⟨j, hj, rfl⟩ := hsurj x
  have hp := conjPow_mem_delta G g (2 ^ (2 * j - 1))
  have hq := conjPow_mem_delta G g (4 ^ j)
  have he : embeddingΔ G g hsurj (g j) = ⁅(⟨_, hp⟩ : Delta G g), ⟨_, hq⟩⁆ :=
    Subtype.ext (word_aPermZ_bPermZ G g hj).symm
  rw [he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end Embedding

/-- **Neumann–Neumann without LEF**: a countable group `Γ` embeds in the commutator subgroup of an
infinite `2`-generated group. The enumeration is of `Γ × ℤ`, so that `Δ` is infinite. -/
theorem exists_twoGenerated_commutator_embedding (Γ : Type) [Group Γ] [Countable Γ] :
    ∃ (Δ : Type) (_ : Group Δ), Infinite Δ ∧ Group.FG Δ ∧
      ∃ f : Γ →* Δ, Function.Injective f ∧ ∀ γ, f γ ∈ commutator Δ := by
  haveI : Countable (Multiplicative ℤ) := inferInstanceAs (Countable ℤ)
  haveI : Infinite (Multiplicative ℤ) := inferInstanceAs (Infinite ℤ)
  obtain ⟨e, he⟩ := exists_surjective_nat (Γ × Multiplicative ℤ)
  have hsurj : ∀ x : Γ × Multiplicative ℤ, ∃ j, 1 ≤ j ∧ e (j - 1) = x := fun x => by
    obtain ⟨n, rfl⟩ := he x
    exact ⟨n + 1, Nat.le_add_left 1 n, by rw [Nat.add_sub_cancel]⟩
  have hinr : Function.Injective (MonoidHom.inr Γ (Multiplicative ℤ)) :=
    fun _ _ h => congrArg Prod.snd h
  have hinl : Function.Injective (MonoidHom.inl Γ (Multiplicative ℤ)) :=
    fun _ _ h => congrArg Prod.fst h
  refine ⟨Delta (Γ × Multiplicative ℤ) (fun j => e (j - 1)), inferInstance,
    Infinite.of_injective _ ((embeddingΔ_injective _ (fun j => e (j - 1)) hsurj).comp hinr),
    Group.closure_finite_fg _,
    (embeddingΔ _ (fun j => e (j - 1)) hsurj).comp (MonoidHom.inl Γ (Multiplicative ℤ)),
    (embeddingΔ_injective _ (fun j => e (j - 1)) hsurj).comp hinl,
    fun γ => embeddingΔ_mem_commutator _ (fun j => e (j - 1)) hsurj
      (MonoidHom.inl Γ (Multiplicative ℤ) γ)⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.NeumannNeumann.exists_twoGenerated_commutator_embedding
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.NeumannNeumann.commutator_fPermZ_tPermZ
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.NeumannNeumann.level_difference_zeroZ
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.NeumannNeumann.word_aPermZ_bPermZ
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.NeumannNeumann.levelZeroHom_injective
#audit_axioms GroupApproximation.SimpleKazhdanSofic.SimpleHosts.NeumannNeumann.embeddingΔ_mem_commutator

end NeumannNeumann
end SimpleHosts
end SimpleKazhdanSofic
end GroupApproximation
