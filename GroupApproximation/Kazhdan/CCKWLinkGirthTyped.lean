import Mathlib.Tactic.LinearCombination
import GroupApproximation.Kazhdan.CCKWLinkRelations

/-!
# The links of the coset complex of `GHB(7)` have girths `6, 8, 8`

The Kac–Moody–Steinberg group `GHB(7)` is the fundamental group of a triangle of groups
with vertex groups `P₀ = ⟨a,b⟩ ≅ U₃(7)`, `P₁ = ⟨c,b⟩ ≅ U₄(7)`, `P₂ = ⟨c,a⟩ ≅ U₄(7)`
(Caprace–Conder–Kaluba–Witzel, arXiv:2011.09276, Theorem 1.3).  In the coset complex, the
link of a vertex of type `i` is the coset graph of `Pᵢ` with respect to its two edge
groups `A = Pᵢ ⊓ Pⱼ` and `B = Pᵢ ⊓ Pₖ`: its vertices are the cosets `pA` and `pB`, and every
`p ∈ Pᵢ` is an edge from `pA` to `pB`.  The graph is bipartite by type.  A cycle of length
`2m` spells a relation `x₁ y₁ ⋯ xₘ yₘ = 1` with every `xₖ ∈ A` and `yₖ ∈ B` nontrivial, and
such a relation spells a closed walk of length `2m` without backtracking, which contains a
cycle of length at most `2m`.  So the link has girth at least `g` exactly when there is no
such relation with `2m < g` (`LinkGirthAtLeast`).

This module proves the typed statement CCKW Theorem 3.1 uses: the link at the `U₃(7)`
vertices has girth at least `6`, and the links at the two `U₄(7)` vertex types have girth
at least `8` (`CCKWLinkGirths`), over the order bounds `|U₃(7)| ≤ 7³`, `|U₄(7)| ≤ 7⁴`.
Lengths two and six are added here to the length-four relations of
`Kazhdan/CCKWLinkRelations.lean`, by the same route through `ψ : GHB(7) → GL₄(F₇)`.
-/

namespace GroupApproximation
namespace KMSGroup

/-- **The three vertex groups of `GHB(7)`**: `P₀ = ⟨a,b⟩`, `P₁ = ⟨c,b⟩`, `P₂ = ⟨c,a⟩`. -/
def vertexGroup : Fin 3 → Subgroup (GHB 7) :=
  ![Subgroup.closure {a 7, b 7}, Subgroup.closure {c 7, b 7}, Subgroup.closure {c 7, a 7}]

/-- **No alternating relation of length `2m`** between subgroups `A` and `B`: no product
`x₁ y₁ ⋯ xₘ yₘ = 1` with every `xₖ ∈ A` and every `yₖ ∈ B` nontrivial. -/
def NoAlternatingRelation {G : Type*} [Group G] (A B : Subgroup G) (m : ℕ) : Prop :=
  ∀ x y : Fin m → G, (∀ k, x k ∈ A) → (∀ k, y k ∈ B) → (∀ k, x k ≠ 1) → (∀ k, y k ≠ 1) →
    (List.ofFn fun k => x k * y k).prod ≠ 1

/-- **The coset graph of a vertex group with respect to its edge groups `A`, `B` has girth at
least `g`**: no alternating relation of length `2m < g`. -/
def LinkGirthAtLeast {G : Type*} [Group G] (A B : Subgroup G) (g : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → 2 * m < g → NoAlternatingRelation A B m

/-- **The typed link girths of `GHB(7)`**: `6` at the `U₃(7)` vertices, `8` at both `U₄(7)`
vertex types. -/
def CCKWLinkGirths : Prop :=
  LinkGirthAtLeast (vertexGroup 0 ⊓ vertexGroup 1) (vertexGroup 0 ⊓ vertexGroup 2) 6 ∧
    LinkGirthAtLeast (vertexGroup 1 ⊓ vertexGroup 0) (vertexGroup 1 ⊓ vertexGroup 2) 8 ∧
      LinkGirthAtLeast (vertexGroup 2 ⊓ vertexGroup 0) (vertexGroup 2 ⊓ vertexGroup 1) 8

namespace GHBQuotient

/-! ## Nonzero parameters of nontrivial edge-group elements -/

theorem ne_zero_of_matAB_b [Finite (U3 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3) {z : GHB 7}
    {j : ZMod 7} (hz : z ∈ Subgroup.closure {a 7, b 7}) (hz1 : z ≠ 1)
    (ht : (psi z : Mat) = matAB (0, j, 0)) : j ≠ 0 := by
  intro hj
  apply psi_ne_one_of_mem_ab h3 hz hz1
  apply Units.ext
  rw [ht, hj]
  exact matAB_zero

theorem ne_zero_of_matAB_a [Finite (U3 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3) {z : GHB 7}
    {i : ZMod 7} (hz : z ∈ Subgroup.closure {a 7, b 7}) (hz1 : z ≠ 1)
    (ht : (psi z : Mat) = matAB (i, 0, 0)) : i ≠ 0 := by
  intro hi
  apply psi_ne_one_of_mem_ab h3 hz hz1
  apply Units.ext
  rw [ht, hi]
  exact matAB_zero

theorem ne_zero_of_matCB_b [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {z : GHB 7}
    {j : ZMod 7} (hz : z ∈ Subgroup.closure {c 7, b 7}) (hz1 : z ≠ 1)
    (ht : (psi z : Mat) = matCB (0, j, 0, 0)) : j ≠ 0 := by
  intro hj
  apply psi_ne_one_of_mem_cb h4 hz hz1
  apply Units.ext
  rw [ht, hj]
  exact matCB_zero

theorem ne_zero_of_matCB_c [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {z : GHB 7}
    {i : ZMod 7} (hz : z ∈ Subgroup.closure {c 7, b 7}) (hz1 : z ≠ 1)
    (ht : (psi z : Mat) = matCB (i, 0, 0, 0)) : i ≠ 0 := by
  intro hi
  apply psi_ne_one_of_mem_cb h4 hz hz1
  apply Units.ext
  rw [ht, hi]
  exact matCB_zero

theorem ne_zero_of_matCA_a [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {z : GHB 7}
    {j : ZMod 7} (hz : z ∈ Subgroup.closure {c 7, a 7}) (hz1 : z ≠ 1)
    (ht : (psi z : Mat) = matCA (0, j, 0, 0)) : j ≠ 0 := by
  intro hj
  apply psi_ne_one_of_mem_ca h4 hz hz1
  apply Units.ext
  rw [ht, hj]
  exact matCA_zero

theorem ne_zero_of_matCA_c [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {z : GHB 7}
    {i : ZMod 7} (hz : z ∈ Subgroup.closure {c 7, a 7}) (hz1 : z ≠ 1)
    (ht : (psi z : Mat) = matCA (i, 0, 0, 0)) : i ≠ 0 := by
  intro hi
  apply psi_ne_one_of_mem_ca h4 hz hz1
  apply Units.ext
  rw [ht, hi]
  exact matCA_zero

/-! ## The parameter laws: lengths two and six -/

theorem mulAB_alternating2_ne_zero : ∀ j i : ZMod 7, j ≠ 0 → i ≠ 0 →
    mulAB (0, j, 0) (i, 0, 0) ≠ 0 := by
  decide +kernel

theorem mulCB_alternating2_ne_zero : ∀ j i : ZMod 7, j ≠ 0 → i ≠ 0 →
    mulCB (0, j, 0, 0) (i, 0, 0, 0) ≠ 0 := by
  decide +kernel

theorem mulCA_alternating2_ne_zero : ∀ j i : ZMod 7, j ≠ 0 → i ≠ 0 →
    mulCA (0, j, 0, 0) (i, 0, 0, 0) ≠ 0 := by
  decide +kernel

/-- Length six at `⟨c,b⟩`, with the last two parameters forced by the first two coordinates
of the relation. -/
theorem mulCB_alternating6_ne_zero : ∀ j₁ i₁ j₂ i₂ : ZMod 7, j₁ ≠ 0 → i₁ ≠ 0 → j₂ ≠ 0 →
    i₂ ≠ 0 → -(j₁ + j₂) ≠ 0 → -(i₁ + i₂) ≠ 0 →
    mulCB (mulCB (mulCB (mulCB (mulCB (0, j₁, 0, 0) (i₁, 0, 0, 0)) (0, j₂, 0, 0))
      (i₂, 0, 0, 0)) (0, -(j₁ + j₂), 0, 0)) (-(i₁ + i₂), 0, 0, 0) ≠ 0 := by
  decide +kernel

/-- Length six at `⟨c,a⟩`, with the last two parameters forced by the first two coordinates
of the relation. -/
theorem mulCA_alternating6_ne_zero : ∀ j₁ i₁ j₂ i₂ : ZMod 7, j₁ ≠ 0 → i₁ ≠ 0 → j₂ ≠ 0 →
    i₂ ≠ 0 → -(j₁ + j₂) ≠ 0 → -(i₁ + i₂) ≠ 0 →
    mulCA (mulCA (mulCA (mulCA (mulCA (0, j₁, 0, 0) (i₁, 0, 0, 0)) (0, j₂, 0, 0))
      (i₂, 0, 0, 0)) (0, -(j₁ + j₂), 0, 0)) (-(i₁ + i₂), 0, 0, 0) ≠ 0 := by
  decide +kernel

/-! ## Length two -/

theorem alternating2_ne_one_ab [Finite (U3 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3) {x y : GHB 7}
    (hx : x ∈ Subgroup.closure {a 7, b 7} ⊓ Subgroup.closure {c 7, b 7})
    (hy : y ∈ Subgroup.closure {a 7, b 7} ⊓ Subgroup.closure {c 7, a 7})
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x * y ≠ 1 := by
  intro hrel
  obtain ⟨j, hj⟩ := exists_matAB_b (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2
  obtain ⟨i, hi⟩ := exists_matAB_a (Subgroup.mem_inf.mp hy).1 (Subgroup.mem_inf.mp hy).2
  have h := congrArg (fun g : GHB 7 => ((psi g : GL4) : Mat)) hrel
  simp only [map_mul, Units.val_mul, map_one, Units.val_one, hj, hi, matAB_mul] at h
  rw [← matAB_zero] at h
  exact mulAB_alternating2_ne_zero j i
    (ne_zero_of_matAB_b h3 (Subgroup.mem_inf.mp hx).1 hx1 hj)
    (ne_zero_of_matAB_a h3 (Subgroup.mem_inf.mp hy).1 hy1 hi) (matAB_injective h)

theorem alternating2_ne_one_cb [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {x y : GHB 7}
    (hx : x ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy : y ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {c 7, a 7})
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x * y ≠ 1 := by
  intro hrel
  obtain ⟨j, hj⟩ := exists_matCB_b (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2
  obtain ⟨i, hi⟩ := exists_matCB_c (Subgroup.mem_inf.mp hy).1 (Subgroup.mem_inf.mp hy).2
  have h := congrArg (fun g : GHB 7 => ((psi g : GL4) : Mat)) hrel
  simp only [map_mul, Units.val_mul, map_one, Units.val_one, hj, hi, matCB_mul] at h
  rw [← matCB_zero] at h
  exact mulCB_alternating2_ne_zero j i
    (ne_zero_of_matCB_b h4 (Subgroup.mem_inf.mp hx).1 hx1 hj)
    (ne_zero_of_matCB_c h4 (Subgroup.mem_inf.mp hy).1 hy1 hi) (matCB_injective h)

theorem alternating2_ne_one_ca [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) {x y : GHB 7}
    (hx : x ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy : y ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {c 7, b 7})
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x * y ≠ 1 := by
  intro hrel
  obtain ⟨j, hj⟩ := exists_matCA_a (Subgroup.mem_inf.mp hx).1 (Subgroup.mem_inf.mp hx).2
  obtain ⟨i, hi⟩ := exists_matCA_c (Subgroup.mem_inf.mp hy).1 (Subgroup.mem_inf.mp hy).2
  have h := congrArg (fun g : GHB 7 => ((psi g : GL4) : Mat)) hrel
  simp only [map_mul, Units.val_mul, map_one, Units.val_one, hj, hi, matCA_mul] at h
  rw [← matCA_zero] at h
  exact mulCA_alternating2_ne_zero j i
    (ne_zero_of_matCA_a h4 (Subgroup.mem_inf.mp hx).1 hx1 hj)
    (ne_zero_of_matCA_c h4 (Subgroup.mem_inf.mp hy).1 hy1 hi) (matCA_injective h)

/-! ## Length six at the `U₄(7)` vertices -/

theorem alternating6_ne_one_cb [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4)
    {x₁ y₁ x₂ y₂ x₃ y₃ : GHB 7}
    (hx₁ : x₁ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₁ : y₁ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {c 7, a 7})
    (hx₂ : x₂ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₂ : y₂ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {c 7, a 7})
    (hx₃ : x₃ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₃ : y₃ ∈ Subgroup.closure {c 7, b 7} ⊓ Subgroup.closure {c 7, a 7})
    (hx₁1 : x₁ ≠ 1) (hy₁1 : y₁ ≠ 1) (hx₂1 : x₂ ≠ 1) (hy₂1 : y₂ ≠ 1) (hx₃1 : x₃ ≠ 1)
    (hy₃1 : y₃ ≠ 1) : x₁ * y₁ * x₂ * y₂ * x₃ * y₃ ≠ 1 := by
  intro hrel
  obtain ⟨j₁, hj₁⟩ := exists_matCB_b (Subgroup.mem_inf.mp hx₁).1 (Subgroup.mem_inf.mp hx₁).2
  obtain ⟨i₁, hi₁⟩ := exists_matCB_c (Subgroup.mem_inf.mp hy₁).1 (Subgroup.mem_inf.mp hy₁).2
  obtain ⟨j₂, hj₂⟩ := exists_matCB_b (Subgroup.mem_inf.mp hx₂).1 (Subgroup.mem_inf.mp hx₂).2
  obtain ⟨i₂, hi₂⟩ := exists_matCB_c (Subgroup.mem_inf.mp hy₂).1 (Subgroup.mem_inf.mp hy₂).2
  obtain ⟨j₃, hj₃⟩ := exists_matCB_b (Subgroup.mem_inf.mp hx₃).1 (Subgroup.mem_inf.mp hx₃).2
  obtain ⟨i₃, hi₃⟩ := exists_matCB_c (Subgroup.mem_inf.mp hy₃).1 (Subgroup.mem_inf.mp hy₃).2
  have h := congrArg (fun g : GHB 7 => ((psi g : GL4) : Mat)) hrel
  simp only [map_mul, Units.val_mul, map_one, Units.val_one, hj₁, hi₁, hj₂, hi₂, hj₃, hi₃,
    matCB_mul] at h
  rw [← matCB_zero] at h
  have hp := matCB_injective h
  have hc1 := congrArg Prod.fst hp
  have hc2 := congrArg (fun t : P4 => t.2.1) hp
  simp [mulCB] at hc1 hc2
  have hi₃' : i₃ = -(i₁ + i₂) := by linear_combination hc1
  have hj₃' : j₃ = -(j₁ + j₂) := by linear_combination hc2
  subst hi₃' hj₃'
  exact mulCB_alternating6_ne_zero j₁ i₁ j₂ i₂
    (ne_zero_of_matCB_b h4 (Subgroup.mem_inf.mp hx₁).1 hx₁1 hj₁)
    (ne_zero_of_matCB_c h4 (Subgroup.mem_inf.mp hy₁).1 hy₁1 hi₁)
    (ne_zero_of_matCB_b h4 (Subgroup.mem_inf.mp hx₂).1 hx₂1 hj₂)
    (ne_zero_of_matCB_c h4 (Subgroup.mem_inf.mp hy₂).1 hy₂1 hi₂)
    (ne_zero_of_matCB_b h4 (Subgroup.mem_inf.mp hx₃).1 hx₃1 hj₃)
    (ne_zero_of_matCB_c h4 (Subgroup.mem_inf.mp hy₃).1 hy₃1 hi₃) hp

theorem alternating6_ne_one_ca [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4)
    {x₁ y₁ x₂ y₂ x₃ y₃ : GHB 7}
    (hx₁ : x₁ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₁ : y₁ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {c 7, b 7})
    (hx₂ : x₂ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₂ : y₂ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {c 7, b 7})
    (hx₃ : x₃ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {a 7, b 7})
    (hy₃ : y₃ ∈ Subgroup.closure {c 7, a 7} ⊓ Subgroup.closure {c 7, b 7})
    (hx₁1 : x₁ ≠ 1) (hy₁1 : y₁ ≠ 1) (hx₂1 : x₂ ≠ 1) (hy₂1 : y₂ ≠ 1) (hx₃1 : x₃ ≠ 1)
    (hy₃1 : y₃ ≠ 1) : x₁ * y₁ * x₂ * y₂ * x₃ * y₃ ≠ 1 := by
  intro hrel
  obtain ⟨j₁, hj₁⟩ := exists_matCA_a (Subgroup.mem_inf.mp hx₁).1 (Subgroup.mem_inf.mp hx₁).2
  obtain ⟨i₁, hi₁⟩ := exists_matCA_c (Subgroup.mem_inf.mp hy₁).1 (Subgroup.mem_inf.mp hy₁).2
  obtain ⟨j₂, hj₂⟩ := exists_matCA_a (Subgroup.mem_inf.mp hx₂).1 (Subgroup.mem_inf.mp hx₂).2
  obtain ⟨i₂, hi₂⟩ := exists_matCA_c (Subgroup.mem_inf.mp hy₂).1 (Subgroup.mem_inf.mp hy₂).2
  obtain ⟨j₃, hj₃⟩ := exists_matCA_a (Subgroup.mem_inf.mp hx₃).1 (Subgroup.mem_inf.mp hx₃).2
  obtain ⟨i₃, hi₃⟩ := exists_matCA_c (Subgroup.mem_inf.mp hy₃).1 (Subgroup.mem_inf.mp hy₃).2
  have h := congrArg (fun g : GHB 7 => ((psi g : GL4) : Mat)) hrel
  simp only [map_mul, Units.val_mul, map_one, Units.val_one, hj₁, hi₁, hj₂, hi₂, hj₃, hi₃,
    matCA_mul] at h
  rw [← matCA_zero] at h
  have hp := matCA_injective h
  have hc1 := congrArg Prod.fst hp
  have hc2 := congrArg (fun t : P4 => t.2.1) hp
  simp [mulCA] at hc1 hc2
  have hi₃' : i₃ = -(i₁ + i₂) := by linear_combination hc1
  have hj₃' : j₃ = -(j₁ + j₂) := by linear_combination hc2
  subst hi₃' hj₃'
  exact mulCA_alternating6_ne_zero j₁ i₁ j₂ i₂
    (ne_zero_of_matCA_a h4 (Subgroup.mem_inf.mp hx₁).1 hx₁1 hj₁)
    (ne_zero_of_matCA_c h4 (Subgroup.mem_inf.mp hy₁).1 hy₁1 hi₁)
    (ne_zero_of_matCA_a h4 (Subgroup.mem_inf.mp hx₂).1 hx₂1 hj₂)
    (ne_zero_of_matCA_c h4 (Subgroup.mem_inf.mp hy₂).1 hy₂1 hi₂)
    (ne_zero_of_matCA_a h4 (Subgroup.mem_inf.mp hx₃).1 hx₃1 hj₃)
    (ne_zero_of_matCA_c h4 (Subgroup.mem_inf.mp hy₃).1 hy₃1 hi₃) hp

end GHBQuotient

/-! ## The typed link girths -/

/-- **The link at the `U₃(7)` vertices has girth at least `6`.** -/
theorem linkGirthAtLeast_six_vertex0 [Finite (U3 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3) :
    LinkGirthAtLeast (vertexGroup 0 ⊓ vertexGroup 1) (vertexGroup 0 ⊓ vertexGroup 2) 6 := by
  intro m hm hg
  match m, hm, hg with
  | 0, hm, _ => exact absurd hm (by omega)
  | 1, _, _ =>
    intro x y hx hy hx1 hy1
    simpa [List.ofFn_succ, List.ofFn_zero] using
      GHBQuotient.alternating2_ne_one_ab h3 (hx 0) (hy 0) (hx1 0) (hy1 0)
  | 2, _, _ =>
    intro x y hx hy hx1 hy1
    simpa [List.ofFn_succ, List.ofFn_zero, mul_assoc] using
      GHBQuotient.alternating_ne_one_ab h3 (hx 0) (hy 0) (hx 1) (hy 1) (hx1 0) (hy1 0)
        (hx1 1) (hy1 1)
  | n + 3, _, hg => exact absurd hg (by omega)

/-- **The link at the `⟨c,b⟩ ≅ U₄(7)` vertices has girth at least `8`.** -/
theorem linkGirthAtLeast_eight_vertex1 [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) :
    LinkGirthAtLeast (vertexGroup 1 ⊓ vertexGroup 0) (vertexGroup 1 ⊓ vertexGroup 2) 8 := by
  intro m hm hg
  match m, hm, hg with
  | 0, hm, _ => exact absurd hm (by omega)
  | 1, _, _ =>
    intro x y hx hy hx1 hy1
    simpa [List.ofFn_succ, List.ofFn_zero] using
      GHBQuotient.alternating2_ne_one_cb h4 (hx 0) (hy 0) (hx1 0) (hy1 0)
  | 2, _, _ =>
    intro x y hx hy hx1 hy1
    simpa [List.ofFn_succ, List.ofFn_zero, mul_assoc] using
      GHBQuotient.alternating_ne_one_cb h4 (hx 0) (hy 0) (hx 1) (hy 1) (hx1 0) (hy1 0)
        (hx1 1) (hy1 1)
  | 3, _, _ =>
    intro x y hx hy hx1 hy1
    simpa [List.ofFn_succ, List.ofFn_zero, mul_assoc] using
      GHBQuotient.alternating6_ne_one_cb h4 (hx 0) (hy 0) (hx 1) (hy 1) (hx 2) (hy 2)
        (hx1 0) (hy1 0) (hx1 1) (hy1 1) (hx1 2) (hy1 2)
  | n + 4, _, hg => exact absurd hg (by omega)

/-- **The link at the `⟨c,a⟩ ≅ U₄(7)` vertices has girth at least `8`.** -/
theorem linkGirthAtLeast_eight_vertex2 [Finite (U4 7)] (h4 : Nat.card (U4 7) ≤ 7 ^ 4) :
    LinkGirthAtLeast (vertexGroup 2 ⊓ vertexGroup 0) (vertexGroup 2 ⊓ vertexGroup 1) 8 := by
  intro m hm hg
  match m, hm, hg with
  | 0, hm, _ => exact absurd hm (by omega)
  | 1, _, _ =>
    intro x y hx hy hx1 hy1
    simpa [List.ofFn_succ, List.ofFn_zero] using
      GHBQuotient.alternating2_ne_one_ca h4 (hx 0) (hy 0) (hx1 0) (hy1 0)
  | 2, _, _ =>
    intro x y hx hy hx1 hy1
    simpa [List.ofFn_succ, List.ofFn_zero, mul_assoc] using
      GHBQuotient.alternating_ne_one_ca h4 (hx 0) (hy 0) (hx 1) (hy 1) (hx1 0) (hy1 0)
        (hx1 1) (hy1 1)
  | 3, _, _ =>
    intro x y hx hy hx1 hy1
    simpa [List.ofFn_succ, List.ofFn_zero, mul_assoc] using
      GHBQuotient.alternating6_ne_one_ca h4 (hx 0) (hy 0) (hx 1) (hy 1) (hx 2) (hy 2)
        (hx1 0) (hy1 0) (hx1 1) (hy1 1) (hx1 2) (hy1 2)
  | n + 4, _, hg => exact absurd hg (by omega)

/-- **The typed link girths `6, 8, 8` of `GHB(7)`**, over the order bounds of the vertex
groups. -/
theorem cckwLinkGirths [Finite (U3 7)] [Finite (U4 7)] (h3 : Nat.card (U3 7) ≤ 7 ^ 3)
    (h4 : Nat.card (U4 7) ≤ 7 ^ 4) : CCKWLinkGirths :=
  ⟨linkGirthAtLeast_six_vertex0 h3, linkGirthAtLeast_eight_vertex1 h4,
    linkGirthAtLeast_eight_vertex2 h4⟩

end KMSGroup
end GroupApproximation

#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.alternating2_ne_one_ab
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.alternating6_ne_one_cb
#audit_axioms GroupApproximation.KMSGroup.GHBQuotient.alternating6_ne_one_ca
#audit_axioms GroupApproximation.KMSGroup.linkGirthAtLeast_six_vertex0
#audit_axioms GroupApproximation.KMSGroup.linkGirthAtLeast_eight_vertex1
#audit_axioms GroupApproximation.KMSGroup.linkGirthAtLeast_eight_vertex2
#audit_axioms GroupApproximation.KMSGroup.cckwLinkGirths
