/-
Copyright (c) 2026 The group-approximation authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GroupApproximation.BHPalomar.GraphProducts.Statement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group

/-!
# Graph products over vertex subsets

For `s ⊆ V`, `GP Γ G s` is the graph product with the vertex groups outside `s` killed, that
is, the graph product over the induced subgraph on `s`. For `t ⊆ s`:

* `gpIncl` maps `GP t` to `GP s`, sending each generator to itself;
* `gpRestr` maps `GP s` to `GP t`, killing the vertices outside `t`;
* `gpRestr_gpIncl`: `gpRestr ∘ gpIncl = id`, so `GP t` is a retract of `GP s`.

`GP Γ G ∅` is trivial (`gp_empty_subsingleton`), and `GP Γ G univ` is the graph product
(`gpUnivEquiv`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace GroupApproximation.BHPalomar.GraphProducts

noncomputable section

open Monoid

variable {V : Type} (Γ : SimpleGraph V) (G : V → Type) [∀ v, Group (G v)]

/-- Kill the vertex groups outside `s`. -/
def killRels (s : Set V) : Set (CoprodI G) :=
  {w | ∃ u, u ∉ s ∧ ∃ a : G u, w = CoprodI.of a}

/-- The graph product over the induced subgraph on `s`. -/
abbrev GP (s : Set V) : Type :=
  CoprodI G ⧸ Subgroup.normalClosure (graphProductRels Γ G ∪ killRels G s)

/-- The vertex group `G u` in `GP Γ G s`. -/
def gpOf (s : Set V) (u : V) : G u →* GP Γ G s :=
  (QuotientGroup.mk' _).comp CoprodI.of

variable {Γ G}

theorem gpOf_killed {s : Set V} {u : V} (hu : u ∉ s) (a : G u) : gpOf Γ G s u a = 1 := by
  simp only [gpOf, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.subset_normalClosure (Or.inr ⟨u, hu, a, rfl⟩)

theorem gpOf_comm (s : Set V) {u w : V} (h : Γ.Adj u w) (a : G u) (b : G w) :
    gpOf Γ G s u a * gpOf Γ G s w b = gpOf Γ G s w b * gpOf Γ G s u a := by
  have h0 : QuotientGroup.mk' (Subgroup.normalClosure (graphProductRels Γ G ∪ killRels G s))
      (CoprodI.of a * CoprodI.of b * (CoprodI.of a)⁻¹ * (CoprodI.of b)⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure (Or.inl ⟨u, w, h, a, b, rfl⟩)
  have h1 : gpOf Γ G s u a * gpOf Γ G s w b * (gpOf Γ G s u a)⁻¹ * (gpOf Γ G s w b)⁻¹ = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h0
    exact h0
  calc gpOf Γ G s u a * gpOf Γ G s w b
      = (gpOf Γ G s u a * gpOf Γ G s w b * (gpOf Γ G s u a)⁻¹ * (gpOf Γ G s w b)⁻¹) *
          (gpOf Γ G s w b * gpOf Γ G s u a) := by group
    _ = gpOf Γ G s w b * gpOf Γ G s u a := by rw [h1, one_mul]

/-- Lift a family of homomorphisms to `GP Γ G s`: it must kill the vertices outside `s` and
send adjacent vertex groups inside `s` to commuting subgroups. -/
def gpLift {A : Type} [Group A] (s : Set V) (φ : ∀ u, G u →* A)
    (hkill : ∀ u, u ∉ s → ∀ a : G u, φ u a = 1)
    (hcomm : ∀ u w, Γ.Adj u w → u ∈ s → w ∈ s → ∀ (a : G u) (b : G w),
      φ u a * φ w b = φ w b * φ u a) :
    GP Γ G s →* A :=
  QuotientGroup.lift _ (CoprodI.lift φ) (Subgroup.normalClosure_le_normal (by
    rintro x (⟨u, w, hadj, a, b, rfl⟩ | ⟨u, hu, a, rfl⟩)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker]
      simp only [map_mul, map_inv, CoprodI.lift_of]
      by_cases hu : u ∈ s
      · by_cases hw : w ∈ s
        · rw [hcomm u w hadj hu hw a b]
          group
        · rw [hkill w hw b]
          group
      · rw [hkill u hu a]
        group
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, CoprodI.lift_of, hkill u hu a]))

@[simp] theorem gpLift_of {A : Type} [Group A] (s : Set V) (φ : ∀ u, G u →* A) (hkill) (hcomm)
    (u : V) (a : G u) : gpLift s φ hkill hcomm (gpOf Γ G s u a) = φ u a := by
  simp only [gpLift, gpOf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk,
    CoprodI.lift_of]

theorem gp_ext {A : Type} [Group A] {s : Set V} {f g : GP Γ G s →* A}
    (h : ∀ u (a : G u), f (gpOf Γ G s u a) = g (gpOf Γ G s u a)) : f = g := by
  apply QuotientGroup.monoidHom_ext
  exact CoprodI.ext_hom _ _ fun u => MonoidHom.ext (h u)

theorem gp_induction {s : Set V} {p : GP Γ G s → Prop} (x : GP Γ G s) (one : p 1)
    (of : ∀ u (a : G u), p (gpOf Γ G s u a)) (mul : ∀ x y, p x → p y → p (x * y)) : p x := by
  induction x using QuotientGroup.induction_on with
  | H w =>
    induction w using CoprodI.induction_on with
    | one => rw [QuotientGroup.mk_one]; exact one
    | of i a => exact of i a
    | mul x y hx hy =>
      rw [QuotientGroup.mk_mul]
      exact mul _ _ hx hy

/-- `GP t → GP s` for `t ⊆ s`. -/
def gpIncl {t s : Set V} (hts : t ⊆ s) : GP Γ G t →* GP Γ G s :=
  gpLift t (fun u => if u ∈ t then gpOf Γ G s u else 1)
    (fun u hu a => by rw [if_neg hu, MonoidHom.one_apply])
    (fun u w hadj hu hw a b => by rw [if_pos hu, if_pos hw]; exact gpOf_comm s hadj a b)

theorem gpIncl_of {t s : Set V} (hts : t ⊆ s) {u : V} (hu : u ∈ t) (a : G u) :
    gpIncl hts (gpOf Γ G t u a) = gpOf Γ G s u a := by
  simp [gpIncl, hu]

theorem gpIncl_of_not {t s : Set V} (hts : t ⊆ s) {u : V} (hu : u ∉ t) (a : G u) :
    gpIncl hts (gpOf Γ G t u a) = 1 := by
  simp [gpIncl, hu]

/-- `GP s → GP t` for `t ⊆ s`: kill the vertices outside `t`. -/
def gpRestr {t s : Set V} (hts : t ⊆ s) : GP Γ G s →* GP Γ G t :=
  gpLift s (fun u => gpOf Γ G t u)
    (fun u hu a => gpOf_killed (fun h => hu (hts h)) a)
    (fun u w hadj _ _ a b => gpOf_comm t hadj a b)

@[simp] theorem gpRestr_of {t s : Set V} (hts : t ⊆ s) (u : V) (a : G u) :
    gpRestr hts (gpOf Γ G s u a) = gpOf Γ G t u a := by
  simp [gpRestr]

theorem gpRestr_gpIncl {t s : Set V} (hts : t ⊆ s) (x : GP Γ G t) :
    gpRestr hts (gpIncl hts x) = x := by
  have h : (gpRestr hts).comp (gpIncl hts) = MonoidHom.id (GP Γ G t) := by
    apply gp_ext
    intro u a
    by_cases hu : u ∈ t
    · simp [gpIncl_of hts hu]
    · simp [gpIncl_of_not hts hu, gpOf_killed hu]
  exact DFunLike.congr_fun h x

theorem gpIncl_gpIncl {c t s : Set V} (hct : c ⊆ t) (hts : t ⊆ s) (x : GP Γ G c) :
    gpIncl hts (gpIncl hct x) = gpIncl (hct.trans hts) x := by
  have h : (gpIncl hts).comp (gpIncl hct) = gpIncl (Γ := Γ) (G := G) (hct.trans hts) := by
    apply gp_ext
    intro u a
    by_cases hu : u ∈ c
    · simp [gpIncl_of hct hu, gpIncl_of hts (hct hu), gpIncl_of (hct.trans hts) hu]
    · simp [gpIncl_of_not hct hu, gpIncl_of_not (hct.trans hts) hu]
  exact DFunLike.congr_fun h x

theorem gp_empty_subsingleton : Subsingleton (GP Γ G ∅) := by
  have h : ∀ x : GP Γ G ∅, x = 1 := by
    intro x
    induction x using gp_induction with
    | one => rfl
    | of u a => exact gpOf_killed (Set.notMem_empty u) a
    | mul x y hx hy => rw [hx, hy, one_mul]
  exact ⟨fun a b => (h a).trans (h b).symm⟩

variable (Γ G)

/-- `GP Γ G univ` is the graph product. -/
def gpUnivEquiv : GraphProduct Γ G ≃* GP Γ G Set.univ :=
  QuotientGroup.quotientMulEquivOfEq (by
    congr 1
    have : killRels G (Set.univ : Set V) = ∅ := by
      ext w
      simp [killRels]
    rw [this, Set.union_empty])

end

end GroupApproximation.BHPalomar.GraphProducts
