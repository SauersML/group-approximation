import GroupApproximation.CharClass.OddPTupleD
import GroupApproximation.CharClass.AcyclicModelsSplitting

/-!
# The contraction of one slot: `∂ s + s ∂ = 1 - e` on tagged simplices

Lane `lix-cupone`, block `OddPAcyclic*` (lix-steenrod's plan §3.4, route (A)).

Over a field, a complex whose positive-degree cycles are boundaries has a contraction `s` and a
projection `e` onto a complement of the boundaries in degree `0`, with `d s + s d = 1 - e`
(`AcyclicModelsSplitting`: `splitHom`, `complProj`, `d_splitHom`, `splitHom_comm`).  This file
applies that to `C = singFreeR K X`, the signed singular chains with `Finsupp` carriers whose
differential **is** the slot boundary `tagBd` of the tuple model, and restates the three facts on
tagged simplices, where the tuple model reads them:

* `bdLC (tagS τ) + sLC (tagBd τ) = single τ 1 - tagE τ`   (one-slot contraction);
* `bdLC (tagE τ) = 0`   (`e` lands in degree `0`, where the boundary vanishes);
* `eLC (tagBd τ) = 0`   (`e` kills boundaries).

`bdLC`, `sLC`, `eLC` are the linear extensions of `tagBd`, `tagS`, `tagE` to `TagSimp X →₀ K`.  The
positive-degree acyclicity is a hypothesis `hK` here; `OddPAcyclicSimplex` discharges it on the
standard simplices.

Every tag of a positive-degree slot map is spelled through `tagAt`, whose degree is `rfl`-visible, so
no degree is ever read off a support.
-/

namespace GroupApproximation.CharClass

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace OddPAcyclic

variable (K : Type) [Field K] (X : TopCat.{0})

/-! ## 1. The contraction data, typed at bare `Finsupp`s -/

/-- The contraction `s : C_m → C_{m+1}` of the singular chains, from the splitting. -/
def chainS (m : ℕ) : (singularSimplices X m →₀ K) →ₗ[K] (singularSimplices X (m + 1) →₀ K) :=
  splitHom ((singFreeR K).obj X) m

/-- The projection `e : C_0 → C_0` onto the chosen complement of the boundaries. -/
def chainE : (singularSimplices X 0 →₀ K) →ₗ[K] (singularSimplices X 0 →₀ K) :=
  complProj ((singFreeR K).obj X) 0

/-- The contraction of a tagged simplex. -/
def tagS (τ : TagSimp X) : TagSimp X →₀ K :=
  tagAt K X (τ.1 + 1) (chainS K X τ.1 (Finsupp.single τ.2 (1 : K)))

/-- The projection of a tagged simplex: `e` in degree `0`, and `0` above. -/
def tagE : TagSimp X → (TagSimp X →₀ K)
  | ⟨0, σ⟩ => tagAt K X 0 (chainE K X (Finsupp.single σ (1 : K)))
  | ⟨_ + 1, _⟩ => 0

theorem tagS_mk (n : ℕ) (σ : singularSimplices X n) :
    tagS K X ⟨n, σ⟩ = tagAt K X (n + 1) (chainS K X n (Finsupp.single σ (1 : K))) :=
  rfl

theorem tagE_mk_zero (σ : singularSimplices X 0) :
    tagE K X ⟨0, σ⟩ = tagAt K X 0 (chainE K X (Finsupp.single σ (1 : K))) :=
  rfl

theorem tagS_eq (n : ℕ) (σ : singularSimplices X n) :
    tagS K X ⟨n, σ⟩
      = Finsupp.mapDomain (fun σ' : singularSimplices X (n + 1) => (⟨n + 1, σ'⟩ : TagSimp X))
          (chainS K X n (Finsupp.single σ (1 : K))) :=
  rfl

theorem tagE_zero_eq (σ : singularSimplices X 0) :
    tagE K X ⟨0, σ⟩
      = Finsupp.mapDomain (fun σ' : singularSimplices X 0 => (⟨0, σ'⟩ : TagSimp X))
          (chainE K X (Finsupp.single σ (1 : K))) :=
  rfl

@[simp] theorem tagE_succ (n : ℕ) (σ : singularSimplices X (n + 1)) :
    tagE K X ⟨n + 1, σ⟩ = 0 :=
  rfl

theorem tagAt_eq_mapDomain (n : ℕ) (z : singularSimplices X n →₀ K) :
    tagAt K X n z = Finsupp.mapDomain (fun σ : singularSimplices X n => (⟨n, σ⟩ : TagSimp X)) z :=
  rfl

/-! ## 2. The linear extensions, and how they cross `tagAt` -/

/-- The slot boundary, extended linearly. -/
def bdLC : Module.End K (TagSimp X →₀ K) := Finsupp.linearCombination K (tagBd K X)

/-- The slot contraction, extended linearly. -/
def sLC : Module.End K (TagSimp X →₀ K) := Finsupp.linearCombination K (tagS K X)

/-- The slot projection, extended linearly. -/
def eLC : Module.End K (TagSimp X →₀ K) := Finsupp.linearCombination K (tagE K X)

theorem bdLC_tagAt_succ (n : ℕ) (z : singularSimplices X (n + 1) →₀ K) :
    bdLC K X (tagAt K X (n + 1) z) = tagAt K X n (chainBd K X n z) := by
  rw [bdLC, tagAt_eq_mapDomain K X (n + 1) z, Finsupp.linearCombination_mapDomain]
  exact linearCombinationR_comp_single ((tagAt K X n).comp (chainBd K X n)) z

theorem bdLC_tagAt_zero (z : singularSimplices X 0 →₀ K) : bdLC K X (tagAt K X 0 z) = 0 := by
  rw [bdLC, tagAt_eq_mapDomain K X 0 z, Finsupp.linearCombination_mapDomain]
  exact linearCombinationR_zero_fun z

theorem sLC_tagAt (n : ℕ) (z : singularSimplices X n →₀ K) :
    sLC K X (tagAt K X n z) = tagAt K X (n + 1) (chainS K X n z) := by
  rw [sLC, tagAt_eq_mapDomain K X n z, Finsupp.linearCombination_mapDomain]
  exact linearCombinationR_comp_single ((tagAt K X (n + 1)).comp (chainS K X n)) z

theorem eLC_tagAt_zero (z : singularSimplices X 0 →₀ K) :
    eLC K X (tagAt K X 0 z) = tagAt K X 0 (chainE K X z) := by
  rw [eLC, tagAt_eq_mapDomain K X 0 z, Finsupp.linearCombination_mapDomain]
  exact linearCombinationR_comp_single ((tagAt K X 0).comp (chainE K X)) z

theorem eLC_tagAt_succ (n : ℕ) (z : singularSimplices X (n + 1) →₀ K) :
    eLC K X (tagAt K X (n + 1) z) = 0 := by
  rw [eLC, tagAt_eq_mapDomain K X (n + 1) z, Finsupp.linearCombination_mapDomain]
  exact linearCombinationR_zero_fun z

/-! ## 3. The three one-slot facts -/

/-- **The one-slot contraction**: `∂ (s τ) + s (∂ τ) = τ - e τ` on a tagged simplex. -/
theorem bdLC_tagS_add_sLC_tagBd
    (hK : ∀ k : ℕ, LinearMap.ker (((singFreeR K).obj X).d (k + 1) k).hom
      ≤ LinearMap.range (((singFreeR K).obj X).d (k + 2) (k + 1)).hom) (τ : TagSimp X) :
    bdLC K X (tagS K X τ) + sLC K X (tagBd K X τ)
      = Finsupp.single τ (1 : K) - tagE K X τ := by
  obtain ⟨n, σ⟩ := τ
  cases n with
  | zero =>
    have hd : chainBd K X 0 (chainS K X 0 (Finsupp.single σ (1 : K)))
        = bdryProj ((singFreeR K).obj X) 0 (Finsupp.single σ (1 : K)) :=
      d_splitHom ((singFreeR K).obj X) hK 0 (Finsupp.single σ (1 : K))
    have hsum := bdryProj_add_complProj ((singFreeR K).obj X) 0 (Finsupp.single σ (1 : K))
    have hb : bdryProj ((singFreeR K).obj X) 0 (Finsupp.single σ (1 : K))
        = Finsupp.single σ (1 : K) - chainE K X (Finsupp.single σ (1 : K)) :=
      eq_sub_of_add_eq hsum
    rw [tagS_mk, bdLC_tagAt_succ, tagBd_zero, map_zero, add_zero, hd, hb, map_sub, tagAt_single,
      tagE_mk_zero]
  | succ n =>
    have hc : chainBd K X (n + 1) (chainS K X (n + 1) (Finsupp.single σ (1 : K)))
        + chainS K X n (chainBd K X n (Finsupp.single σ (1 : K)))
        = Finsupp.single σ (1 : K) :=
      splitHom_comm ((singFreeR K).obj X) hK n (Finsupp.single σ (1 : K))
    rw [tagS_mk, bdLC_tagAt_succ, tagBd_succ_eq, ← tagAt_eq_mapDomain, sLC_tagAt,
      ← map_add (tagAt K X (n + 1)), hc,
      tagAt_single, tagE_succ, sub_zero]

/-- **`e` lands where the boundary vanishes.** -/
theorem bdLC_tagE (τ : TagSimp X) : bdLC K X (tagE K X τ) = 0 := by
  obtain ⟨n, σ⟩ := τ
  cases n with
  | zero => rw [tagE_mk_zero, bdLC_tagAt_zero]
  | succ n => rw [tagE_succ, map_zero]

/-- **`e` kills boundaries.** -/
theorem eLC_tagBd (τ : TagSimp X) : eLC K X (tagBd K X τ) = 0 := by
  obtain ⟨n, σ⟩ := τ
  cases n with
  | zero => rw [tagBd_zero, map_zero]
  | succ n =>
    rw [tagBd_succ_eq, ← tagAt_eq_mapDomain]
    cases n with
    | zero =>
      rw [eLC_tagAt_zero]
      have h0 : chainE K X (chainBd K X 0 (Finsupp.single σ (1 : K))) = 0 :=
        complProj_of_mem_range ((singFreeR K).obj X) 0 ⟨Finsupp.single σ (1 : K), rfl⟩
      rw [h0, map_zero]
    | succ n => exact eLC_tagAt_succ K X n _

end OddPAcyclic

end

end GroupApproximation.CharClass
