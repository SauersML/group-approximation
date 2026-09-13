import GroupApproximation.GGT.HullLemma35Printed
import GroupApproximation.GGT.HullSCUnionGeometryCoprod
import GroupApproximation.Sofic.FreeProductRouterObstruction
import GroupApproximation.Meta.AxiomGuard

/-!
# The free factors of a free product are hyperbolically embedded

The manuscript's paragraph on Fournier-Facio's group (section `sec:torsion-free`, tex 1680-1684)
says:

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

Hull's proof of Corollary 7.4 (arXiv:1308.4345v2, §7) takes `F = G₁ ∗ G₂` and uses the clause
"Since `{G₁, G₂} ↪h F`". This module proves that clause for all groups `G₁` and `G₂`:
`printedFreeFactorsHypEmbedded : PrintedFreeFactorsHypEmbedded`.

The relative generating set is `X = ∅` with the family `{G₁, G₂}`.

* **Local finiteness.** Every relative ball is `{1}`. Read a path from `1` that uses no edge of
  `Γ_{G₁}`. At a vertex equal to `1`, which lies in `G₁`, the next letter comes from `G₂`, so
  every partial product is `1` or has a reduced word beginning in `G₂`. A nontrivial element of
  `G₁` begins in `G₁`, so a path ending in `G₁` ends at `1`. The same holds with the factors
  exchanged.
* **Hyperbolicity.** `Γ(G₁ ∗ G₂, G₁ ⊔ G₂)` is the free product of the Cayley graphs `Γ(Gᵢ, Gᵢ)`,
  each of diameter at most `1`. `HullSCUnionGeometry.isFourPointHyperbolic_unionCarrier` gives
  the four-point condition at `δ = 1` over `CoprodI`, and
  `FreeProductRouterObstruction.coprodIBoolEquiv` carries it to `Monoid.Coprod` in every universe.
-/

namespace GroupApproximation
namespace GGT

open Monoid
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.FreeProductUnionNorm
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

namespace FreeFactorsHypEmbedded

open RelHyp (headIdx headIdx_of headIdx_one headIdx_mul_of)

/-! ## 1.  The binary free product as an indexed one -/

/-- The two factors of `G₁ ∗ G₂`, as a family indexed by `Bool`. -/
def pairFam (G₁ G₂ : Type u) : Bool → Type u
  | false => G₁
  | true => G₂

instance pairFamGroup (G₁ G₂ : Type u) [Group G₁] [Group G₂] :
    ∀ b, Group (pairFam G₁ G₂ b)
  | false => inferInstanceAs (Group G₁)
  | true => inferInstanceAs (Group G₂)

/-- **The relative generating set `(∅, {G₁, G₂})` of `G₁ ∗ G₂`.** -/
def factorsRelGenSet (G₁ G₂ : Type u) [Group G₁] [Group G₂] :
    RelGenSet (Monoid.Coprod G₁ G₂) (Fin 2) where
  base := ∅
  fam := ![(Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range,
    (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range]
  symmetricGenerating := by
    constructor
    · rintro x (hx | hx)
      · exact absurd hx (Set.notMem_empty x)
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_union_right _ (Set.mem_iUnion.mpr
          ⟨lam, SetLike.mem_coe.mpr (Subgroup.inv_mem _ (SetLike.mem_coe.mp hlam))⟩)
    · rw [eq_top_iff, ← Monoid.Coprod.closure_range_inl_union_inr]
      refine Subgroup.closure_mono ?_
      rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
      · refine Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨0, SetLike.mem_coe.mpr ?_⟩)
        exact (MonoidHom.mem_range.mpr ⟨a, rfl⟩ :
          Monoid.Coprod.inl a ∈ (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range)
      · refine Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨1, SetLike.mem_coe.mpr ?_⟩)
        exact (MonoidHom.mem_range.mpr ⟨b, rfl⟩ :
          Monoid.Coprod.inr b ∈ (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range)

section Equiv

variable {G₁ G₂ : Type u} [Group G₁] [Group G₂]

/-- **`G₁ ∗ G₂` is the free product of the family `pairFam G₁ G₂`**, in every universe. -/
def pairEquiv : Monoid.Coprod G₁ G₂ ≃* CoprodI (pairFam G₁ G₂) :=
  (FreeProductRouterObstruction.coprodIBoolEquiv (pairFam G₁ G₂)).symm

theorem pairEquiv_inl (a : G₁) :
    pairEquiv (Monoid.Coprod.inl a : Monoid.Coprod G₁ G₂)
      = CoprodI.of (M := pairFam G₁ G₂) (i := false) a :=
  Monoid.Coprod.lift_apply_inl (CoprodI.of (M := pairFam G₁ G₂) (i := false))
    (CoprodI.of (M := pairFam G₁ G₂) (i := true)) a

theorem pairEquiv_inr (b : G₂) :
    pairEquiv (Monoid.Coprod.inr b : Monoid.Coprod G₁ G₂)
      = CoprodI.of (M := pairFam G₁ G₂) (i := true) b :=
  Monoid.Coprod.lift_apply_inr (CoprodI.of (M := pairFam G₁ G₂) (i := false))
    (CoprodI.of (M := pairFam G₁ G₂) (i := true)) b

theorem pairEquiv_symm_of_false (a : G₁) :
    pairEquiv.symm (CoprodI.of (M := pairFam G₁ G₂) (i := false) a)
      = (Monoid.Coprod.inl a : Monoid.Coprod G₁ G₂) :=
  (MulEquiv.symm_apply_eq pairEquiv).mpr (pairEquiv_inl a).symm

theorem pairEquiv_symm_of_true (b : G₂) :
    pairEquiv.symm (CoprodI.of (M := pairFam G₁ G₂) (i := true) b)
      = (Monoid.Coprod.inr b : Monoid.Coprod G₁ G₂) :=
  (MulEquiv.symm_apply_eq pairEquiv).mpr (pairEquiv_inr b).symm

/-- A member of either factor is a single letter of the indexed free product. -/
theorem exists_of_mem_fam {lam : Fin 2} {h : Monoid.Coprod G₁ G₂}
    (hh : h ∈ (factorsRelGenSet G₁ G₂).fam lam) :
    ∃ (i : Bool) (z : pairFam G₁ G₂ i), pairEquiv h = CoprodI.of z := by
  obtain ⟨_ | _ | _, hk⟩ := lam
  · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp
      (hh : h ∈ (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range)
    exact ⟨false, a, pairEquiv_inl a⟩
  · obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp
      (hh : h ∈ (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range)
    exact ⟨true, b, pairEquiv_inr b⟩
  · exact absurd hk (by omega)

end Equiv

/-! ## 2.  Relative balls -/

section Heads

variable {G₁ G₂ : Type u} [Group G₁] [Group G₂] [∀ b, DecidableEq (pairFam G₁ G₂ b)]

/-- A single letter is trivial or begins in its own factor. -/
theorem heads_of_eq_of {h : Monoid.Coprod G₁ G₂} {i : Bool} {z : pairFam G₁ G₂ i}
    (hz : pairEquiv h = CoprodI.of z) : h = 1 ∨ headIdx (pairEquiv h) = some i := by
  by_cases hz1 : z = 1
  · left
    apply pairEquiv.injective
    rw [hz, hz1, map_one, map_one]
  · right
    rw [hz]
    exact headIdx_of hz1

/-- A single letter of factor `i` that is `1` or begins in factor `b ≠ i` is `1`. -/
theorem eq_one_of_heads {h : Monoid.Coprod G₁ G₂} {i b : Bool} {z : pairFam G₁ G₂ i}
    (hz : pairEquiv h = CoprodI.of z) (hib : i ≠ b)
    (hh : h = 1 ∨ headIdx (pairEquiv h) = some b) : h = 1 := by
  rcases hh with hh | hh
  · exact hh
  · rcases heads_of_eq_of hz with h1 | h1
    · exact h1
    · rw [h1] at hh
      exact absurd (Option.some.inj hh) hib

/-- **One step of a path keeps the invariant.** At a partial product equal to `1` the next
letter must be `1` or begin in `b`; at a nontrivial one the head does not move. -/
theorem heads_mul {b : Bool} {g a : Monoid.Coprod G₁ G₂}
    (hg : g = 1 ∨ headIdx (pairEquiv g) = some b)
    (ha : ∃ (i : Bool) (z : pairFam G₁ G₂ i), pairEquiv a = CoprodI.of z)
    (hstart : g = 1 → a = 1 ∨ headIdx (pairEquiv a) = some b) :
    g * a = 1 ∨ headIdx (pairEquiv (g * a)) = some b := by
  obtain ⟨i, z, hz⟩ := ha
  rcases hg with hg | hhead
  · rw [hg, one_mul]
    exact hstart hg
  · have hg1 : pairEquiv g ≠ 1 := by
      intro hcon
      rw [hcon, headIdx_one] at hhead
      simp at hhead
    by_cases hga : g * a = 1
    · exact Or.inl hga
    · refine Or.inr ?_
      have hne : pairEquiv g * CoprodI.of z ≠ 1 := by
        intro hcon
        apply hga
        apply pairEquiv.injective
        rw [map_mul, hz, hcon, map_one]
      rw [map_mul, hz, headIdx_mul_of z hg1 hne]
      exact hhead

/-- **The invariant survives a path that avoids `Γ_{H lam}`**, when every letter outside
`H lam` is `1` or begins in `b`. -/
theorem heads_listVal (lam : Fin 2) (b : Bool)
    (hother : ∀ (mu : Fin 2) (h : Monoid.Coprod G₁ G₂), mu ≠ lam →
      h ∈ (factorsRelGenSet G₁ G₂).fam mu → h = 1 ∨ headIdx (pairEquiv h) = some b) :
    ∀ (w : List (RelLetter (Monoid.Coprod G₁ G₂) (Fin 2))) (g : Monoid.Coprod G₁ G₂),
      (∀ a ∈ w, (factorsRelGenSet G₁ G₂).IsLetter a) →
      AvoidsFrom (factorsRelGenSet G₁ G₂).fam lam w g →
      (g = 1 ∨ headIdx (pairEquiv g) = some b) →
      g * RelLetter.listVal w = 1 ∨
        headIdx (pairEquiv (g * RelLetter.listVal w)) = some b := by
  intro w
  induction w with
  | nil =>
      intro g _ _ hg
      rw [RelLetter.listVal_nil, mul_one]
      exact hg
  | cons a w ih =>
      intro g hlet havoid hg
      have ha : (factorsRelGenSet G₁ G₂).IsLetter a := hlet a (by simp)
      obtain ⟨hnot, hrest⟩ := havoid
      cases a with
      | base x => exact absurd ha (Set.notMem_empty x)
      | comp mu h =>
          have hh : h ∈ (factorsRelGenSet G₁ G₂).fam mu := ha
          have hstep : g * h = 1 ∨ headIdx (pairEquiv (g * h)) = some b := by
            refine heads_mul hg (exists_of_mem_fam hh) ?_
            intro hg1
            refine hother mu h ?_ hh
            intro hmu
            refine hnot ⟨hmu, ?_⟩
            rw [hg1]
            exact one_mem _
          have hprod : g * RelLetter.listVal (RelLetter.comp mu h :: w)
              = g * h * RelLetter.listVal w := by
            simp only [RelLetter.listVal, List.map_cons, List.prod_cons, RelLetter.val,
              mul_assoc]
          rw [hprod]
          exact ih (g * h) (fun x hx => hlet x (List.mem_cons.mpr (Or.inr hx))) hrest hstep

end Heads

section Balls

variable {G₁ G₂ : Type u} [Group G₁] [Group G₂]

/-- **The relative ball of a factor is `{1}`**, given which factor it is and which factor the
other member of the family is. -/
theorem relBall_subset_one_of_sides (lam : Fin 2) (i b : Bool) (hib : i ≠ b)
    (hlam : ∀ h, h ∈ (factorsRelGenSet G₁ G₂).fam lam →
      ∃ z : pairFam G₁ G₂ i, pairEquiv h = CoprodI.of z)
    (hother : ∀ (mu : Fin 2) (h : Monoid.Coprod G₁ G₂), mu ≠ lam →
      h ∈ (factorsRelGenSet G₁ G₂).fam mu → ∃ z : pairFam G₁ G₂ b, pairEquiv h = CoprodI.of z)
    (n : ℕ) :
    (factorsRelGenSet G₁ G₂).relBall lam n ⊆ ({1} : Set (Monoid.Coprod G₁ G₂)) := by
  classical
  rintro h ⟨hmem, w, hlet, rfl, havoid, -⟩
  obtain ⟨z, hz⟩ := hlam _ hmem
  have hkey := heads_listVal lam b
    (fun mu h hmu hh => by
      obtain ⟨z', hz'⟩ := hother mu h hmu hh
      exact heads_of_eq_of hz') w 1 hlet havoid (Or.inl rfl)
  rw [one_mul] at hkey
  exact Set.mem_singleton_iff.mpr (eq_one_of_heads hz hib hkey)

/-- **Clause (b)**: every relative ball of `(∅, {G₁, G₂})` is finite. -/
theorem relBall_finite (lam : Fin 2) (n : ℕ) :
    ((factorsRelGenSet G₁ G₂).relBall lam n).Finite := by
  refine Set.Finite.subset (Set.finite_singleton (1 : Monoid.Coprod G₁ G₂)) ?_
  obtain ⟨_ | _ | _, hk⟩ := lam
  · refine relBall_subset_one_of_sides _ false true (by decide) ?_ ?_ n
    · intro h hh
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp
        (hh : h ∈ (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range)
      exact ⟨a, pairEquiv_inl a⟩
    · rintro ⟨_ | _ | _, hk'⟩ h hmu hh
      · exact (hmu rfl).elim
      · obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp
          (hh : h ∈ (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range)
        exact ⟨b, pairEquiv_inr b⟩
      · exact absurd hk' (by omega)
  · refine relBall_subset_one_of_sides _ true false (by decide) ?_ ?_ n
    · intro h hh
      obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp
        (hh : h ∈ (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range)
      exact ⟨b, pairEquiv_inr b⟩
    · rintro ⟨_ | _ | _, hk'⟩ h hmu hh
      · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp
          (hh : h ∈ (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range)
        exact ⟨a, pairEquiv_inl a⟩
      · exact (hmu rfl).elim
      · exact absurd hk' (by omega)
  · exact absurd hk (by omega)

end Balls

/-! ## 3.  Hyperbolicity -/

/-- **A word-length-preserving isomorphism carries the four-point condition back**, in every
universe. `HullSCUnionGeometry.isFourPointHyperbolic_of_wordNorm_eq` is the same statement over
`Type`. -/
theorem isFourPointHyperbolic_comap_of_wordNorm_eq {E Gam : Type u} [Group E] [Group Gam]
    {A : Set E} {C : Set Gam} (e : E ≃* Gam)
    (hnorm : ∀ w : E, wordNorm C (e w) = wordNorm A w) {δ : ℕ}
    (hC : Hyperbolic.IsFourPointHyperbolic C δ) :
    Hyperbolic.IsFourPointHyperbolic A δ := by
  intro w x y z
  have hd : ∀ a b : E, wordDist A a b = wordDist C (e a) (e b) := by
    intro a b
    have h : (e a)⁻¹ * e b = e (a⁻¹ * b) := by
      rw [map_mul, map_inv]
    show wordNorm A (a⁻¹ * b) = wordNorm C ((e a)⁻¹ * e b)
    rw [h, hnorm]
  rw [hd w x, hd y z, hd w y, hd x z, hd w z, hd x y]
  exact hC (e w) (e x) (e y) (e z)

section Geometry

variable {G₁ G₂ : Type u} [Group G₁] [Group G₂]

/-- **`Γ(G₁ ∗ G₂, G₁ ⊔ G₂)` satisfies the four-point condition at `δ = 1`.** -/
theorem isFourPointHyperbolic_alphabet :
    Hyperbolic.IsFourPointHyperbolic (factorsRelGenSet G₁ G₂).alphabet.carrier 1 := by
  classical
  have hS : ∀ b : Bool, IsSymmetricGeneratingSet (Set.univ : Set (pairFam G₁ G₂ b)) :=
    fun _ => ⟨fun _ _ => Set.mem_univ _, Subgroup.closure_univ⟩
  have hδ : ∀ b : Bool,
      Hyperbolic.IsFourPointHyperbolic (Set.univ : Set (pairFam G₁ G₂ b)) 1 :=
    fun _ => Hyperbolic.isFourPointHyperbolic_of_bounded
      (fun _ _ => wordNorm_le_one_of_mem (Set.mem_univ _))
  have hC := HullSCUnionGeometry.isFourPointHyperbolic_unionCarrier hS hδ
  have hAC : ∀ a ∈ (factorsRelGenSet G₁ G₂).alphabet.carrier,
      pairEquiv a ∈ unionCarrier (fun b : Bool => (Set.univ : Set (pairFam G₁ G₂ b))) := by
    rintro a (ha | ha)
    · exact absurd ha (Set.notMem_empty a)
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp ha
      obtain ⟨i, z, hz⟩ := exists_of_mem_fam (SetLike.mem_coe.mp hlam)
      exact ⟨i, z, Set.mem_univ _, hz.symm⟩
  have hCA : ∀ x ∈ unionCarrier (fun b : Bool => (Set.univ : Set (pairFam G₁ G₂ b))),
      pairEquiv.symm x ∈ (factorsRelGenSet G₁ G₂).alphabet.carrier := by
    rintro x ⟨i, z, -, rfl⟩
    refine Set.mem_union_right _ (Set.mem_iUnion.mpr ?_)
    cases i with
    | false =>
        exact ⟨0, SetLike.mem_coe.mpr (MonoidHom.mem_range.mpr
          ⟨z, (pairEquiv_symm_of_false z).symm⟩ :
            _ ∈ (Monoid.Coprod.inl : G₁ →* Monoid.Coprod G₁ G₂).range)⟩
    | true =>
        exact ⟨1, SetLike.mem_coe.mpr (MonoidHom.mem_range.mpr
          ⟨z, (pairEquiv_symm_of_true z).symm⟩ :
            _ ∈ (Monoid.Coprod.inr : G₂ →* Monoid.Coprod G₁ G₂).range)⟩
  have hnorm := HullSC.wordNorm_of_mulEquiv (factorsRelGenSet G₁ G₂).alphabet.symmetricGenerating
    (isSymmetricGeneratingSet_unionCarrier hS) pairEquiv hAC hCA
  exact isFourPointHyperbolic_comap_of_wordNorm_eq pairEquiv hnorm hC

/-- **`{G₁, G₂} ↪h (G₁ ∗ G₂, ∅)`**: clauses (a) and (b) of Hull's Definition 3.1. -/
theorem isHyperbolicallyEmbedded_factorsRelGenSet :
    (factorsRelGenSet G₁ G₂).IsHyperbolicallyEmbedded where
  hyperbolic := ⟨((1 : ℕ) : ℝ), isHyperbolicSpace_cayley_of_fourPoint
    (factorsRelGenSet G₁ G₂).alphabet isFourPointHyperbolic_alphabet⟩
  locallyFinite := fun lam n => relBall_finite lam n

end Geometry

end FreeFactorsHypEmbedded

/-- **The free factors are hyperbolically embedded in the free product**, for all groups `G₁`
and `G₂`. This is the clause "Since `{G₁, G₂} ↪h F`" of Hull's proof of Corollary 7.4
(arXiv:1308.4345v2, §7), which the manuscript invokes at tex 1680-1684 (section
`sec:torsion-free`):

> The group $G_0$ is obtained there as a common quotient of two finitely generated acylindrically
> hyperbolic groups by Hull's theorem~\cite[Corollary~7.4]{Hull}, which allows the quotient to be
> chosen acylindrically hyperbolic; we take $G_0$ to be such a quotient.

The witness is `X = ∅`. -/
theorem printedFreeFactorsHypEmbedded : PrintedFreeFactorsHypEmbedded.{u} :=
  fun G₁ G₂ _ _ => ⟨FreeFactorsHypEmbedded.factorsRelGenSet G₁ G₂, rfl,
    FreeFactorsHypEmbedded.isHyperbolicallyEmbedded_factorsRelGenSet⟩

#audit_closed_axioms GroupApproximation.GGT.printedFreeFactorsHypEmbedded

#audit_axioms GroupApproximation.GGT.FreeFactorsHypEmbedded.relBall_finite

#audit_axioms GroupApproximation.GGT.FreeFactorsHypEmbedded.isFourPointHyperbolic_alphabet

end GGT
end GroupApproximation
