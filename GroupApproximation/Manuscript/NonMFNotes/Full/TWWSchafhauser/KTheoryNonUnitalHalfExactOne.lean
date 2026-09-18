import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.KTheoryNonUnitalHalfExactUnit
import GroupApproximation.KTheory.K1Lift

/-!
# Half-exactness of `K₁` for non-unital C⋆-algebras

Lane `TWWSch3d3-1C`, work order `WO-3d3-1C`, for `thm:fixed-radical-membership`
(`non_mf_group_notes.tex`, l.1376--1378). Let `ι : J → A` be injective and `π : A → B`
surjective with `ker π = range ι`. Then `K₁(J) → K₁(A) → K₁(B)` is exact at `K₁(A)`
(M. Rørdam, F. Larsen, N. Laustsen, *An introduction to K-theory for C⋆-algebras*,
Proposition 8.2.4).

The argument is the one in RLL. Suppose `[u] ∈ K₁(A)` dies in `K₁(B)`. Then at some level `k`,
`π⁺ (diag (u, 1))` lies in `U_0(M_k(B⁺))`. Lift it to `w ∈ U_0(M_k(A⁺))`, which is possible
because `π⁺` is surjective (`exists_matMapUnitary_lift`). The unitary `v = diag (u, 1) w⁻¹` has
the class of `u` and satisfies `π⁺ v = 1`. So every entry of `v` is sent to a scalar by `π⁺`,
and therefore comes from `J⁺`. Since `ι⁺` is injective, the entrywise preimage of `v` is again
unitary.

* `exists_towerMap_eq_one`: an element that dies in a sequential colimit dies at a finite level;
* `exists_matMapUnitary_eq_of_map_eq_one`, `exists_kOne_map_of_map_eq_one`: the unital
  lifting statements;
* `KOneN.map_map_of_exact`, `KOneN.exact_map`: half-exactness of `K₁` in the non-unital
  setting.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

/-- An element of a level that becomes trivial in the colimit of a tower of groups is already
trivial at some later level. -/
theorem exists_towerMap_eq_one {G : ℕ → Type*} [∀ n, Group (G n)] (T : GroupTower G) {n : ℕ}
    {x : G n} (h : T.iota n x = 1) : ∃ (k : ℕ) (hk : n ≤ k), T.map hk x = 1 := by
  have h' : T.Rel ⟨n, x⟩ ⟨0, (1 : G 0)⟩ :=
    Quotient.exact (show Quotient.mk T.setoid ⟨n, x⟩ = Quotient.mk T.setoid ⟨0, (1 : G 0)⟩ from h)
  obtain ⟨k, hx, hy, e⟩ := h'
  exact ⟨k, hx, e.trans (map_one (T.map hy))⟩

section Unital

variable {C A B : Type*} [CStarAlgebra C] [CStarAlgebra A] [CStarAlgebra B]

/-- The entries of the identity matrix are scalars. -/
theorem cstarMat_one_apply_eq_algebraMap (n : ℕ) (i j : Fin n) :
    (1 : CStarMat n B) i j = algebraMap ℂ B ((1 : CStarMat n ℂ) i j) := by
  rw [CStarMatrix.one_apply, CStarMatrix.one_apply]
  split_ifs
  · exact (map_one (algebraMap ℂ B)).symm
  · exact (map_zero (algebraMap ℂ B)).symm

/-- Entrywise application of an injective map is injective. -/
theorem matMapStarAlgHom_injective {φ : C →⋆ₐ[ℂ] A} (hφ : Function.Injective φ) (n : ℕ) :
    Function.Injective (matMapStarAlgHom φ n) := fun X Y h =>
  CStarMatrix.ext fun i j => by
    have h' : φ (X i j) = φ (Y i j) := congrArg (fun M : CStarMat n A => M i j) h
    exact hφ h'

/-- A unitary matrix killed by `ψ`, all of whose entries with scalar image come from `C`, is the
image of a unitary matrix over `C`, provided `φ : C → A` is injective. -/
theorem exists_matMapUnitary_eq_of_map_eq_one {φ : C →⋆ₐ[ℂ] A} {ψ : A →⋆ₐ[ℂ] B}
    (hφ : Function.Injective φ)
    (hlift : ∀ (a : A) (c : ℂ), ψ a = algebraMap ℂ B c → ∃ x, φ x = a) {n : ℕ}
    {v : unitary (CStarMat n A)} (hv : matMapUnitary ψ n v = 1) :
    ∃ w : unitary (CStarMat n C), matMapUnitary φ n w = v := by
  have hv' : matMapStarAlgHom ψ n (v : CStarMat n A) = 1 := congrArg Subtype.val hv
  have hij : ∀ i j : Fin n,
      ψ ((v : CStarMat n A) i j) = algebraMap ℂ B ((1 : CStarMat n ℂ) i j) := fun i j =>
    (congrArg (fun M : CStarMat n B => M i j) hv').trans (cstarMat_one_apply_eq_algebraMap n i j)
  choose X hX using fun i j : Fin n => hlift ((v : CStarMat n A) i j) _ (hij i j)
  have hM : matMapStarAlgHom φ n (X : CStarMat n C) = (v : CStarMat n A) :=
    CStarMatrix.ext fun i j => hX i j
  have hu : (X : CStarMat n C) ∈ unitary (CStarMat n C) := by
    have hvu := Unitary.mem_iff.mp v.prop
    refine Unitary.mem_iff.mpr ⟨matMapStarAlgHom_injective hφ n ?_,
      matMapStarAlgHom_injective hφ n ?_⟩
    · rw [map_mul, map_star, hM, map_one]
      exact hvu.1
    · rw [map_mul, map_star, hM, map_one]
      exact hvu.2
  exact ⟨⟨X, hu⟩, Subtype.ext hM⟩

section Order

variable [PartialOrder C] [StarOrderedRing C] [PartialOrder A] [StarOrderedRing A]
  [PartialOrder B] [StarOrderedRing B]

/-- **Exactness of `K₁` at the middle term, the lifting half, unital form** (RLL Proposition
8.2.4). Let `φ : C → A` be injective and `ψ : A → B` surjective, and suppose every element of
`A` that `ψ` sends to a scalar comes from `C`. Then every class in `K₁(A)` killed by `ψ` comes
from `K₁(C)`. -/
theorem exists_kOne_map_of_map_eq_one {φ : C →⋆ₐ[ℂ] A} {ψ : A →⋆ₐ[ℂ] B}
    (hφ : Function.Injective φ) (hψ : Function.Surjective ψ)
    (hlift : ∀ (a : A) (c : ℂ), ψ a = algebraMap ℂ B c → ∃ x, φ x = a) {x : KOne A}
    (hx : KOne.map ψ x = 1) : ∃ y : KOne C, KOne.map φ y = x := by
  obtain ⟨n, c, rfl⟩ := (kOneTower A).exists_iota x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  have hx' : kOneIota B n (QuotientGroup.mk (matMapUnitary ψ n u)) = 1 := hx
  obtain ⟨k, hk, hu⟩ := exists_towerMap_eq_one (kOneTower B) hx'
  have hblock : blockOneUnitary hk (matMapUnitary ψ n u) =
      matMapUnitary ψ k (blockOneUnitary hk u) :=
    Subtype.ext (matMapHom_blockOne ψ (u : CStarMat n A) k).symm
  have hu' : (QuotientGroup.mk (blockOneUnitary hk (matMapUnitary ψ n u)) : KOneLevel B k) = 1 :=
    hu
  have hu0 : matMapUnitary ψ k (blockOneUnitary hk u) ∈
      unitaryComponentOne (CStarMat k B) := by
    rw [← hblock]
    exact (QuotientGroup.eq_one_iff (blockOneUnitary hk (matMapUnitary ψ n u))).mp hu'
  obtain ⟨w, hw, hwu⟩ := exists_matMapUnitary_lift hψ k hu0
  have hv1 : matMapUnitary ψ k (blockOneUnitary hk u * w⁻¹) = 1 := by
    rw [map_mul, map_inv, hwu, mul_inv_cancel]
  obtain ⟨y, hy⟩ := exists_matMapUnitary_eq_of_map_eq_one hφ hlift hv1
  refine ⟨kOneIota C k (QuotientGroup.mk y), ?_⟩
  rw [KOne.map_iota_mk, hy, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    (QuotientGroup.eq_one_iff w).mpr hw, inv_one, mul_one]
  exact kOneIota_kOneMap A hk (QuotientGroup.mk u)

end Order

end Unital

section NonUnital

attribute [local instance] unitizationOrder unitizationStarOrderedRing

variable {J A B : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra A]
  [NonUnitalCStarAlgebra B] {ι : J →⋆ₙₐ[ℂ] A} {π : A →⋆ₙₐ[ℂ] B}

/-- **`K₁(J) → K₁(A) → K₁(B)` is a complex**, because `π ∘ ι = 0` and the zero map induces zero
on `K₁`. -/
theorem KOneN.map_map_of_exact (hex : ∀ a, π a = 0 ↔ a ∈ Set.range ι) (x : KOneN J) :
    KOneN.map π (KOneN.map ι x) = 0 := by
  have h := DFunLike.congr_fun (KOneN.map_comp π ι) x
  rw [comp_eq_zero_of_exact hex, KOneN.map_zero_hom, AddMonoidHom.zero_apply] at h
  exact h.symm

/-- **Half-exactness of `K₁`** (RLL Proposition 8.2.4). For `ι : J → A` injective and
`π : A → B` surjective with `ker π = range ι`, the sequence `K₁(J) → K₁(A) → K₁(B)` is exact
at `K₁(A)`. This is part of `thm:fixed-radical-membership` (`non_mf_group_notes.tex`,
l.1376--1378). -/
theorem KOneN.exact_map (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hex : ∀ a, π a = 0 ↔ a ∈ Set.range ι) :
    Function.Exact (KOneN.map ι) (KOneN.map π) := by
  intro y
  constructor
  · intro hy
    obtain ⟨a, rfl⟩ := (KOneN.ofMul (J := A)).surjective y
    have ha : KOneN.ofMul (KOne.map (Unitization.starMap π) a) =
        KOneN.ofMul (1 : KOne (Unitization ℂ B)) := hy
    obtain ⟨b, hb⟩ := exists_kOne_map_of_map_eq_one (Unitization.starMap_injective hι)
      (Unitization.starMap_surjective hπ)
      (fun _ _ h => exists_starMap_eq_of_starMap_eq_algebraMap hex h)
      ((KOneN.ofMul (J := B)).injective ha)
    exact ⟨KOneN.ofMul b,
      (KOneN.map_ofMul ι b).trans (congrArg (fun z => KOneN.ofMul (J := A) z) hb)⟩
  · rintro ⟨x, rfl⟩
    exact KOneN.map_map_of_exact hex x

end NonUnital

end

end TWWSchafhauser
end Full
end GroupApproximation
