import Mathlib.Algebra.FreeAlgebra
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.Coefficients

/-!
# Stable `K₂` of augmented rings and of free algebras (lane LVNK1)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii, route W1: the Lean
route to infinite finitely presented simple Kazhdan groups needs stable `K₂(L_{𝔽₂}(1,2)) = 0`.
Work order WO-LVNK-1 asks for stable `K₂(𝔽₂⟨x₀,x₁⟩) = 0`, an input of the triangular pieces
`F_n = 𝔽₂⟨x₀,x₁⟩ · C_{0,n}` of the nonnegative part of the Cohn algebra
(Ara–Brustenga–Cortiñas 2009, `thm:skewyao`, Step 3, `yaoseq6.tex` l.640-688).

The classical statement is Gersten's theorem (*K-theory of free rings*, Comm. Algebra 1 (1974)),
`K₂(F⟨X⟩) = K₂(F)` for a field `F`; Waldhausen (Ann. Math. 108 (1978)) recovers it from free
products `F⟨X⟩ = F[x₀] *_F F[x₁]`.  In degree two it splits into the retract part and a nil part:
`K₂(F⟨X⟩) = K₂(F) ⊕ ker (K₂(F⟨X⟩) → K₂(F))`.

This file proves that splitting at finite stages, for any augmented ring `π : R → A` with a
ring-map section `σ : A → R`:

* `AugNilK2Trivial π`: every element of `K₂(n, R)` in the kernel of `π` dies after padding;
* `augNilK2Trivial_of_stableK2Trivial`: stable `K₂(R) = 0` kills the nil part;
* `baseSurjective_of_augNilK2Trivial`: the nil part vanishing makes `K₂(A) → K₂(R)` stably onto;
* `stableK2Trivial_of_augNilK2Trivial`, `stableK2Trivial_iff_augNil`: stable `K₂(R) = 0` is
  *equivalent* to stable `K₂(A) = 0` together with `AugNilK2Trivial π`;

and specializes it to free algebras:

* `freeAug F X : F⟨X⟩ → F` (`xᵢ ↦ 0`) and `freeConst F X : F → F⟨X⟩`, with
  `freeAug_comp_freeConst`;
* `stableK2Trivial_freeAlgebra_iff`: stable `K₂(F⟨X⟩) = 0` iff stable `K₂(F) = 0` and the
  augmentation nil part of `K₂(F⟨X⟩)` vanishes (Gersten's theorem in degree two).
-/

namespace GroupApproximation.Full.LVFreeAlgK2

open SteinbergGroup

section Augmented

variable {R A : Type*} [Ring R] [Ring A]

/-- **Augmentation nil-`K₂` vanishes at finite stages**: every element of `K₂(n, R)` whose image
under the augmentation `π : R → A` is trivial in `St_n(A)` dies after padding.  For the free
algebra `F⟨X⟩ → F` this is the degree-two content of Gersten's theorem `K₂(F⟨X⟩) = K₂(F)`
(Gersten 1974; Waldhausen 1978).  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def AugNilK2Trivial (π : R →+* A) : Prop :=
  ∀ (n : ℕ) (k : SteinbergGroup (Fin n) R), projection k = 1 →
    ringMap π k = 1 → ∃ (N : ℕ) (h : n ≤ N), indexMap (Fin.castLEEmb h) k = 1

/-- Stable `K₂(R) = 0` kills the augmentation nil part (the augmentation hypothesis is not even
needed).  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem augNilK2Trivial_of_stableK2Trivial (π : R →+* A) (h : LVH2GL3.StableK2Trivial R) :
    AugNilK2Trivial π := by
  intro n k hk _
  exact h n k hk

/-- **Splitting `K₂(R) = K₂(A) ⊕ ker π_*`, surjectivity half.**  If the augmentation nil part
vanishes, every `k ∈ K₂(n, R)` is, after padding, the image under the section `σ` of an element
of `K₂(N, A)`: namely of `π_* k`, since `k · (σ_* π_* k)⁻¹` lies in the kernel of `π_*`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem baseSurjective_of_augNilK2Trivial (π : R →+* A) (σ : A →+* R)
    (hσ : π.comp σ = RingHom.id A) (hN : AugNilK2Trivial π) :
    LVStableK2.StableK2BaseSurjective σ := by
  intro n k hk
  have hy : projection (ringMap π k) = 1 := by
    rw [LVCohnK2.projection_ringMap, hk, map_one]
  have hσπ : projection (ringMap σ (ringMap π k)) = 1 := by
    rw [LVCohnK2.projection_ringMap, hy, map_one]
  have hk' : projection (k * (ringMap σ (ringMap π k))⁻¹) = 1 := by
    rw [map_mul, map_inv, hσπ, hk, inv_one, mul_one]
  have hc : ringMap π (ringMap σ (ringMap π k)) = ringMap π k := by
    rw [LVCohnK2.ringMap_ringMap σ π (ringMap π k), hσ, LVCohnK2.ringMap_id_apply]
  have hk'' : ringMap π (k * (ringMap σ (ringMap π k))⁻¹) = 1 := by
    rw [map_mul, map_inv, hc, mul_inv_cancel]
  obtain ⟨N, hnN, hNk⟩ := hN n _ hk' hk''
  refine ⟨N, hnN, indexMap (Fin.castLEEmb hnN) (ringMap π k),
    LVH2GL3.projection_indexMap_eq_one (Fin.castLEEmb hnN) hy, ?_⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at hNk
  rw [← LVStableK2.indexMap_ringMap]
  exact hNk.symm

/-- Stable `K₂(A) = 0` and vanishing of the augmentation nil part give stable `K₂(R) = 0`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_of_augNilK2Trivial (π : R →+* A) (σ : A →+* R)
    (hσ : π.comp σ = RingHom.id A) (hA : LVH2GL3.StableK2Trivial A)
    (hN : AugNilK2Trivial π) : LVH2GL3.StableK2Trivial R :=
  LVStableK2.stableK2Trivial_of_baseSurjective σ
    (baseSurjective_of_augNilK2Trivial π σ hσ hN) hA

/-- **The nil part is the whole difficulty.**  For an augmented ring, stable `K₂(R) = 0` is
equivalent to stable `K₂(A) = 0` together with vanishing of the augmentation nil part.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem stableK2Trivial_iff_augNil (π : R →+* A) (σ : A →+* R)
    (hσ : π.comp σ = RingHom.id A) :
    LVH2GL3.StableK2Trivial R ↔ LVH2GL3.StableK2Trivial A ∧ AugNilK2Trivial π :=
  ⟨fun h => ⟨LVCohnK2.stableK2Trivial_of_retract π σ hσ h,
      augNilK2Trivial_of_stableK2Trivial π h⟩,
    fun h => stableK2Trivial_of_augNilK2Trivial π σ hσ h.1 h.2⟩

end Augmented

section FreeAlgebra

variable (F X : Type*) [CommRing F]

/-- The augmentation `F⟨X⟩ → F`, `xᵢ ↦ 0`.
(Gersten 1974; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def freeAug : FreeAlgebra F X →+* F :=
  (FreeAlgebra.algebraMapInv (R := F) (X := X)).toRingHom

/-- The constants `F → F⟨X⟩`.
(Gersten 1974; `simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
def freeConst : F →+* FreeAlgebra F X :=
  algebraMap F (FreeAlgebra F X)

/-- The augmentation retracts the constants, elementwise.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem freeAug_freeConst (a : F) : freeAug F X (freeConst F X a) = a := by
  show FreeAlgebra.algebraMapInv (R := F) (X := X) (algebraMap F (FreeAlgebra F X) a) = a
  exact FreeAlgebra.algebraMap_leftInverse (R := F) (X := X) a

/-- The augmentation retracts the constants.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem freeAug_comp_freeConst : (freeAug F X).comp (freeConst F X) = RingHom.id F :=
  RingHom.ext fun a => freeAug_freeConst F X a

/-- **Gersten's theorem in degree two, reduced to its nil part.**  Stable `K₂(F⟨X⟩) = 0` is
equivalent to stable `K₂(F) = 0` together with vanishing of the augmentation nil part
`ker (K₂(F⟨X⟩) → K₂(F))`.  (Gersten, *K-theory of free rings*, Comm. Algebra 1 (1974);
`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii, route W1.) -/
theorem stableK2Trivial_freeAlgebra_iff :
    LVH2GL3.StableK2Trivial (FreeAlgebra F X) ↔
      LVH2GL3.StableK2Trivial F ∧ AugNilK2Trivial (freeAug F X) :=
  stableK2Trivial_iff_augNil (freeAug F X) (freeConst F X) (freeAug_comp_freeConst F X)

end FreeAlgebra

end GroupApproximation.Full.LVFreeAlgK2
