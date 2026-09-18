import GroupApproximation.BooneHigman.Metabelian.ElemFPNK2CoreSlice
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2CubeNilFieldCone
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2CubeResidueFieldCone
import GroupApproximation.Meta.AxiomGuard

/-!
# The slice `NK₂` residual, level by level

Lane `bh-met-90t`.  The slice residual `nk2Core_SliceOverStatement A` (lane `bh-met-90o`) is a
conjunction over the number `n + 1` of cube variables.  Here it is split into levels, and the
levels are related to each other.

* `nk2Slice_LevelStatement A n`: the slice residual at the single level `n` (rank `N = n + 5`).
  `nk2Core_SliceOverStatement A` is `∀ n, nk2Slice_LevelStatement A n` by definition
  (`nk2Slice_sliceOver_iff_level`).
* `nk2Slice_DiesStatement A n`: every cube element `v ∈ K₂(n + 5, A[s_0..s_n])` (killed by every
  `π_i`) dies after padding.
* `nk2Slice_dies_of_level`: given `hres`, level `n` gives death at level `n`.  This is the proof of
  `nk2Core_pad_dies_of_sliceOver`, run at one level only, followed by unpadding.
* `nk2Slice_level_of_dies`: conversely, death at level `n` gives level `n` (`s = 1`), with no
  hypothesis on `A`.
* `nk2Slice_dies_of_dies_succ`: **death at level `n + 1` gives death at level `n`.**  Pad
  `v` to `ι v ∈ K₂(n + 6, A[s_0..s_n])`; the cone `j : s_0 ↦ s_0 s_{n+1}` sends it to a cube
  element `j (ι v) ∈ K₂((n + 1) + 5, A[s_0..s_{n+1}])` (`czCubeResField_K2Map_cubeKill_cone`),
  which dies by level `n + 1`; the retraction `r : s_{n+1} ↦ 1` has `r ∘ j = id`, so `ι v` dies,
  hence `v` dies.  Ring-generic, no hypothesis.
* `nk2Slice_dies_of_dies_le`: iterating, death at any level `n' ≥ n` gives death at level `n`.

Module `ElemFPNK2SliceWire` uses these to replace the slice residual by the demand at cofinally
many levels only.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian.ElemFP

section Pad

variable {R : Type*} [Ring R]

/-- Padding preserves death after padding. -/
theorem nk2Slice_diesAfterPadding_pad {N N' : ℕ} (h : N ≤ N') {u : K2n N R}
    (hu : K2DiesAfterPadding u) :
    K2DiesAfterPadding (K2IndexMap (R := R) (Fin.castLEEmb h) u) := by
  obtain ⟨M, hNM, hM⟩ := hu
  refine ⟨max M N', le_max_right M N', ?_⟩
  rw [K2IndexMap_castLEEmb_castLEEmb h (le_max_right M N') u]
  exact K2IndexMap_eq_one_of_le hNM (le_max_left M N') _ hM

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Slice_diesAfterPadding_pad

end Pad

section Over

variable (A : Type*) [CommRing A]

/-- **The slice residual at the single level `n`** (cube variables `s_0..s_n`, rank `n + 5`). -/
def nk2Slice_LevelStatement (n : ℕ) : Prop :=
  ∀ N : ℕ, N = n + 5 →
    ∀ v : K2n N (MvPolynomial (Fin (n + 1)) A),
      (∀ i : Fin (n + 1), K2Map (cubeKill A i) v = 1) →
        ∀ p : ℕ, p.Prime →
          ∀ P : Ideal (MvPolynomial (Fin (n + 1)) A), P.IsMaximal →
            (p : MvPolynomial (Fin (n + 1)) A) ∈ P →
              (MvPolynomial.X (Fin.last n) - 1 : MvPolynomial (Fin (n + 1)) A) ∈ P →
                ∃ s : MvPolynomial (Fin (n + 1)) A, s ∉ P ∧
                  K2DiesAfterPadding
                    (quillenDiff
                      (K2Map (MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom
                        (K2Map (czCubeResFieldCone A n)
                          (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v))) s)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Slice_LevelStatement

/-- The slice residual is the conjunction of its levels (by definition). -/
theorem nk2Slice_sliceOver_iff_level :
    nk2Core_SliceOverStatement A ↔ ∀ n : ℕ, nk2Slice_LevelStatement A n :=
  ⟨fun h n ↦ h n, fun h n ↦ h n⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Slice_sliceOver_iff_level

/-- **Death at level `n`**: every cube element of `K₂(n + 5, A[s_0..s_n])` dies after padding. -/
def nk2Slice_DiesStatement (n : ℕ) : Prop :=
  ∀ N : ℕ, N = n + 5 →
    ∀ v : K2n N (MvPolynomial (Fin (n + 1)) A),
      (∀ i : Fin (n + 1), K2Map (cubeKill A i) v = 1) → K2DiesAfterPadding v

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Slice_DiesStatement

/-- Death at level `n` gives the slice residual at level `n`, with `s = 1` (no hypothesis). -/
theorem nk2Slice_level_of_dies {n : ℕ} (h : nk2Slice_DiesStatement A n) :
    nk2Slice_LevelStatement A n := by
  intro N hN v hv _ _ P hP _ _
  refine ⟨1, (Ideal.ne_top_iff_one _).mp hP.ne_top, ?_⟩
  exact diesAfterPadding_quillenDiff_of_diesAfterPadding
    (diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom
      (diesAfterPadding_K2Map (czCubeResFieldCone A n)
        (nk2Slice_diesAfterPadding_pad (Nat.le_add_right N 1) (h N hN v hv)))) 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Slice_level_of_dies

/-- **Death from the slice residual at one level.**  If every maximal ideal of every
`A[s_1..s_k]` contains a prime, the slice residual at level `n` gives death at level `n`.  The
argument of `nk2Core_pad_dies_of_sliceOver` (Krull, the slice retraction `ε`, the collapse),
run at level `n` only, kills `ι v`; unpadding kills `v`. -/
theorem nk2Slice_dies_of_level
    (hres : ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
      ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P)
    {n : ℕ} (h : nk2Slice_LevelStatement A n) : nk2Slice_DiesStatement A n := by
  intro N hN v hv
  refine diesAfterPadding_of_diesAfterPadding_castLEEmb (Nat.le_add_right N 1) ?_
  have htop : quillenIdeal
      (K2Map (MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom
        (K2Map (czCubeResFieldCone A n)
          (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v))) ⊔
      Ideal.span {(MvPolynomial.X (Fin.last n) - 1 : MvPolynomial (Fin (n + 1)) A)} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hp, hpM⟩ := hres (n + 1) M hM
    obtain ⟨s, hsM, hs⟩ := h N hN v hv p hp M hM hpM
      (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact hsM (hle (Ideal.mem_sup_left ((mem_quillenIdeal _ s).mpr hs)))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp htop)
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  have hεa : nk2Core_sliceRetract A n a = 1 := by
    have h1 := congrArg (nk2Core_sliceRetract A n) hab
    rwa [map_add, map_mul, map_sub, map_one, nk2Core_sliceRetract_X_last, sub_self, mul_zero,
      add_zero] at h1
  have hd := diesAfterPadding_K2Map
    (Polynomial.mapRingHom (Polynomial.mapRingHom (nk2Core_sliceRetract A n)))
    ((mem_quillenIdeal _ a).mp ha)
  rw [nk2Core_K2Map_quillenDiff, hεa,
    K2Map_K2Map (MvPolynomial.finSuccEquiv A (n + 1)).toRingEquiv.toRingHom
      (czCubeResFieldCone A n),
    K2Map_K2Map (Polynomial.mapRingHom (nk2Core_sliceRetract A n)),
    nk2Core_sliceRetract_comp_cone] at hd
  have hev : K2Map (Polynomial.evalRingHom 0 :
      Polynomial (MvPolynomial (Fin n) A) →+* MvPolynomial (Fin n) A)
        (K2Map (MvPolynomial.finSuccEquiv A n).toRingEquiv.toRingHom
          (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v)) = 1 := by
    rw [K2Map_K2Map, ← evalZero_finSuccEquiv_comp_cubeKill_zero (R := A) n, ← K2Map_K2Map,
      czNK2_cubeKill_pad A hv 0, map_one]
  have hdu := diesAfterPadding_K2Map (MvPolynomial.finSuccEquiv A n).toRingEquiv.symm.toRingHom
    (diesAfterPadding_of_one_mem_quillenIdeal hev ((mem_quillenIdeal _ 1).mpr hd))
  rwa [K2Map_K2Map_of_comp_eq_id _ _
    (MvPolynomial.finSuccEquiv A n).toRingEquiv.symm_toRingHom_comp_toRingHom] at hdu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Slice_dies_of_level

/-- **Death descends one level.**  Death at level `n + 1` gives death at level `n`: the cone
`j : s_0 ↦ s_0 s_{n+1}` sends the padded cube element `ι v ∈ K₂(n + 6, A[s_0..s_n])` to a cube
element of `K₂((n + 1) + 5, A[s_0..s_{n+1}])`, which dies; the retraction `r` (`r ∘ j = id`)
brings the death back to `ι v`, and unpadding to `v`.  Ring-generic, no hypothesis. -/
theorem nk2Slice_dies_of_dies_succ {n : ℕ} (h : nk2Slice_DiesStatement A (n + 1)) :
    nk2Slice_DiesStatement A n := by
  intro N hN v hv
  refine diesAfterPadding_of_diesAfterPadding_castLEEmb (Nat.le_add_right N 1) ?_
  have hw := h (N + 1) (by omega)
    (K2Map (czCubeResFieldCone A n) (K2IndexMap (Fin.castLEEmb (Nat.le_add_right N 1)) v))
    (czCubeResField_K2Map_cubeKill_cone (czNK2_cubeKill_pad A hv))
  have hd := diesAfterPadding_K2Map (czCubeResFieldConeRetract A n) hw
  rwa [K2Map_K2Map_of_comp_eq_id _ _ (czCubeResField_retract_comp_cone A n)] at hd

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Slice_dies_of_dies_succ

/-- Death at any level `n' ≥ n` gives death at level `n` (induction on `n'` from `n`). -/
theorem nk2Slice_dies_of_dies_le {n n' : ℕ} (hle : n ≤ n') (h : nk2Slice_DiesStatement A n') :
    nk2Slice_DiesStatement A n :=
  Nat.le_induction (m := n)
    (P := fun k _ ↦ nk2Slice_DiesStatement A k → nk2Slice_DiesStatement A n)
    (fun h ↦ h) (fun _ _ ih h ↦ ih (nk2Slice_dies_of_dies_succ A h)) n' hle h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Slice_dies_of_dies_le

/-- Given `hres`, death at level `n` and the slice residual at level `n` are equivalent. -/
theorem nk2Slice_level_iff_dies
    (hres : ∀ k : ℕ, ∀ P : Ideal (MvPolynomial (Fin k) A), P.IsMaximal →
      ∃ p : ℕ, p.Prime ∧ (p : MvPolynomial (Fin k) A) ∈ P) (n : ℕ) :
    nk2Slice_LevelStatement A n ↔ nk2Slice_DiesStatement A n :=
  ⟨nk2Slice_dies_of_level A hres, nk2Slice_level_of_dies A⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Slice_level_iff_dies

end Over

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
