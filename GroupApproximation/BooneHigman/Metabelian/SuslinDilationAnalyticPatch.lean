import GroupApproximation.BooneHigman.Metabelian.SuslinDilationAnalyticStepA
import GroupApproximation.BooneHigman.Metabelian.SuslinLocalGlobalCompose
import GroupApproximation.Meta.AxiomGuard

/-!
# Suslin dilation, analytic half, part 4: Suslin's dilation lemma

Lane `bh-met-76`.  Let `φ : B → S`, `s ∈ B` with

* every `c ∈ S` has `c φ(s)^t ∈ φ(B)` (`hsurj`), and
* `φ(b) = 0` forces `s^n b = 0` (`hker`)

(e.g. `B → B_s`).  **Dilation lemma** (`suslinDilAn_dilation`, `N ≥ 3`): if `σ ∈ GL_N(B[Y])`
has `σ(0) = 1` and `φ(σ) ∈ E_N(S[Y])`, then `σ(s^k Y) ∈ E_N(B[Y])` for some `k`.

Proof: the estimate of `SuslinDilationAnalyticStepA.lean` at level `0` puts
`φ(σ(s^k Y)) = φ(σ)(φ(s)^k Y)` into `φ(E_N(B[Y]))`, say `= φ(V)`.  Replacing `V` by
`V V(0)⁻¹`, every entry `d` of `σ(s^k Y) - V` has `d(0) = 0` and `φ(d) = 0`, so `s^n d = 0`,
so `d(s^n Y) = 0` (`suslinDilAn_dilate_eq_zero`): `σ(s^{n+k} Y) = V(s^n Y) ∈ E_N(B[Y])`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Absorption

section Kappa

variable {R : Type*} [CommRing R]

theorem suslinDilAn_constantCoeff_comp_kappa :
    (Polynomial.constantCoeff (R := R)).comp
        ((Polynomial.C : R →+* Polynomial R).comp (Polynomial.constantCoeff (R := R))) =
      Polynomial.constantCoeff (R := R) :=
  RingHom.ext fun p ↦ by
    simp only [RingHom.comp_apply, Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_constantCoeff_comp_kappa

theorem suslinDilAn_kappa_comp_dilate (u : R) :
    ((Polynomial.C : R →+* Polynomial R).comp (Polynomial.constantCoeff (R := R))).comp
        (suslinDilAnDilate u) =
      (Polynomial.C : R →+* Polynomial R).comp (Polynomial.constantCoeff (R := R)) := by
  rw [RingHom.comp_assoc, suslinDilAnDilate_constantCoeff]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_kappa_comp_dilate

theorem suslinDilAn_map_apply {R' : Type*} [CommRing R'] {N : ℕ} (f : R →+* R')
    (u : (Matrix (Fin N) (Fin N) R)ˣ) (i j : Fin N) :
    (elementaryMatrixUnitMap (ι := Fin N) f u : Matrix (Fin N) (Fin N) R') i j =
      f ((u : Matrix (Fin N) (Fin N) R) i j) :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_map_apply

end Kappa

section Patch

variable {B S : Type*} [CommRing B] [CommRing S] (φ : B →+* S) (s : B) {N : ℕ}

theorem suslinDilAn_constantCoeff_comp_map :
    (Polynomial.constantCoeff (R := S)).comp (Polynomial.mapRingHom φ) =
      φ.comp (Polynomial.constantCoeff (R := B)) :=
  RingHom.ext fun p ↦ by
    simp only [RingHom.comp_apply, Polynomial.constantCoeff_apply, Polynomial.coe_mapRingHom,
      Polynomial.coeff_map]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_constantCoeff_comp_map

theorem suslinDilAn_map_comp_kappa :
    (Polynomial.mapRingHom φ).comp
        ((Polynomial.C : B →+* Polynomial B).comp (Polynomial.constantCoeff (R := B))) =
      ((Polynomial.C : S →+* Polynomial S).comp (Polynomial.constantCoeff (R := S))).comp
        (Polynomial.mapRingHom φ) :=
  RingHom.ext fun p ↦ by
    simp only [RingHom.comp_apply, Polynomial.constantCoeff_apply, Polynomial.coe_mapRingHom,
      Polynomial.map_C, Polynomial.coeff_map]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_map_comp_kappa

/-- **Patching**: two matrices with the same constant term `1` and the same image under `φ`
agree after a dilation `Y ↦ s^n Y`. -/
theorem suslinDilAn_patch (hker : ∀ b : B, φ b = 0 → ∃ n : ℕ, s ^ n * b = 0)
    {U V : (Matrix (Fin N) (Fin N) (Polynomial B))ˣ}
    (hV : V ∈ elementaryGroup (Fin N) (Polynomial B))
    (hU0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := B)) U = 1)
    (hV0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := B)) V = 1)
    (hUV : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom φ) U =
      elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom φ) V) :
    ∃ n : ℕ, elementaryMatrixUnitMap (ι := Fin N) (suslinDilAnDilate (s ^ n)) U ∈
      elementaryGroup (Fin N) (Polynomial B) := by
  have h0 : ∀ i j : Fin N, Polynomial.constantCoeff
      ((U : Matrix (Fin N) (Fin N) (Polynomial B)) i j -
        (V : Matrix (Fin N) (Fin N) (Polynomial B)) i j) = 0 := by
    intro i j
    have hU := congrArg (fun w : (Matrix (Fin N) (Fin N) B)ˣ ↦
      (w : Matrix (Fin N) (Fin N) B) i j) hU0
    have hV := congrArg (fun w : (Matrix (Fin N) (Fin N) B)ˣ ↦
      (w : Matrix (Fin N) (Fin N) B) i j) hV0
    simp only [suslinDilAn_map_apply] at hU hV
    rw [map_sub, hU, hV, sub_self]
  have hd : ∀ i j : Fin N, ∃ n : ℕ, Polynomial.C s ^ n *
      ((U : Matrix (Fin N) (Fin N) (Polynomial B)) i j -
        (V : Matrix (Fin N) (Fin N) (Polynomial B)) i j) = 0 := by
    intro i j
    refine suslinDilAn_ker_poly φ s hker _ ?_
    have h := congrArg (fun w : (Matrix (Fin N) (Fin N) (Polynomial S))ˣ ↦
      (w : Matrix (Fin N) (Fin N) (Polynomial S)) i j) hUV
    simp only [suslinDilAn_map_apply] at h
    rw [map_sub, h, sub_self]
  choose n hn using hd
  set m := Finset.univ.sup fun p : Fin N × Fin N ↦ n p.1 p.2
  have hDUV : elementaryMatrixUnitMap (ι := Fin N) (suslinDilAnDilate (s ^ m)) U =
      elementaryMatrixUnitMap (ι := Fin N) (suslinDilAnDilate (s ^ m)) V := by
    apply Units.ext
    ext i j
    rw [suslinDilAn_map_apply, suslinDilAn_map_apply, ← sub_eq_zero, ← map_sub]
    refine suslinDilAn_dilate_eq_zero (h0 i j) ?_
    rw [Polynomial.C_pow]
    exact suslinDilAn_C_pow_mul_mono (hn i j)
      (Finset.le_sup (f := fun p : Fin N × Fin N ↦ n p.1 p.2) (Finset.mem_univ (i, j)))
  refine ⟨m, ?_⟩
  rw [hDUV]
  exact elementaryGroup_map_le (ι := Fin N) (suslinDilAnDilate (s ^ m))
    (Subgroup.mem_map_of_mem _ hV)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_patch

/-- **Suslin's dilation lemma** (`N ≥ 3`): if `σ(0) = 1` and `φ(σ) ∈ E_N(S[Y])`, then
`σ(s^k Y) ∈ E_N(B[Y])` for some `k`. -/
theorem suslinDilAn_dilation (hN : 2 < N)
    (hsurj : ∀ c : S, ∃ (t : ℕ) (a : B), c * φ s ^ t = φ a)
    (hker : ∀ b : B, φ b = 0 → ∃ n : ℕ, s ^ n * b = 0)
    (σ : (Matrix (Fin N) (Fin N) (Polynomial B))ˣ)
    (hσ0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := B)) σ = 1)
    (hσ : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom φ) σ ∈
      elementaryGroup (Fin N) (Polynomial S)) :
    ∃ k : ℕ, elementaryMatrixUnitMap (ι := Fin N) (suslinDilAnDilate (s ^ k)) σ ∈
      elementaryGroup (Fin N) (Polynomial B) := by
  obtain ⟨k₀, hk₀⟩ := suslinDilAn_estimate_of_mem φ s hN hsurj hσ 0
  have hk := hk₀ k₀ le_rfl
  have hκ : elementaryMatrixUnitMap (ι := Fin N)
      ((Polynomial.C : S →+* Polynomial S).comp (Polynomial.constantCoeff (R := S)))
        (elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom φ) σ) = 1 := by
    rw [← suslinLocalGlobal_map_map (Polynomial.C : S →+* Polynomial S)
        (Polynomial.constantCoeff (R := S)),
      suslinLocalGlobal_map_map (Polynomial.constantCoeff (R := S)) (Polynomial.mapRingHom φ),
      suslinDilAn_constantCoeff_comp_map,
      ← suslinLocalGlobal_map_map φ (Polynomial.constantCoeff (R := B)), hσ0, map_one, map_one]
  have hcomm : elementaryMatrixUnitMap (ι := Fin N) (suslinDilAnDilate (φ s ^ k₀))
      (elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom φ) σ) =
        elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom φ)
          (elementaryMatrixUnitMap (ι := Fin N) (suslinDilAnDilate (s ^ k₀)) σ) := by
    rw [suslinLocalGlobal_map_map, suslinLocalGlobal_map_map, ← map_pow,
      suslinDilAnDilate_comp_mapRingHom]
  rw [hκ, inv_one, mul_one, hcomm] at hk
  obtain ⟨V, hV, hVU⟩ := Subgroup.mem_map.1
    (suslinDilAnLevel_le_map (Polynomial.mapRingHom φ) (Polynomial.C s) 0 hk)
  have hκV : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom φ)
      (elementaryMatrixUnitMap (ι := Fin N)
        ((Polynomial.C : B →+* Polynomial B).comp (Polynomial.constantCoeff (R := B))) V) = 1 := by
    rw [suslinLocalGlobal_map_map, suslinDilAn_map_comp_kappa, ← suslinLocalGlobal_map_map, hVU,
      ← hcomm, suslinLocalGlobal_map_map, suslinDilAn_kappa_comp_dilate, hκ]
  have hV' : V * (elementaryMatrixUnitMap (ι := Fin N)
      ((Polynomial.C : B →+* Polynomial B).comp (Polynomial.constantCoeff (R := B))) V)⁻¹ ∈
        elementaryGroup (Fin N) (Polynomial B) :=
    mul_mem hV (inv_mem (elementaryGroup_map_le (ι := Fin N)
      ((Polynomial.C : B →+* Polynomial B).comp (Polynomial.constantCoeff (R := B)))
      (Subgroup.mem_map_of_mem _ hV)))
  have hV'0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := B))
      (V * (elementaryMatrixUnitMap (ι := Fin N)
        ((Polynomial.C : B →+* Polynomial B).comp (Polynomial.constantCoeff (R := B))) V)⁻¹) =
          1 := by
    rw [map_mul, map_inv, suslinLocalGlobal_map_map, suslinDilAn_constantCoeff_comp_kappa,
      mul_inv_cancel]
  have hV'U : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom φ)
      (elementaryMatrixUnitMap (ι := Fin N) (suslinDilAnDilate (s ^ k₀)) σ) =
        elementaryMatrixUnitMap (ι := Fin N) (Polynomial.mapRingHom φ)
          (V * (elementaryMatrixUnitMap (ι := Fin N)
            ((Polynomial.C : B →+* Polynomial B).comp (Polynomial.constantCoeff (R := B))) V)⁻¹) := by
    rw [map_mul, map_inv, hκV, inv_one, mul_one, hVU]
  have hU0 : elementaryMatrixUnitMap (ι := Fin N) (Polynomial.constantCoeff (R := B))
      (elementaryMatrixUnitMap (ι := Fin N) (suslinDilAnDilate (s ^ k₀)) σ) = 1 := by
    rw [suslinLocalGlobal_map_map, suslinDilAnDilate_constantCoeff, hσ0]
  obtain ⟨n, hn⟩ := suslinDilAn_patch φ s hker hV' hU0 hV'0 hV'U
  refine ⟨n + k₀, ?_⟩
  rw [pow_add, ← suslinDilAnDilate_comp, ← suslinLocalGlobal_map_map]
  exact hn

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Absorption.suslinDilAn_dilation

end Patch

end Absorption
end Metabelian
end BooneHigman
end GroupApproximation
