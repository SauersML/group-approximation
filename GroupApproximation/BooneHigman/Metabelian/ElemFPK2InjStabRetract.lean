import Mathlib.Algebra.MvPolynomial.Rename
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowParInjEndpoint
import GroupApproximation.Meta.AxiomGuard

/-!
# Injective `K₂` stability: naturality and transport along retracts

Lane `bh-met-80`, helper module.  Over arbitrary rings, with no hypothesis:

* `k2InjStab_K2Stab_K2Map`: coefficient maps commute with the stabilization
  `K2Stab n : K₂(n, -) → K₂(n+1, -)`.  This is `K2IndexMap_K2Map` along `Fin.castSuccEmb`.
* `k2InjStab_injective_of_retract`: let `f : R →+* S` have a left inverse `g`.  If
  `K2Stab n S` is injective, then so is `K2Stab n R`.  For `u` with `K2Stab n R u = 1`,
  naturality gives `K2Stab n S (f u) = f (K2Stab n R u) = 1`, so `f u = 1`, and then
  `u = g (f u) = 1`.

Polynomial-ring consequence:

* `k2InjStab_polyInjective_of_target`: `VdKRowParInjK2StabStatement` (injectivity of
  `K2Stab (k + 4)` over `R_k = F_p[s_1, …, s_k]`, `k > 0`; module
  `ElemFPK2VdKRowParInjEndpoint`) gives `PolyK2InjectiveStabilityStatement` (module
  `ElemFPK2Split`): injectivity of `K2Stab N` over `R_k` for all `k ≥ 0`, `N ≥ k + 4`, `N ≥ 5`.
  Put `k' = N - 4 ≥ max k 1`.  The renaming `R_k → R_{k'}` has the left inverse `killCompl`,
  so the diagonal case at `k'` transports to `R_k`.  The converse,
  `vdkRowParInjK2Stab_of_polyK2InjectiveStability`, already exists.  So the two statements are
  equivalent.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- Coefficient maps commute with the stabilization `K₂(n, -) → K₂(n+1, -)`. -/
theorem k2InjStab_K2Stab_K2Map {R S : Type*} [Ring R] [Ring S] {n : ℕ} (f : R →+* S)
    (u : K2n n R) : K2Stab n S (K2Map f u) = K2Map f (K2Stab n R u) :=
  K2IndexMap_K2Map (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) f u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2InjStab_K2Stab_K2Map

/-- **Injective stability passes to retracts.**  If `f : R →+* S` has a left inverse and
`K2Stab n S` is injective, then `K2Stab n R` is injective. -/
theorem k2InjStab_injective_of_retract {R S : Type*} [Ring R] [Ring S] {n : ℕ}
    (f : R →+* S) (g : S →+* R) (hgf : g.comp f = RingHom.id R)
    (h : Function.Injective (K2Stab n S)) : Function.Injective (K2Stab n R) := by
  refine (injective_iff_map_eq_one _).mpr fun u hu ↦ ?_
  have hv : K2Stab n S (K2Map f u) = 1 :=
    (k2InjStab_K2Stab_K2Map f u).trans
      ((DFunLike.congr_arg (K2Map (I := Fin (n + 1)) f) hu).trans
        (map_one (K2Map (I := Fin (n + 1)) f)))
  have hv1 : K2Map f u = 1 := h (hv.trans (map_one (K2Stab n S)).symm)
  calc u = K2Map g (K2Map f u) := (K2Map_K2Map_of_comp_eq_id g f hgf u).symm
    _ = K2Map g 1 := by rw [hv1]
    _ = 1 := map_one (K2Map (I := Fin n) g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2InjStab_injective_of_retract

/-- The diagonal target `VdKRowParInjK2StabStatement` gives injective stability at every rank
`N ≥ k + 4`, `N ≥ 5`, over `F_p[s_1, …, s_k]` for every `k ≥ 0`: add `N - 4 - k` dummy
variables. -/
theorem k2InjStab_polyInjective_of_target (h : VdKRowParInjK2StabStatement) :
    PolyK2InjectiveStabilityStatement := by
  intro p hp k N hkN h5N
  obtain ⟨k', rfl⟩ : ∃ k' : ℕ, N = k' + 4 := ⟨N - 4, by omega⟩
  have hkk : k ≤ k' := by omega
  exact k2InjStab_injective_of_retract
    (MvPolynomial.rename (R := ZMod p) (Fin.castLE hkk)).toRingHom
    (MvPolynomial.killCompl (R := ZMod p) (Fin.castLE_injective hkk)).toRingHom
    (RingHom.ext fun x ↦ MvPolynomial.killCompl_rename_app (Fin.castLE_injective hkk) x)
    (h p hp k' (by omega))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2InjStab_polyInjective_of_target

end GroupApproximation.BooneHigman.Metabelian.ElemFP
