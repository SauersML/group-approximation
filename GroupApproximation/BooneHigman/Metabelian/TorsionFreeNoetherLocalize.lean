import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.RingTheory.MvPolynomial.Basic
import GroupApproximation.BooneHigman.Primary.Coprimary
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeNoetherTranscendence
import GroupApproximation.BooneHigman.Metabelian.TorsionFreeNoetherFinite
import GroupApproximation.Meta.AxiomGuard

/-!
# Torsion-free linearity, coprimary case: generic localization (lane bh-met-43)

Let `A` be a commutative ring generated (as a ring) by a finite set `t`, `W` a finitely
generated `A`-module that is coprimary with `(P, e)`, and suppose `P` contains no nonzero integer.

* `noether_exists_transcendence_lift` gives `g : D = ℤ[ι] → A` with `g d ∉ P` for `d ≠ 0`, and
  every `a : A` a root modulo `P` of a nonzero `p ∈ D[X]`.
* Put `S = g(D⁰)`, `B = S⁻¹A`, `M = S⁻¹W`, `K = Frac D`, `φ : K → B` the induced map.
* `W → M` is injective: elements of `S` lie outside `P`, so they act injectively on `W`.
* `B` is generated over `K` by the images of `t`, and `p^e` (mapped to `K`) kills `M` at the
  image of `a ∈ t` because `p(a)^e ∈ P^e` kills `W`.  So `M` is finite-dimensional over `K`
  (`noether_finiteDimensional_of_adjoin`), and `A` acts on `M` by `K`-linear maps.

* `noether_exists_fd_embedding`: the endpoint.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace Coprimary

/-- **Generic localization.** A finitely generated coprimary module over a finitely generated
commutative ring, whose prime contains no nonzero integer, embeds `A`-equivariantly into a
finite-dimensional vector space over a field of characteristic zero on which `A` acts linearly. -/
theorem noether_exists_fd_embedding {A W : Type} [CommRing A] [AddCommGroup W] [Module A W]
    [Module.Finite A W] (t : Set A) (ht : t.Finite) (hcl : Subring.closure t = ⊤)
    (P : Ideal A) (e : ℕ) (hW : Primary.IsCoprimaryWith A W P e)
    (hP : ∀ n : ℤ, n ≠ 0 → (n : A) ∉ P) :
    ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V),
      ringChar K = 0 ∧ FiniteDimensional K V ∧
      ∃ (τ : A →* Module.End K V) (ι₀ : W →+ V), Function.Injective ι₀ ∧
        ∀ (a : A) (w : W), ι₀ (a • w) = τ a (ι₀ w) := by
  obtain ⟨ι, g, hgP, halg⟩ := noether_exists_transcendence_lift P hP
  obtain ⟨S, hSP, hgS, hSg⟩ : ∃ S : Submonoid A, (∀ s ∈ S, s ∉ P) ∧
      (∀ d ∈ nonZeroDivisors (MvPolynomial ι ℤ), g d ∈ S) ∧
      ∀ s ∈ S, ∃ d ∈ nonZeroDivisors (MvPolynomial ι ℤ), g d = s := by
    refine ⟨(nonZeroDivisors (MvPolynomial ι ℤ)).map g, fun s hs => ?_,
      fun d hd => Submonoid.mem_map_of_mem g hd, fun s hs => Submonoid.mem_map.1 hs⟩
    obtain ⟨d, hd, rfl⟩ := Submonoid.mem_map.1 hs
    exact hgP d (nonZeroDivisors.ne_zero hd)
  obtain ⟨φ, hφ⟩ : ∃ φ : FractionRing (MvPolynomial ι ℤ) →+* Localization S, ∀ d,
      φ (algebraMap (MvPolynomial ι ℤ) (FractionRing (MvPolynomial ι ℤ)) d) =
        algebraMap A (Localization S) (g d) :=
    ⟨IsLocalization.map (M := nonZeroDivisors (MvPolynomial ι ℤ)) (Localization S) g
      (fun d hd => hgS d hd),
      fun d => IsLocalization.map_eq _ d⟩
  letI : Algebra (FractionRing (MvPolynomial ι ℤ)) (Localization S) := φ.toAlgebra
  letI instKM : Module (FractionRing (MvPolynomial ι ℤ)) (LocalizedModule S W) :=
    Module.compHom (LocalizedModule S W)
      (algebraMap (FractionRing (MvPolynomial ι ℤ)) (Localization S))
  haveI : IsScalarTower (FractionRing (MvPolynomial ι ℤ)) (Localization S)
      (LocalizedModule S W) := ⟨fun k b m => by
    exact mul_smul (algebraMap (FractionRing (MvPolynomial ι ℤ)) (Localization S) k) b m⟩
  -- the action of `A` on `M` by a scalar: the basic computation on fractions
  have hmk : ∀ (r : A) (w : W) (s : S), algebraMap A (Localization S) r •
      LocalizedModule.mk w s = LocalizedModule.mk (r • w) s := by
    intro r w s
    rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk, one_mul]
  -- `B` is generated over `K` by the images of `t`
  have hA : ∀ a : A, algebraMap A (Localization S) a ∈
      Algebra.adjoin (FractionRing (MvPolynomial ι ℤ)) (algebraMap A (Localization S) '' t) := by
    intro a
    have hle : Subring.closure t ≤ (Algebra.adjoin (FractionRing (MvPolynomial ι ℤ))
        (algebraMap A (Localization S) '' t)).toSubring.comap (algebraMap A (Localization S)) :=
      Subring.closure_le.2 fun x hx => Subring.mem_comap.2 (Subalgebra.mem_toSubring.2
        (Algebra.subset_adjoin (Set.mem_image_of_mem (algebraMap A (Localization S)) hx)))
    have ha : a ∈ Subring.closure t := by
      rw [hcl]
      exact Subring.mem_top a
    exact Subalgebra.mem_toSubring.1 (Subring.mem_comap.1 (hle ha))
  have hadj : Algebra.adjoin (FractionRing (MvPolynomial ι ℤ))
      (algebraMap A (Localization S) '' t) = ⊤ := by
    refine eq_top_iff.2 fun b _ => ?_
    obtain ⟨a, s, hb⟩ := IsLocalization.exists_mk'_eq S b
    obtain ⟨d, hd, hds⟩ := hSg s s.2
    have hc : algebraMap (MvPolynomial ι ℤ) (FractionRing (MvPolynomial ι ℤ)) d ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have hinv : IsLocalization.mk' (Localization S) (1 : A) s =
        φ (algebraMap (MvPolynomial ι ℤ) (FractionRing (MvPolynomial ι ℤ)) d)⁻¹ := by
      rw [IsLocalization.mk'_eq_iff_eq_mul, map_one, ← hds, ← hφ, ← map_mul, inv_mul_cancel₀ hc,
        map_one]
    rw [← hb, IsLocalization.mk'_eq_mul_mk'_one, hinv]
    exact Subalgebra.mul_mem _ (hA a)
      (Subalgebra.algebraMap_mem _ (algebraMap (MvPolynomial ι ℤ)
        (FractionRing (MvPolynomial ι ℤ)) d)⁻¹)
  have hcompφ : (algebraMap (FractionRing (MvPolynomial ι ℤ)) (Localization S)).comp
      (algebraMap (MvPolynomial ι ℤ) (FractionRing (MvPolynomial ι ℤ))) =
        (algebraMap A (Localization S)).comp g :=
    RingHom.ext fun d => hφ d
  -- each generator of `B` is killed on `M` by a nonzero polynomial over `K`
  have hkill : ∀ b ∈ algebraMap A (Localization S) '' t,
      ∃ p : Polynomial (FractionRing (MvPolynomial ι ℤ)), p ≠ 0 ∧
        ∀ m : LocalizedModule S W, Polynomial.aeval b p • m = 0 := by
    rintro _ ⟨a, -, rfl⟩
    obtain ⟨p, hp0, hpa⟩ := halg a
    refine ⟨(p ^ e).map (algebraMap (MvPolynomial ι ℤ) (FractionRing (MvPolynomial ι ℤ))),
      (Polynomial.map_ne_zero_iff (IsFractionRing.injective (MvPolynomial ι ℤ)
        (FractionRing (MvPolynomial ι ℤ)))).2 (pow_ne_zero e hp0), fun m => ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcompφ, ← Polynomial.hom_eval₂,
      Polynomial.eval₂_pow]
    refine LocalizedModule.induction_on (fun w s => ?_) m
    rw [hmk, hW.smul_eq_zero_of_mem_pow _ (Ideal.pow_mem_pow hpa e) w, LocalizedModule.zero_mk]
  have hfd : FiniteDimensional (FractionRing (MvPolynomial ι ℤ)) (LocalizedModule S W) :=
    noether_finiteDimensional_of_adjoin (algebraMap A (Localization S) '' t) (ht.image _) hadj
      hkill
  -- `A` acts on `M` by `K`-linear maps
  obtain ⟨τ, hτ⟩ : ∃ τ : A →* Module.End (FractionRing (MvPolynomial ι ℤ)) (LocalizedModule S W),
      ∀ (a : A) (m : LocalizedModule S W), τ a m = algebraMap A (Localization S) a • m :=
    ⟨{ toFun := fun a =>
          { toFun := fun m => algebraMap A (Localization S) a • m
            map_add' := fun m m' => smul_add _ m m'
            map_smul' := fun k m => by
              show algebraMap A (Localization S) a •
                  (algebraMap (FractionRing (MvPolynomial ι ℤ)) (Localization S) k • m) =
                algebraMap (FractionRing (MvPolynomial ι ℤ)) (Localization S) k •
                  (algebraMap A (Localization S) a • m)
              rw [smul_smul, smul_smul, mul_comm] }
        map_one' := LinearMap.ext fun m => by
          show algebraMap A (Localization S) 1 • m = m
          rw [map_one, one_smul]
        map_mul' := fun a a' => LinearMap.ext fun m => by
          show algebraMap A (Localization S) (a * a') • m =
            algebraMap A (Localization S) a • (algebraMap A (Localization S) a' • m)
          rw [map_mul, mul_smul] }, fun _ _ => rfl⟩
  -- `W → M` is injective
  have hinj : Function.Injective (LocalizedModule.mkLinearMap S W) := by
    intro w w' h
    rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.mkLinearMap_apply,
      LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    rw [one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def] at hu
    exact hW.smul_injective_of_notMem u (hSP u u.2) hu
  refine ⟨FractionRing (MvPolynomial ι ℤ), inferInstance, LocalizedModule S W, inferInstance,
    instKM, ringChar.eq_zero, hfd, τ, (LocalizedModule.mkLinearMap S W).toAddMonoidHom, hinj,
    fun a w => ?_⟩
  rw [hτ]
  show LocalizedModule.mk (a • w) 1 = algebraMap A (Localization S) a • LocalizedModule.mk w 1
  rw [hmk]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Coprimary.noether_exists_fd_embedding

end Coprimary
end Metabelian
end BooneHigman
end GroupApproximation
