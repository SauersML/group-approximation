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
    ⟨IsLocalization.map (Localization S) g (fun d hd => hgS d hd),
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
      Subring.closure_le.2 fun x hx => Algebra.subset_adjoin ⟨x, hx, rfl⟩
    have ha : a ∈ Subring.closure t := by
      rw [hcl]
      exact Subring.mem_top a
    exact hle ha
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
