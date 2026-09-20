import GroupApproximation.BooneHigmanLinear.CharZero.BTri.StepFG
import GroupApproximation.BooneHigmanLinear.CharZero.BTri.StepInputs
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.ZInv
import GroupApproximation.BooneHigman.Metabelian.SuslinKillLift
import GroupApproximation.BooneHigman.Metabelian.AbsorptionSuslinEuclidInstances
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGen
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngTorusOne
import GroupApproximation.BooneHigman.Metabelian.ElemFPCzBaseFGSqfree
import GroupApproximation.Meta.AxiomGuard

/-!
# Z1-base from the building inputs (piece Z.6, wiring)

`StepInputs A p` collects what the Bruhat–Tits building of `SL₃(A[1/p])` supplies: the
type-preserving action with the standard chamber as strict fundamental domain, connectivity,
simple connectivity, and `Stab(s₀) = SL₃(A)`. `BuildingInputsStatement` asks for them for every
principal ideal domain `A` and prime `p`. The stabilizer is proved in `DomainStabilizer`;
`buildingInputs_of` therefore needs only the triangle action and simple connectivity.

From these inputs:

* `fng_of_twisted`: the twisted step (`twisted_step`, with `edge_fg`) makes `K₂(3, A[1/p])`
  finitely normally generated when `K₂(3, A)` is;
* `fng_of_ringEquiv`, `fng_of_away_mul`: this transfers along `ℤ[1/m][1/p] ≅ ℤ[1/mp]`;
* `fng_away_of_inputs`: prime induction from `K₂(3, ℤ)` (`czK2FngTorus_k2ThreeOne_fng`);
* `baseFG_of_inputs`: `CharZeroK2BaseFGStatement`, through the corpus reductions
  `czBaseFG_sqfreeFour_of_rankThree` and `czBaseFG_baseFG_of_sqfreeFour`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace BTri

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.BooneHigman.Metabelian

/-- `u ↦ δᵢ(ι u)`. -/
noncomputable def twistMap {A : Type*} [CommRing A] (p : A) (i : Fin 3) :
    SteinbergGroup (Fin 3) A →* SteinbergGroup (Fin 3) (Localization.Away p) :=
  (twist A p i).comp (ringMap (algebraMap A (Localization.Away p)))

/-- **The twisted step gives finite normal generation.** -/
theorem fng_of_twisted {A : Type*} [CommRing A] {p : A}
    (hA : (K2 (Fin 3) A).IsFinitelyNormallyGenerated)
    (hstep : ∃ s : Set (SteinbergGroup (Fin 3) (Localization.Away p)), s.Finite ∧
      s ⊆ K2 (Fin 3) (Localization.Away p) ∧
      K2 (Fin 3) (Localization.Away p) ≤ Subgroup.normalClosure (twistedK2 A p ∪ s)) :
    (K2 (Fin 3) (Localization.Away p)).IsFinitelyNormallyGenerated := by
  obtain ⟨t, htfin, ht⟩ := hA
  obtain ⟨s, hsfin, hsK, hle⟩ := hstep
  refine ⟨(⋃ i, twistMap p i '' t) ∪ s,
    (Set.finite_iUnion fun i => htfin.image _).union hsfin, le_antisymm ?_ ?_⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro x (hx | hx)
    · obtain ⟨i, u, hu, rfl⟩ := Set.mem_iUnion.mp hx
      have hu' : u ∈ K2 (Fin 3) A := by
        rw [← ht]
        exact Subgroup.subset_normalClosure hu
      exact dgHom_mem_K2 (dvec A p i) (ringMap_mem_K2 (algebraMap A (Localization.Away p)) hu')
    · exact hsK hx
  · refine hle.trans (Subgroup.normalClosure_le_normal ?_)
    rintro x (hx | hx)
    · unfold twistedK2 at hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hi
      have hu' : u ∈ Subgroup.normalClosure t := by
        rw [ht]
        exact hu
      have hmap : Subgroup.normalClosure t ≤ (Subgroup.normalClosure
          ((⋃ i, twistMap p i '' t) ∪ s)).comap (twistMap p i) := by
        refine Subgroup.normalClosure_le_normal fun v hv => ?_
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        exact Subgroup.subset_normalClosure
          (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i, v, hv, rfl⟩))
      exact Subgroup.mem_comap.mp (hmap hu')
    · exact Subgroup.subset_normalClosure (Set.mem_union_right _ hx)

#audit_axioms fng_of_twisted

/-- **Finite normal generation of `K₂(3, -)` transfers along ring isomorphisms.** -/
theorem fng_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (h : (K2 (Fin 3) R).IsFinitelyNormallyGenerated) :
    (K2 (Fin 3) S).IsFinitelyNormallyGenerated := by
  have hs : ∀ u : SteinbergGroup (Fin 3) S,
      ringMap e.toRingHom (ringMap e.symm.toRingHom u) = u := fun u => by
    have hc : e.toRingHom.comp e.symm.toRingHom = RingHom.id S :=
      RingHom.ext fun x => e.apply_symm_apply x
    rw [ringMap_ringMap, hc, ringMap_id, MonoidHom.id_apply]
  have hK : (K2 (Fin 3) R).map (ringMap e.toRingHom) = K2 (Fin 3) S := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr (K2_le_comap_ringMap _)) fun u hu => ?_
    exact Subgroup.mem_map.mpr ⟨_, ringMap_mem_K2 e.symm.toRingHom hu, hs u⟩
  rw [← hK]
  exact Subgroup.IsFinitelyNormallyGenerated.map h (f := ringMap e.toRingHom) fun u => ⟨_, hs u⟩

#audit_axioms fng_of_ringEquiv

/-- Transfer to `ℤ[1/mp]` from a localization of `ℤ` away from `pm`. -/
theorem fng_of_away_mul {T : Type} [CommRing T] [Algebra ℤ T] (m p : ℕ)
    (hT : IsLocalization.Away ((p : ℤ) * (m : ℤ)) T)
    (h : (K2 (Fin 3) T).IsFinitelyNormallyGenerated) :
    (K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))).IsFinitelyNormallyGenerated := by
  have h' : ((m * p : ℕ) : ℤ) = (p : ℤ) * (m : ℤ) := by push_cast; ring
  haveI : IsLocalization.Away ((m * p : ℕ) : ℤ) T := by
    rw [h']
    exact hT
  exact fng_of_ringEquiv (IsLocalization.algEquiv (Submonoid.powers ((m * p : ℕ) : ℤ)) T
    (Localization.Away ((m * p : ℕ) : ℤ))).toRingEquiv h

#audit_axioms fng_of_away_mul

/-- `p` stays prime in `ℤ[1/m]` when `p ∤ m`. -/
theorem prime_away {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hdvd : ¬p ∣ m) :
    Prime ((p : ℕ) : Localization.Away (m : ℤ)) := by
  haveI := CharZeroHost.charZero_away hm.ne'
  haveI := CharZeroHost.isDomain_away hm.ne'
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 : ((p : ℕ) : Localization.Away (m : ℤ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hspan : Ideal.span {((p : ℕ) : Localization.Away (m : ℤ))} =
      RingHom.ker (CharZeroHost.redAway hp hdvd) := by
    ext z
    rw [Ideal.mem_span_singleton, RingHom.mem_ker]
    constructor
    · rintro ⟨c, rfl⟩
      rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]
    · intro hz
      obtain ⟨y, hy⟩ := CharZeroHost.redAway_exists_eq_mul hp hdvd z hz
      exact ⟨y, hy⟩
  rw [← Ideal.span_singleton_prime h0, hspan]
  exact RingHom.ker_isPrime _

#audit_axioms prime_away

/-- **The one-prime step at `p ∤ m`**, from the building inputs. -/
theorem fng_step (hI : BuildingInputsStatement) {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hdvd : ¬p ∣ m) (hfng : (K2 (Fin 3) (Localization.Away (m : ℤ))).IsFinitelyNormallyGenerated) :
    (K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))).IsFinitelyNormallyGenerated := by
  haveI := CharZeroHost.isDomain_away hm.ne'
  haveI := Absorption.suslinKill_away_pid m
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hprime : Prime (algebraMap ℤ (Localization.Away (m : ℤ)) (p : ℤ)) := by
    rw [map_natCast]
    exact prime_away hm hp hdvd
  have hin := hI (Localization.Away (m : ℤ)) _ hprime
  obtain ⟨_, hA⟩ := hin.triangle
  have hinj : Function.Injective (algebraMap (Localization.Away (m : ℤ))
      (Localization.Away (algebraMap ℤ (Localization.Away (m : ℤ)) (p : ℤ)))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hprime.ne_zero)
  have hSL := Absorption.specialLinearInElementary_away m (N := 3) (by omega)
  haveI := ElemFPCharZero.czK2Fng_steinbergAway_fg m 3 (by omega)
  haveI := sl3_fg hSL
  have hr : ∀ a : Localization.Away (m : ℤ), CharZeroHost.redAway hp hdvd a = 0 →
      ∃ y, a = algebraMap ℤ (Localization.Away (m : ℤ)) (p : ℤ) * y := fun a ha => by
    obtain ⟨y, hy⟩ := CharZeroHost.redAway_exists_eq_mul hp hdvd a ha
    exact ⟨y, by rw [hy, map_natCast]⟩
  have hB := fng_of_twisted hfng (twisted_step hinj hin.stab hSL hA hin.connected
    hin.simplyConnected fun i j => edge_fg hin.stab hinj (CharZeroHost.redAway hp hdvd) hr i j)
  haveI : IsScalarTower ℤ (Localization.Away (m : ℤ))
      (Localization.Away (algebraMap ℤ (Localization.Away (m : ℤ)) (p : ℤ))) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  exact fng_of_away_mul m p (IsLocalization.Away.mul (Localization.Away (m : ℤ))
    (Localization.Away (algebraMap ℤ (Localization.Away (m : ℤ)) (p : ℤ))) (m : ℤ) (p : ℤ)) hB

#audit_axioms fng_step

/-- The step at `p ∣ m`: then `ℤ[1/mp] = ℤ[1/m]`. -/
theorem fng_step_of_dvd {m p : ℕ} (hdvd : p ∣ m)
    (hfng : (K2 (Fin 3) (Localization.Away (m : ℤ))).IsFinitelyNormallyGenerated) :
    (K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))).IsFinitelyNormallyGenerated := by
  obtain ⟨k, hk⟩ := hdvd
  have hmk : (m : ℤ) = (p : ℤ) * (k : ℤ) := by rw [hk, Nat.cast_mul]
  have h : IsUnit (algebraMap ℤ (Localization.Away (m : ℤ)) ((p : ℤ) * (k : ℤ))) := by
    rw [← hmk]
    exact IsLocalization.Away.algebraMap_isUnit (m : ℤ)
  rw [map_mul] at h
  haveI : IsLocalization.Away (algebraMap ℤ (Localization.Away (m : ℤ)) (p : ℤ))
      (Localization.Away (m : ℤ)) :=
    IsLocalization.away_of_isUnit_of_bijective _ (isUnit_of_mul_isUnit_left h)
      Function.bijective_id
  haveI : IsScalarTower ℤ (Localization.Away (m : ℤ)) (Localization.Away (m : ℤ)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  exact fng_of_away_mul m p (IsLocalization.Away.mul (Localization.Away (m : ℤ))
    (Localization.Away (m : ℤ)) (m : ℤ) (p : ℤ)) hfng

#audit_axioms fng_step_of_dvd

/-- **Prime induction**: `K₂(3, ℤ[1/n])` is finitely normally generated for every `n > 0`. -/
theorem fng_away_of_inputs (hI : BuildingInputsStatement) :
    ∀ n : ℕ, 0 < n → (K2 (Fin 3) (Localization.Away (n : ℤ))).IsFinitelyNormallyGenerated := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst h1
      exact ElemFPCharZero.czK2FngTorus_k2ThreeOne_fng
    · obtain ⟨p, hp, c, rfl⟩ : ∃ p : ℕ, p.Prime ∧ ∃ c : ℕ, n = c * p :=
        ⟨n.minFac, Nat.minFac_prime h1, n / n.minFac,
          (Nat.div_mul_cancel (Nat.minFac_dvd n)).symm⟩
      have hcpos : 0 < c := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn
      have hclt : c < c * p := (lt_mul_iff_one_lt_right hcpos).mpr hp.one_lt
      by_cases hdvd : p ∣ c
      · exact fng_step_of_dvd hdvd (ih c hclt hcpos)
      · exact fng_step hI hcpos hp hdvd (ih c hclt hcpos)

#audit_axioms fng_away_of_inputs

/-- The rank-three statement of the corpus. -/
theorem rankThree_of_inputs (hI : BuildingInputsStatement) :
    ElemFPCharZero.czK2FngGtOne_RankThreeStatement := fun m hm =>
  fng_away_of_inputs hI m (by omega)

#audit_axioms rankThree_of_inputs

/-- **Z1-base from the building inputs.** -/
theorem baseFG_of_inputs (hI : BuildingInputsStatement) :
    ElemFPCharZero.CharZeroK2BaseFGStatement :=
  ElemFPCharZero.czBaseFG_baseFG_of_sqfreeFour
    (ElemFPCharZero.czBaseFG_sqfreeFour_of_rankThree (rankThree_of_inputs hI))

#audit_axioms baseFG_of_inputs

end BTri
end BooneHigmanLinear
end GroupApproximation
