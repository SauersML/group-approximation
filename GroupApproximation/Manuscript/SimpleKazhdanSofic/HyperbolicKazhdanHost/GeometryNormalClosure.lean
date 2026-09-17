import GroupApproximation.Manuscript.SimpleKazhdanSofic.HyperbolicKazhdanHost.Admissible
import GroupApproximation.GGT.ElementaryCentralizerAxis
import GroupApproximation.GGT.ElementaryMorseOrbit
import GroupApproximation.GGT.ElementaryIndependence
import GroupApproximation.GGT.OsinTheorem11
import GroupApproximation.GGT.HullYiFiniteRadicalDetector
import GroupApproximation.GGT.HullSCQuotientSuitabilityWithTorsion
import GroupApproximation.Meta.AxiomGuard

/-!
# Normal closures are suitable: clause G2

`simple_kazhdan_sofic_group.tex`, section "LEF groups", tex l.477–481 (census row
`fc84c012b409`):

> Without LEF, every countable group embeds in a finitely generated simple group~\cite{Gorjuskin,Schupp},
> and even in a simple quotient of a torsion-free hyperbolic Kazhdan group~\cite[Theorem~1.5]{CoulonFournierFacio},
> so one simple Kazhdan group contains Higman's universal finitely presented group~\cite{Higman}.

This module proves clause G2 of `CoulonFournierFacioGeometryStatement`. Let `A` be a Hull
generating set of `Q` and suppose some subgroup `N` of `Q` is suitable over `A`. Then for every
`x ≠ 1`, the normal closure of `x` is suitable over `A`.

## The route

This is the general form of Osin's Lemma 7.1 together with Hull's Lemma 3.9. The corpus proves
all of the geometry it needs.

* **Every nontrivial normal subgroup `M` is infinite.** Otherwise `M` is a finite subgroup
  normalized by `Q`, hence by `N`, so it is trivial.
* **`M` acts non-elementarily.** An infinite normal subgroup is s-normal. By
  `GGT.Elementary.actsNonElementarily_of_isSNormal_of_centralizer`, an s-normal subgroup of a
  group acting non-elementarily and acylindrically on `Γ(Q, A)` acts non-elementarily. The
  inputs to that theorem are proved for every Hull generating set: Osin's classification, the
  Morse centralizer estimate, independence, and virtual cyclicity of `E(g)`.
* **`M` normalizes no nontrivial finite subgroup.**
  * Let `R` be the loxodromic radical of `M`, that is, the intersection of `E(h)` over the
    loxodromic `h ∈ M` (`HullSC.loxRadical`).
  * `R` is finite: it lies inside `E(a) ∩ E(b)` for two independent loxodromics `a, b ∈ M`.
  * `R` is normalized by all of `Q`, since `M` is normal and `E(·)` is conjugation-equivariant.
    So `R` is normalized by `N`, and therefore `R = 1`.
  * Let `F` be a finite subgroup normalized by `M`. Each `h ∈ M` has a power centralizing a given
    `f ∈ F` (`HullSC.exists_pow_commute_of_normalizes_finite`), so `f ∈ E(h)`. Hence `F ≤ R = 1`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace HyperbolicKazhdanHost

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

section NormalClosure

variable {Q : Type} [Group Q]

/-- **A nontrivial normal subgroup is suitable** as soon as some subgroup is. -/
theorem suitable_of_normal (A : HullGeneratingSet Q) {N : Subgroup Q}
    (hN : Suitable A.alphabet N) {M : Subgroup Q} (hM : M.Normal) (hMbot : M ≠ ⊥) :
    Suitable A.alphabet M := by
  have hNNF := hN.normalizesNoNontrivialFinite
  -- `M` is infinite
  have hMinf : (M : Set Q).Infinite := by
    intro hfin
    exact hMbot (hNNF M hfin.to_subtype (fun s _ y hy => hM.conj_mem y hy s))
  -- so `M` is s-normal
  have hMs : HullSuitable.IsSNormal M := by
    intro g
    refine Set.Infinite.mono ?_ hMinf
    intro y hy
    show y ∈ M ∧ g * y * g⁻¹ ∈ M
    exact ⟨hy, hM.conj_mem y hy g⟩
  -- so `M` acts non-elementarily
  have hne : ActsNonElementarily M (Cayley.base A.alphabet) :=
    GGT.Elementary.actsNonElementarily_of_isSNormal_of_centralizer A.isometric A.acylindrical
      (GGT.OsinClassification.hasLoxodromicOfUnbounded_cayley A)
      (GGT.ElementaryMorse.independentOfNoCommonZpow_cayley A)
      (HullSC.elementaryClosureVirtuallyCyclic_hullGeneratingSet A)
      (GGT.Elementary.noIndependentPairInCentralizer_of_orbitNearAxis A.isometric
        A.acylindrical (GGT.ElementaryMorse.centralizerOrbitNearAxis_cayley A))
      A.nonElementary hMs
  refine ⟨hne, ?_⟩
  obtain ⟨a, haM, b, hbM, halox, hblox, hind⟩ := hne
  have hvc := HullSC.elementaryClosureVirtuallyCyclic_hullGeneratingSet A
  -- the loxodromic radical of `M` is finite
  have hRfin : ((HullSC.loxRadical A.alphabet M : Subgroup Q) : Set Q).Finite := by
    by_contra hinf
    exact GGT.Elementary.not_infinite_le_inf_elementaryClosure A.isometric hvc halox hblox
      hind (HullSC.loxRadical_le haM halox) (HullSC.loxRadical_le hbM hblox) hinf
  -- it is normalized by all of `Q`
  have hRconj : ∀ g : Q, ∀ x ∈ HullSC.loxRadical A.alphabet M,
      g * x * g⁻¹ ∈ HullSC.loxRadical A.alphabet M := by
    intro g x hx
    refine HullSC.mem_loxRadical.mpr ?_
    intro h hhM hhlox
    have hconjM : g⁻¹ * h * g ∈ M := by
      have hc := hM.conj_mem h hhM g⁻¹
      rwa [inv_inv] at hc
    have hconjlox : IsLoxodromic (g⁻¹ * h * g) (Cayley.base A.alphabet) := by
      have hc := isLoxodromic_conj A.isometric (a := g⁻¹) hhlox
      rwa [inv_inv] at hc
    have hmem := HullSC.mem_loxRadical.mp hx (g⁻¹ * h * g) hconjM hconjlox
    have hconj := GGT.Elementary.mem_elementaryClosure_conj (a := g) hmem
    have heq : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
    rwa [heq] at hconj
  -- hence it is trivial
  have hRbot : HullSC.loxRadical A.alphabet M = ⊥ :=
    hNNF _ hRfin.to_subtype (fun s _ x hx => hRconj s x hx)
  -- every finite subgroup normalized by `M` lies in the radical
  intro F hF hnorm
  haveI := hF
  rw [Subgroup.eq_bot_iff_forall]
  intro f hf
  have hfR : f ∈ HullSC.loxRadical A.alphabet M := by
    refine HullSC.mem_loxRadical.mpr ?_
    intro h hhM _
    obtain ⟨n, hn, hcomm⟩ :=
      HullSC.exists_pow_commute_of_normalizes_finite (hnorm h hhM) hf
    have hc : Commute f (h ^ n) := (mul_inv_eq_iff_eq_mul.mp hcomm).symm
    have hmem : f ∈ GGT.Elementary.elementaryClosure (h ^ (n : ℤ)) := by
      rw [zpow_natCast]
      exact GGT.Elementary.mem_elementaryClosure_of_commute hc
    rwa [GGT.Elementary.elementaryClosure_zpow h (by omega : (n : ℤ) ≠ 0)] at hmem
  rw [hRbot, Subgroup.mem_bot] at hfR
  exact hfR

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.suitable_of_normal

/-- **Clause G2 of `CoulonFournierFacioGeometryStatement`.** Suppose some subgroup is suitable
over a Hull generating set `A`. Then the normal closure of any `x ≠ 1` is suitable over `A`. -/
theorem suitable_normalClosure (A : HullGeneratingSet Q) (N : Subgroup Q)
    (hN : Suitable A.alphabet N) (x : Q) (hx : x ≠ 1) :
    Suitable A.alphabet (Subgroup.normalClosure {x}) := by
  have hxmem : x ∈ Subgroup.normalClosure ({x} : Set Q) :=
    Subgroup.subset_normalClosure (Set.mem_singleton x)
  refine suitable_of_normal A hN
    (inferInstance : (Subgroup.normalClosure ({x} : Set Q)).Normal) ?_
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hxmem
  exact hx hxmem

#audit_axioms GroupApproximation.SimpleKazhdanSofic.HyperbolicKazhdanHost.suitable_normalClosure

end NormalClosure

end HyperbolicKazhdanHost
end SimpleKazhdanSofic
end GroupApproximation
