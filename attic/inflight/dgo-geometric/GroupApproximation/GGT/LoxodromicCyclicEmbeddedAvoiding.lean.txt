import GroupApproximation.GGT.HullYiCyclicProductClosure
import GroupApproximation.GGT.DGOLemma421FromUniform414
import GroupApproximation.GGT.DGOProposition414General
import GroupApproximation.GGT.HullTheorem316Assembly
import GroupApproximation.GGT.DGOCorollary427Full
import GroupApproximation.GGT.DGOProposition433Finite

/-!
# A loxodromic element with cyclic elementary closure avoiding a finite set

For an acylindrically hyperbolic group with no nontrivial finite normal
subgroup and a finite set `F`, this module produces one element `y` which is

* loxodromic on Hull's Cayley graph,
* of cyclic elementary closure, `E(y) = ⟨y⟩`,
* commensurable with no element of `F`, so that `⟨f⟩ ∩ ⟨y⟩ = 1` for every
  `f ∈ F`, and
* hyperbolically embedded as `⟨y⟩ ↪_h (G, X)` over a relative generating set
  `X` containing `F`, with `f⟨y⟩f⁻¹ ∩ ⟨y⟩ = 1` for every `f ∈ F` outside the
  identity.

This is the one construction two chains consume:

* **Property `P_naive`** (Abbott--Dahmani, arXiv:1610.04143, Proposition 1.3 and
  Theorem 2.2): the ping-pong partner is a large power of such a `y`, and what
  the ping-pong spends is that no nontrivial power of an element of `F` lies in
  `E(y)`.  `pow_mem_zpowers_eq_one` below is that clause.
* **Gerasimova--Osin's Lemma 4.2**: an infinite cyclic hyperbolically embedded
  subgroup `H` with `F ⊆ X` and `fHf⁻¹ ∩ H = 1`, which they obtain from
  Dahmani--Guirardel--Osin's Theorem 2.24, Proposition 2.10, Example 3.3(b),
  Proposition 4.35 and Corollary 4.27.  Here it comes from Hull's suitable
  cyclic pair with finite avoidance, whose producer is a theorem of the
  repository (`HullSC.yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b`,
  over the proved uniform DGO Proposition 4.14), then the cyclic embedding over
  Hull's alphabet (`HullSC.isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional`),
  then DGO Corollary 4.27 (`GGT.dgoCorollary427`) to add `F`, and DGO
  Proposition 4.33 (`GGT.finite_conj_inter_of_notMem`) for the conjugation
  clause.

The trivial finite radical is taken verbatim as
`∀ N : Subgroup G, N.Normal → Finite N → N = ⊥`, which is
`TorsionFreePrinted.HasTrivialFiniteRadical G` unfolded; it is what makes the
whole group suitable in Hull's sense.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (simplicity, unique trace and
stable rank one of `C*_r(Q)`, tex lines 1718--1736); certifies no printed
sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace CyclicEmbeddedChoice

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## Hull's generating set and the suitability of the whole group -/

/-- **The data of acylindrical hyperbolicity is a Hull generating set.** -/
theorem nonempty_hullGeneratingSet (G : Type) [Group G]
    [hG : IsAcylindricallyHyperbolic G] : Nonempty (HullGeneratingSet G) := by
  obtain ⟨A, δ, hδ, hacy, hne⟩ := hG.out
  exact ⟨⟨A, δ, hδ, hacy, hne⟩⟩

/-- **With no nontrivial finite normal subgroup, the whole group is suitable**
(Hull, Definition 1.4): it acts non-elementarily, and a finite subgroup it
normalizes is a finite normal subgroup. -/
theorem suitable_top_of_trivialFiniteRadical {G : Type} [Group G]
    (A : HullGeneratingSet G)
    (hrad : ∀ N : Subgroup G, N.Normal → Finite N → N = ⊥) :
    Suitable A.alphabet (⊤ : Subgroup G) := by
  refine ⟨A.nonElementary, ?_⟩
  intro F hF hnorm
  exact hrad F ⟨fun n hn g => hnorm g (Subgroup.mem_top g) n hn⟩ hF

/-! ## The loxodromic element -/

/-- **A loxodromic element with cyclic elementary closure, commensurable with
no element of a prescribed finite set, whose cyclic subgroup is hyperbolically
embedded over Hull's alphabet.** -/
theorem exists_loxodromic_cyclic_avoiding {G : Type} [Group G]
    (A : HullGeneratingSet G)
    (hrad : ∀ N : Subgroup G, N.Normal → Finite N → N = ⊥) (F : Finset G) :
    ∃ y : G, IsLoxodromic y (Cayley.base A.alphabet) ∧
      Elementary.elementaryClosure y = Subgroup.zpowers y ∧
      (∀ x ∈ F, ¬ HullSC.AreCommensurable y x) ∧
      (HullSC.coneOffFamily A.alphabet
        (fun _ : Unit => Subgroup.zpowers y)).IsHyperbolicallyEmbedded := by
  have hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{0} :=
    HullSC.yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b
      (OsinComponents.dgoLemma421b_of_uniform414
        OsinComponents.dgoProposition414Uniform)
  obtain ⟨g, _hgT, hlox, _hnc, hcyc, havoid⟩ :=
    hyi A (suitable_top_of_trivialFiniteRadical A hrad) F
  refine ⟨g true, hlox true, hcyc true, havoid true, ?_⟩
  exact HullSC.isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional
    A (fun _ : Unit => g true)
    (HullSC.pairwiseNonCommensurable_of_subsingleton (fun _ : Unit => g true))
    (fun _ => hlox true) (fun _ => hcyc true)

/-- **No nontrivial power of an element of `F` lies in `⟨y⟩`**, when `y` is
commensurable with no element of `F`.  This is the clause the ping-pong of
property `P_naive` spends, for elements of finite and of infinite order alike. -/
theorem pow_mem_zpowers_eq_one {G : Type} [Group G] {y : G} {F : Finset G}
    (havoid : ∀ x ∈ F, ¬ HullSC.AreCommensurable y x) {f : G} (hf : f ∈ F)
    (a : ℤ) (hmem : f ^ a ∈ Subgroup.zpowers y) : f ^ a = 1 := by
  by_contra hne
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have ha : a ≠ 0 := by
    rintro rfl
    exact hne (zpow_zero f)
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zpow_zero] at hk
    exact hne hk.symm
  exact havoid f hf ⟨k, a, 1, hk0, ha, by rw [one_mul, inv_one, mul_one, hk]⟩

/-! ## Gerasimova--Osin's Lemma 4.2 -/

/-- **An infinite cyclic hyperbolically embedded subgroup over a base containing
a prescribed finite set, conjugated off itself by every element of the set.**

The conjugation clause is stated per element: `f ⟨y⟩ f⁻¹ ∩ ⟨y⟩ = 1` for every
`f ∈ F`. -/
theorem exists_cyclic_hypEmbedded_avoiding (G : Type) [Group G]
    [IsAcylindricallyHyperbolic G]
    (hrad : ∀ N : Subgroup G, N.Normal → Finite N → N = ⊥) (F : Finset G)
    (hF : (1 : G) ∉ F) :
    ∃ (y : G) (X : Set G), ¬ IsOfFinOrder y ∧ (F : Set G) ⊆ X ∧
      IsHypEmbeddedOf G X (Subgroup.zpowers y) ∧
      ∀ f ∈ F, ∀ h ∈ Subgroup.zpowers y,
        f * h * f⁻¹ ∈ Subgroup.zpowers y → h = 1 := by
  obtain ⟨A⟩ := nonempty_hullGeneratingSet G
  obtain ⟨y, hlox, _hcyc, havoid, hemb₀⟩ :=
    exists_loxodromic_cyclic_avoiding A hrad F
  have hinf : ¬ IsOfFinOrder y := not_isOfFinOrder_of_isLoxodromic hlox
  have hinj : Function.Injective (fun n : ℤ => y ^ n) :=
    injective_zpow_iff_not_isOfFinOrder.mpr hinf
  -- the base enlarged by `F` and the inverses of its elements
  let D₀ : RelGenSet G Unit :=
    HullSC.coneOffFamily A.alphabet (fun _ : Unit => Subgroup.zpowers y)
  let D₁ : RelGenSet G Unit :=
    { base := A.alphabet.carrier ∪ ((F : Set G) ∪ {x : G | x⁻¹ ∈ F})
      fam := fun _ => Subgroup.zpowers y
      symmetricGenerating := by
        refine ⟨?_, ?_⟩
        · rintro x (hx | hx)
          · rcases hx with hx | hx | hx
            · exact Or.inl (Or.inl (A.alphabet.symmetricGenerating.inv_mem x hx))
            · exact Or.inl (Or.inr (Or.inr (by simpa using hx)))
            · exact Or.inl (Or.inr (Or.inl (by simpa using hx)))
          · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hx
            exact Or.inr (Set.mem_iUnion.mpr ⟨lam, (Subgroup.zpowers y).inv_mem hlam⟩)
        · refine eq_top_iff.mpr ?_
          rw [← A.alphabet.symmetricGenerating.closure_eq]
          exact Subgroup.closure_mono fun x hx => Or.inl (Or.inl hx) }
  have hfin : ((D₀.base \ D₁.base) ∪ (D₁.base \ D₀.base)).Finite := by
    refine (F.finite_toSet.union
      (F.finite_toSet.preimage inv_injective.injOn)).subset ?_
    rintro x (⟨hx0, hx1⟩ | ⟨hx1, hx0⟩)
    · exact absurd (Or.inl hx0) hx1
    · rcases hx1 with hx | hx
      · exact absurd hx hx0
      · exact hx
  have hemb₁ : D₁.IsHyperbolicallyEmbedded :=
    (RelGenSet.dgoCorollary427 G Unit D₀ D₁ rfl hfin).mp hemb₀
  refine ⟨y, D₁.base, hinf, fun x hx => Or.inr (Or.inl hx), ⟨D₁, rfl, rfl, hemb₁⟩, ?_⟩
  intro f hf h hh hconj
  by_contra hne
  -- `f` is not in `⟨y⟩`
  have hfnot : f⁻¹ ∉ D₀.fam () := by
    intro hfm
    have hfm' : f ^ (1 : ℤ) ∈ Subgroup.zpowers y := by
      rw [zpow_one]
      simpa using (Subgroup.zpowers y).inv_mem hfm
    have := pow_mem_zpowers_eq_one havoid hf 1 hfm'
    rw [zpow_one] at this
    exact hF (this ▸ hf)
  have hfinite := finite_conj_inter_of_notMem D₀ hemb₀ hfnot
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hm : m ≠ 0 := by
    rintro rfl
    exact hne (zpow_zero y)
  refine Set.not_infinite.mpr hfinite ?_
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℤ => (y ^ m) ^ k) ?_ ?_
  · intro a b hab
    have hab' : y ^ (m * a) = y ^ (m * b) := by
      simpa only [← zpow_mul] using hab
    exact mul_left_cancel₀ hm (hinj hab')
  · intro k
    refine ⟨Subgroup.zpow_mem _ (Subgroup.zpow_mem_zpowers y m) _, ?_⟩
    show f⁻¹⁻¹ * (y ^ m) ^ k * f⁻¹ ∈ Subgroup.zpowers y
    rw [inv_inv, ← conj_zpow]
    exact Subgroup.zpow_mem _ hconj k

end CyclicEmbeddedChoice
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.CyclicEmbeddedChoice.nonempty_hullGeneratingSet
#audit_axioms GroupApproximation.GGT.CyclicEmbeddedChoice.suitable_top_of_trivialFiniteRadical
#audit_axioms GroupApproximation.GGT.CyclicEmbeddedChoice.exists_loxodromic_cyclic_avoiding
#audit_axioms GroupApproximation.GGT.CyclicEmbeddedChoice.pow_mem_zpowers_eq_one
#audit_axioms GroupApproximation.GGT.CyclicEmbeddedChoice.exists_cyclic_hypEmbedded_avoiding
