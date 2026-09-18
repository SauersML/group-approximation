import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngRank3SecDiv
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngRank3SecGen
import GroupApproximation.Meta.AxiomGuard

/-!
# A smaller coset residual for `K₂(3, ℤ[1/m])` (lane `bh-met-93x`, endpoint)

Target: `czK2FngGtOneRank3_CosetStatement` (lane `bh-met-93s`).  For each `m > 0` and prime
`p`, it asks for a finite `s ⊆ K₂(3, ℤ[1/(mp)])` and a section
`σ : E_3(ℤ[1/(mp)]) ⧸ φ(E_3(ℤ[1/m])) → St_3(ℤ[1/(mp)])` with `σ(Γ) ∈ Q`.  All **twelve**
generators `x_ij(1)`, `x_ij(u)`, `u = 1/(mp)`, must pass the check.  **Not closed outright.**

**The residual `czK2FngRank3Sec_ResidualStatement`.**  It is the same data, with two changes.
* It is required only for primes `p` with `p ∤ m`.
* Only **four** checks are required: `x₀₁(1)`, `x₁₂(1)`, `x₂₀(1)` and `x₀₁(u)`
  (`czK2FngRank3Sec_CyclicSectionProp`).

**Proved outright.**
* `czK2FngRank3Sec_coset_of_dvd` (module `...SecDiv`): the case `p ∣ m`, with `s = ∅` and
  `σ = 1`.  Here `ℤ[1/m] → ℤ[1/(mp)]` is surjective, so `Q` is everything.
* `czK2FngRank3Sec_sectionProp_of_cyclic`: the four checks give all twelve.  The checks form a
  subgroup (`czK2FngGtOneRank3_good`), and that subgroup contains all twelve generators by
  `czK2FngRank3Sec_all_of_cyclic` (module `...SecGen`).
* `czK2FngRank3Sec_coset_of_residual`: the residual gives `czK2FngGtOneRank3_CosetStatement`.
* `czK2FngRank3Sec_rankThree_of_residual`: the residual gives `czK2FngGtOne_RankThreeStatement`.
* `czK2FngRank3Sec_residual_of_coset`: the converse.

**Strength (LOUD).**  The residual is formally implied by `CosetStatement`
(`residual_of_coset`), because it asks for fewer checks, and for fewer primes.  By
`coset_of_residual` it is therefore **logically EQUIVALENT** to `CosetStatement`, and hence to
the target `czK2FngGtOne_RankThreeStatement`.  It is **strictly smaller in proof content**:
* the case `p ∣ m` is gone (proved here);
* eight of the twelve generator checks are gone (derived here);
* only one check still involves the new coefficient `1/(mp)`.

It is **not** "`E_3(ℤ[1/m])` is finitely presented", and it contains no hypothesis about any
presentation.

**Remaining gap.**  One must construct, for `p ∤ m`, a section `σ` on the type-0 vertices
`E_3(S)/Γ` of the Bruhat–Tits building of `SL_3(ℚ_p)`, together with a finite
`s ⊆ K₂(3, S)`, such that `x₀₁(1)`, `x₁₂(1)`, `x₂₀(1)` and `x₀₁(1/(mp))` pass the check.
This is the actual finite-presentation content: simple connectivity of the building, or
equivalently the relations of the triangle of groups.  No explicit section is constructed in
this lane.

**Truth.**  The residual is true because the target is true (`SL_3(ℤ[1/n])` is finitely
presented).  This is a truth check only and is not a hypothesis.  Any lifting section
`σ(y) ∈ projection⁻¹(y)` then works (`czK2FngGtOneRank3_check_of_le`).  The script
`$SP/bh-met-93x/truth_check.py` checks the following:
* the eight commutator derivations;
* that the four elements generate the same subgroup as the twelve in `SL_3(F_q)`;
* the explicit preimage `a · k^n · (1/m)^{2n}` used for surjectivity;
* that the residual is not vacuous for `p ∤ m` (`1/p ∉ ℤ[1/m]`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **Four checks.**  There is a section `σ` on `E_3(S)/φ(E_3(R))` with `σ(Γ) ∈ Q` such that
`x₀₁(1)`, `x₁₂(1)`, `x₂₀(1)` and `x₀₁(u)` pass the check. -/
def czK2FngRank3Sec_CyclicSectionProp {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (s : Set (SteinbergGroup (Fin 3) S)) (u : S) : Prop :=
  ∃ σ : (elementaryGroup (Fin 3) S ⧸ (elementaryGroupMap (ι := Fin 3) φ).range) →
      SteinbergGroup (Fin 3) S,
    σ (QuotientGroup.mk 1) ∈ czK2FngGtOneRank3_Q φ s ∧
    czK2FngGtOneRank3_Check (czK2FngGtOneRank3_Q φ s) σ (x (0 : Fin 3) 1 (by decide) 1) ∧
    czK2FngGtOneRank3_Check (czK2FngGtOneRank3_Q φ s) σ (x (1 : Fin 3) 2 (by decide) 1) ∧
    czK2FngGtOneRank3_Check (czK2FngGtOneRank3_Q φ s) σ (x (2 : Fin 3) 0 (by decide) 1) ∧
    czK2FngGtOneRank3_Check (czK2FngGtOneRank3_Q φ s) σ (x (0 : Fin 3) 1 (by decide) u)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_CyclicSectionProp

/-- **Four checks give all twelve.** -/
theorem czK2FngRank3Sec_sectionProp_of_cyclic {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (s : Set (SteinbergGroup (Fin 3) S)) (u : S)
    (h : czK2FngRank3Sec_CyclicSectionProp φ s u) : czK2FngGtOneRank3_SectionProp φ s u := by
  obtain ⟨σ, h0, c01, c12, c20, cu⟩ := h
  have hall := czK2FngRank3Sec_all_of_cyclic
    (czK2FngGtOneRank3_good (czK2FngGtOneRank3_Q φ s) σ) u
    (czK2FngGtOneRank3_mem_good.mpr c01) (czK2FngGtOneRank3_mem_good.mpr c12)
    (czK2FngGtOneRank3_mem_good.mpr c20) (czK2FngGtOneRank3_mem_good.mpr cu)
  exact ⟨σ, h0, fun i j hij ↦ czK2FngGtOneRank3_mem_good.mp (hall i j hij).1,
    fun i j hij ↦ czK2FngGtOneRank3_mem_good.mp (hall i j hij).2⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_sectionProp_of_cyclic

/-- Conversely, all twelve checks give the four. -/
theorem czK2FngRank3Sec_cyclic_of_sectionProp {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (s : Set (SteinbergGroup (Fin 3) S)) (u : S)
    (h : czK2FngGtOneRank3_SectionProp φ s u) : czK2FngRank3Sec_CyclicSectionProp φ s u := by
  obtain ⟨σ, h0, h1, hu⟩ := h
  exact ⟨σ, h0, h1 0 1 (by decide), h1 1 2 (by decide), h1 2 0 (by decide), hu 0 1 (by decide)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_cyclic_of_sectionProp

/-- **The residual (lane `bh-met-93x`).**  For `m > 0` and `p` prime with `p ∤ m`, there are a
finite `s ⊆ K₂(3, ℤ[1/(mp)])` and a section on `E_3(ℤ[1/(mp)])/E_3(ℤ[1/m])` with `σ(Γ) ∈ Q`
such that `x₀₁(1)`, `x₁₂(1)`, `x₂₀(1)` and `x₀₁(1/(mp))` pass the check.  It is logically
equivalent to `czK2FngGtOneRank3_CosetStatement` and strictly smaller in proof content (see
the module docstring). -/
def czK2FngRank3Sec_ResidualStatement : Prop :=
  ∀ m p : ℕ, 0 < m → p.Prime → ¬ p ∣ m →
    ∃ s : Set (SteinbergGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))), s.Finite ∧
      s ⊆ K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) ∧
      czK2FngRank3Sec_CyclicSectionProp (czK2FngGtOneRank3_locMap m p) s
        (IsLocalization.Away.invSelf ((m * p : ℕ) : ℤ) :
          Localization.Away ((m * p : ℕ) : ℤ))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_ResidualStatement

/-- **The residual gives the coset statement of lane `bh-met-93s`.** -/
theorem czK2FngRank3Sec_coset_of_residual (h : czK2FngRank3Sec_ResidualStatement) :
    czK2FngGtOneRank3_CosetStatement := by
  intro m p hm hp
  by_cases hpm : p ∣ m
  · exact czK2FngRank3Sec_coset_of_dvd m p hpm
  · obtain ⟨s, hsfin, hsK, hσ⟩ := h m p hm hp hpm
    exact ⟨s, hsfin, hsK, czK2FngRank3Sec_sectionProp_of_cyclic _ s _ hσ⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_coset_of_residual

/-- **The residual gives the target** `czK2FngGtOne_RankThreeStatement`: `K₂(3, ℤ[1/m])` is
finitely normally generated for every `m > 1`. -/
theorem czK2FngRank3Sec_rankThree_of_residual (h : czK2FngRank3Sec_ResidualStatement) :
    czK2FngGtOne_RankThreeStatement :=
  czK2FngGtOneRank3_rankThree_of_coset (czK2FngRank3Sec_coset_of_residual h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_rankThree_of_residual

/-- **Converse (LOUD: the residual is formally implied by the coset statement, hence
equivalent to it).** -/
theorem czK2FngRank3Sec_residual_of_coset (h : czK2FngGtOneRank3_CosetStatement) :
    czK2FngRank3Sec_ResidualStatement := by
  intro m p hm hp _
  obtain ⟨s, hsfin, hsK, hσ⟩ := h m p hm hp
  exact ⟨s, hsfin, hsK, czK2FngRank3Sec_cyclic_of_sectionProp _ s _ hσ⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngRank3Sec_residual_of_coset

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
