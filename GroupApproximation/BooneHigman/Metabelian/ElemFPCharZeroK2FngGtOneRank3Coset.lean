import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneRank3Core
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneRank3Gen
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneRank3Step
import GroupApproximation.Meta.AxiomGuard

/-!
# The coset residual for `czK2FngGtOne_RankThreeStatement` (lane `bh-met-93s`, endpoint)

Target: `czK2FngGtOne_RankThreeStatement`, that `K₂(3, ℤ[1/m])` is finitely normally generated
for every `m > 1`.  **Not closed outright.**

**The residual `czK2FngGtOneRank3_CosetStatement`.**  Let `m > 0` and let `p` be prime.  Put
`S = ℤ[1/(mp)]`, let `φ : ℤ[1/m] → S` be the localisation map, and let `Γ = φ(E_3(ℤ[1/m]))`,
a subgroup of `E_3(S)`.  Let `X = E_3(S)/Γ`, which is the set of type-0 vertices of the
Bruhat–Tits building of `SL_3(ℚ_p)`.  The statement asks for a finite `s ⊆ K₂(3, S)` and a map
`σ : X → St_3(S)` such that
* `σ(Γ) ∈ Q`, and
* the twelve generators `x_ij(1)` and `x_ij(1/(mp))` pass the check: `σ(g·y)⁻¹ · g · σ(y) ∈ Q`
  for every vertex `y`.

Here `Q = Φ(St_3(ℤ[1/m])) ⊔ ⟪Φ(K₂(3, ℤ[1/m])) ∪ s⟫`.

**Proved outright.**
* `czK2FngGtOneRank3_step_of_coset`: the residual gives the one-prime step
  `czK2FngGtOneRank3_StepStatement`.  The checks close under products and inverses
  (`czK2FngGtOneRank3_good`), and the twelve generators generate `St_3(S)`
  (`czK2FngGtOneRank3_eq_top`).  So every element passes the check.  `K₂` fixes `X`, so
  `K₂(3, S) ⊆ Q`, and `Q ∩ K₂(3, S) ⊆ N` because `φ` is injective.
* `czK2FngGtOneRank3_rankThree_of_coset`: **the residual gives the target.**  The route is the
  prime induction `czK2FngGtOneRank3_rankThree_of_step`, with base case
  `czK2FngTorus_k2ThreeOne_fng` (`SL_3(ℤ)`, `P13`).
* `czK2FngGtOneRank3_coset_of_step`: the converse.  Given the step, any section
  `σ(y) ∈ projection⁻¹(y.out)` passes every check.

**Strength (LOUD).  The residual is logically EQUIVALENT to the target.**  Both directions are
proved: `rankThree_of_coset`, and `coset_of_step ∘ step_of_rankThree`.  It is **not** logically
weaker.  It is **strictly smaller in proof content**, in the same sense as lanes `92h` and `92k`:
* All group-theoretic bookkeeping is done here: the prime induction, the transport of normal
  generation, Reidemeister–Schreier closure, and the passage `Q ∩ K₂ ⊆ N`.
* What remains is local combinatorics on the vertex set `X`.  One must choose `σ` and verify
  twelve generator-wise conditions.
* The residual never mentions a presentation of any matrix group, and it contains no
  quantifier over the elements of `K₂`.

It is **not** the equivalent restatement "`E_3(ℤ[1/m])` is finitely presented".

**Truth.**  The residual is true because the target is true: `SL_3(ℤ[1/m])` is finitely
presented (Behr; Borel–Serre).  This is a truth check only and is not a hypothesis.  The script
`$SP/bh-met-93s/truth_check.py` checks the matrix identities used: root additivity, the
commutator `[x_ik(a), x_kj(b)] = x_ij(ab)`, the trivial action of `K₂` on cosets, and the
Euclidean reduction over `ℤ[1/m]`.  It also checks the shape of the coset data on a small
model.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **A section passing the check, for a coefficient map `φ`.**  `u` is the second generator
coefficient.  `σ` is defined on `E_3(S)/φ(E_3(R))`, and `σ(Γ) ∈ Q`.  All `x_ij(1)` and all
`x_ij(u)` pass the check. -/
def czK2FngGtOneRank3_SectionProp {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (s : Set (SteinbergGroup (Fin 3) S)) (u : S) : Prop :=
  ∃ σ : (elementaryGroup (Fin 3) S ⧸ (elementaryGroupMap (ι := Fin 3) φ).range) →
      SteinbergGroup (Fin 3) S,
    σ (QuotientGroup.mk 1) ∈ czK2FngGtOneRank3_Q φ s ∧
    (∀ (i j : Fin 3) (h : i ≠ j),
      czK2FngGtOneRank3_Check (czK2FngGtOneRank3_Q φ s) σ (x i j h 1)) ∧
    (∀ (i j : Fin 3) (h : i ≠ j),
      czK2FngGtOneRank3_Check (czK2FngGtOneRank3_Q φ s) σ (x i j h u))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_SectionProp

/-- **The residual (lane `bh-met-93s`).**  For `m > 0` and `p` prime, there is a finite
`s ⊆ K₂(3, ℤ[1/(mp)])` and a section on `E_3(ℤ[1/(mp)])/E_3(ℤ[1/m])` such that the generators
`x_ij(1)` and `x_ij(1/(mp))` pass the check.  It is logically equivalent to
`czK2FngGtOne_RankThreeStatement` and smaller in proof content (see the module docstring). -/
def czK2FngGtOneRank3_CosetStatement : Prop :=
  ∀ m p : ℕ, 0 < m → p.Prime →
    ∃ s : Set (SteinbergGroup (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ))), s.Finite ∧
      s ⊆ K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) ∧
      czK2FngGtOneRank3_SectionProp (czK2FngGtOneRank3_locMap m p) s
        (IsLocalization.Away.invSelf ((m * p : ℕ) : ℤ) :
          Localization.Away ((m * p : ℕ) : ℤ))

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_CosetStatement

/-- **The residual gives the one-prime step.** -/
theorem czK2FngGtOneRank3_step_of_coset (h : czK2FngGtOneRank3_CosetStatement) :
    czK2FngGtOneRank3_StepStatement := by
  intro m p hm hp
  obtain ⟨s, hsfin, hsK, σ, h0, h1, hu⟩ := h m p hm hp
  refine ⟨s, hsfin, hsK, ?_⟩
  intro k hk
  have hmp : m * p ≠ 0 := Nat.mul_ne_zero hm.ne' hp.ne_zero
  have htop : czK2FngGtOneRank3_good (czK2FngGtOneRank3_Q (czK2FngGtOneRank3_locMap m p) s) σ =
      ⊤ :=
    czK2FngGtOneRank3_eq_top (m * p) 3 (by omega) _
      (fun i j hij ↦ czK2FngGtOneRank3_mem_good.mpr (h1 i j hij))
      (fun i j hij ↦ czK2FngGtOneRank3_mem_good.mpr (hu i j hij))
  have hkQ := czK2FngGtOneRank3_mem_Q_of_top _ σ (QuotientGroup.mk 1) h0 htop hk
  exact czK2FngGtOneRank3_mem_N_of_mem_Q (czK2FngGtOneRank3_locMap m p)
    (czK2FngGtOneRank3_locMap_injective m p hmp) s hsK hkQ hk

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_step_of_coset

/-- **The residual gives the target** `czK2FngGtOne_RankThreeStatement`. -/
theorem czK2FngGtOneRank3_rankThree_of_coset (h : czK2FngGtOneRank3_CosetStatement) :
    czK2FngGtOne_RankThreeStatement :=
  czK2FngGtOneRank3_rankThree_of_step (czK2FngGtOneRank3_step_of_coset h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_rankThree_of_coset

section Converse

variable {R S : Type*} [CommRing R] [CommRing S]

/-- **Converse direction.**  If `K₂(3, S) ≤ N`, then any section that lifts coset
representatives passes the check for every `g`. -/
theorem czK2FngGtOneRank3_check_of_le (φ : R →+* S) (s : Set (SteinbergGroup (Fin 3) S))
    (hle : K2 (Fin 3) S ≤ czK2FngGtOneRank3_N φ s)
    (σ : (elementaryGroup (Fin 3) S ⧸ (elementaryGroupMap (ι := Fin 3) φ).range) →
      SteinbergGroup (Fin 3) S)
    (hσ : ∀ y, projection (σ y) = y.out) (g : SteinbergGroup (Fin 3) S) :
    czK2FngGtOneRank3_Check (czK2FngGtOneRank3_Q φ s) σ g := by
  intro y
  apply czK2FngGtOneRank3_mem_Q_of_projection φ s hle
  rw [map_mul, map_mul, map_inv, hσ, hσ]
  have h1 : (QuotientGroup.mk (projection g * y.out) :
      elementaryGroup (Fin 3) S ⧸ (elementaryGroupMap (ι := Fin 3) φ).range) =
      projection g • (QuotientGroup.mk y.out :
        elementaryGroup (Fin 3) S ⧸ (elementaryGroupMap (ι := Fin 3) φ).range) :=
    rfl
  rw [QuotientGroup.out_eq'] at h1
  rw [mul_assoc]
  exact QuotientGroup.eq.mp (by rw [QuotientGroup.out_eq', h1])

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_check_of_le

/-- **Converse direction.**  If `K₂(3, S) ≤ N`, then a section as in `SectionProp` exists for
every coefficient `u`. -/
theorem czK2FngGtOneRank3_exists_section (φ : R →+* S) (s : Set (SteinbergGroup (Fin 3) S))
    (hle : K2 (Fin 3) S ≤ czK2FngGtOneRank3_N φ s) (u : S) :
    czK2FngGtOneRank3_SectionProp φ s u := by
  obtain ⟨σ, hσ⟩ : ∃ σ : (elementaryGroup (Fin 3) S ⧸
      (elementaryGroupMap (ι := Fin 3) φ).range) → SteinbergGroup (Fin 3) S,
      ∀ y, projection (σ y) = y.out :=
    ⟨fun y ↦ (projection_surjective y.out).choose,
      fun y ↦ (projection_surjective y.out).choose_spec⟩
  refine ⟨σ, ?_, fun i j hij ↦ czK2FngGtOneRank3_check_of_le φ s hle σ hσ (x i j hij 1),
    fun i j hij ↦ czK2FngGtOneRank3_check_of_le φ s hle σ hσ (x i j hij u)⟩
  apply czK2FngGtOneRank3_mem_Q_of_projection φ s hle
  rw [hσ]
  have h2 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (QuotientGroup.mk 1 :
    elementaryGroup (Fin 3) S ⧸ (elementaryGroupMap (ι := Fin 3) φ).range))
  rw [mul_one] at h2
  exact inv_mem_iff.mp h2

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_exists_section

end Converse

/-- **Converse (LOUD: the residual is equivalent to the step).** -/
theorem czK2FngGtOneRank3_coset_of_step (h : czK2FngGtOneRank3_StepStatement) :
    czK2FngGtOneRank3_CosetStatement := by
  intro m p hm hp
  obtain ⟨s, hsfin, hsK, hle⟩ := h m p hm hp
  have hle' : K2 (Fin 3) (Localization.Away ((m * p : ℕ) : ℤ)) ≤
      czK2FngGtOneRank3_N (czK2FngGtOneRank3_locMap m p) s := hle
  exact ⟨s, hsfin, hsK, czK2FngGtOneRank3_exists_section _ s hle' _⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_coset_of_step

/-- **Converse (LOUD: the residual is equivalent to the target).** -/
theorem czK2FngGtOneRank3_coset_of_rankThree (h : czK2FngGtOne_RankThreeStatement) :
    czK2FngGtOneRank3_CosetStatement :=
  czK2FngGtOneRank3_coset_of_step (czK2FngGtOneRank3_step_of_rankThree h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_coset_of_rankThree

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
