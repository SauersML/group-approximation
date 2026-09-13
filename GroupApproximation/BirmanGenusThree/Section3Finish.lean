import GroupApproximation.BirmanGenusThree.Section3CaseB
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Chen–Salter, §3.4: both cases give a section of a central extension

Chen–Salter (arXiv:1804.11235v1, §3.4) finish with rational cohomology: `(i × s)^*[Δ] = 0` because
the section `σ : H̄ → PB₂(Σ_2)` lands in the configuration space, while Künneth gives
`χ(Σ_2)·[H̄] ≠ 0` in Case A and `[H̄] ≠ 0` in Case B. This file replaces that computation by two
constructions of a section over `H̄` of a central extension of `π₁(Σ_2)`. A transfer argument then
shows that such a section cannot exist (b3-surfacegroup, `not_exists_section_of_surjective`).

Write `P = PB₂(Σ_2)` with the two point-forgetting maps `p₁, p₂ : P → π₁(Σ_2)`, so that
`p₁ ∘ σ = id` and `p₂ ∘ σ = s`.
- **Case B** (`s = 1`). `σ` lands in `ker p₂ = π₁(Σ_2 ∖ pt)`, a free group. A free group lifts
  along the surjection `π₁(UT Σ_2) → π₁(Σ_2)`, so `σ` gives a section of the unit tangent bundle
  extension over `H̄` (`section_of_caseB`).
- **Case A** (`s = id`). Let `E_Δ → π₁(Σ_2) × π₁(Σ_2)` be the central extension with class `[Δ]`.
  It splits over `P` because `[Δ]` restricts to zero there (Lemma 3.9), and its pullback along the
  diagonal has class `χ(Σ_2)·[Σ_2] ≠ 0`. Since `(p₁, p₂) ∘ σ` is the diagonal, `σ` gives a section of
  that pullback over `H̄` (`section_of_caseA`).

`section3_finish` combines Corollary 3.4 and Lemmas 3.5–3.6 with these two constructions.
-/

namespace GroupApproximation.BirmanGenusThree.Section3

/-- A homomorphism from a free group lifts along any surjective homomorphism. -/
theorem exists_lift_of_isFreeGroup {K E Q : Type*} [Group K] [IsFreeGroup K] [Group E] [Group Q]
    (proj : E →* Q) (hproj : Function.Surjective proj) (ψ : K →* Q) :
    ∃ τ : K →* E, proj.comp τ = ψ := by
  refine ⟨IsFreeGroup.lift fun a => Function.surjInv hproj (ψ (IsFreeGroup.of a)), ?_⟩
  refine IsFreeGroup.ext_hom fun a => ?_
  rw [MonoidHom.comp_apply, IsFreeGroup.lift_of]
  exact Function.surjInv_eq hproj _

/-- **Case B.** If `σ` lifts the inclusion of `H` through `p₁` and is killed by `p₂`, and `ker p₂` is
free, then the surjection `proj` has a section over `H`. -/
theorem section_of_caseB {Q E P : Type*} [Group Q] [Group E] [Group P] (proj : E →* Q)
    (hproj : Function.Surjective proj) (p₁ p₂ : P →* Q) [IsFreeGroup p₂.ker] {H : Subgroup Q}
    (σ : H →* P) (hσ₁ : ∀ h : H, p₁ (σ h) = h) (hσ₂ : ∀ h : H, p₂ (σ h) = 1) :
    ∃ τ : H →* E, ∀ h : H, proj (τ h) = h := by
  obtain ⟨τ₀, hτ₀⟩ := exists_lift_of_isFreeGroup proj hproj (p₁.comp p₂.ker.subtype)
  let σ' : H →* p₂.ker := σ.codRestrict p₂.ker fun h => MonoidHom.mem_ker.2 (hσ₂ h)
  exact ⟨τ₀.comp σ', fun h => (DFunLike.congr_fun hτ₀ (σ' h)).trans (hσ₁ h)⟩

/-- The pullback of `πΔ : EΔ → Q × Q` along the diagonal `Q → Q × Q`. -/
def diagonalPullback {Q EΔ : Type*} [Group Q] [Group EΔ] (πΔ : EΔ →* Q × Q) : Subgroup EΔ :=
  ((MonoidHom.id Q).prod (MonoidHom.id Q)).range.comap πΔ

/-- The projection of the diagonal pullback to `Q`. -/
def diagonalProj {Q EΔ : Type*} [Group Q] [Group EΔ] (πΔ : EΔ →* Q × Q) :
    diagonalPullback πΔ →* Q :=
  (MonoidHom.fst Q Q).comp (πΔ.comp (diagonalPullback πΔ).subtype)

/-- **Case A.** If `(p₁, p₂) : P → Q × Q` lifts to `EΔ` and `σ` lifts the inclusion of `H` through
both `p₁` and `p₂`, then the diagonal pullback of `EΔ` has a section over `H`. -/
theorem section_of_caseA {Q EΔ P : Type*} [Group Q] [Group EΔ] [Group P] (πΔ : EΔ →* Q × Q)
    (p₁ p₂ : P →* Q) (δ : P →* EΔ) (hδ : ∀ x, πΔ (δ x) = (p₁ x, p₂ x)) {H : Subgroup Q}
    (σ : H →* P) (hσ₁ : ∀ h : H, p₁ (σ h) = h) (hσ₂ : ∀ h : H, p₂ (σ h) = h) :
    ∃ τ : H →* diagonalPullback πΔ, ∀ h : H, diagonalProj πΔ (τ h) = h := by
  have hmem : ∀ h : H, (δ.comp σ) h ∈ diagonalPullback πΔ := fun h =>
    Subgroup.mem_comap.2 <| MonoidHom.mem_range.2
      ⟨(h : Q), by rw [MonoidHom.prod_apply, MonoidHom.id_apply, MonoidHom.comp_apply, hδ, hσ₁, hσ₂]⟩
  refine ⟨(δ.comp σ).codRestrict _ hmem, fun h => ?_⟩
  change (πΔ (δ (σ h))).1 = h
  rw [hδ, hσ₁]

/-- **Chen–Salter, §3.4, without cohomology.** Given the inputs of Corollary 3.4 and Lemmas 3.5–3.6
for `s`, and a group `P` with maps `p₁, p₂` such that `p₁ ∘ σ = id` and `p₂ ∘ σ = s`, either `proj`
(Case B) or the diagonal pullback of `πΔ` (Case A) has a section over `H`. -/
theorem section3_finish {Q : Type*} [Group Q] [IsMulTorsionFree Q] {S : Set Q} {H : Subgroup Q}
    {s : H →* Q} (hG : PowConjRigid Q) (hC : CommonPowers Q) (hS : SimpleSystem S)
    (hSne : S.Nonempty) (hH : HasPowersIn H) (hs : PowerExponentForm S H s)
    {ι : Type*} (T : ι → MulAut Q) (hTH : ∀ i, ∀ x ∈ H, T i x ∈ H)
    (h38 : ∀ i (x : H), (⟨T i x, hTH i x x.2⟩ : H) * x⁻¹ ∈ simplePowers S H)
    (h37 : ∀ i (x : H), IsConj (s ⟨T i x, hTH i x x.2⟩) (T i (s x)))
    (h28 : ∀ y : Q, (∀ i, IsConj (T i y) y) → y = 1)
    {E P EΔ : Type*} [Group E] [Group P] [Group EΔ] (proj : E →* Q)
    (hproj : Function.Surjective proj) (p₁ p₂ : P →* Q) [IsFreeGroup p₂.ker] (πΔ : EΔ →* Q × Q)
    (δ : P →* EΔ) (hδ : ∀ x, πΔ (δ x) = (p₁ x, p₂ x)) (σ : H →* P)
    (hσ₁ : ∀ h : H, p₁ (σ h) = h) (hσ₂ : ∀ h : H, p₂ (σ h) = s h) :
    (∃ τ : H →* E, ∀ h : H, proj (τ h) = h) ∨
      ∃ τ : H →* diagonalPullback πΔ, ∀ h : H, diagonalProj πΔ (τ h) = h := by
  rcases corollary_3_4 hG hC hS hH hs with hA | hB
  · exact Or.inr <| section_of_caseA πΔ p₁ p₂ δ hδ σ hσ₁ fun h =>
      (hσ₂ h).trans (lemma_3_5 hC hS hSne hH hA h)
  · exact Or.inl <| section_of_caseB proj hproj p₁ p₂ σ hσ₁ fun h =>
      (hσ₂ h).trans (lemma_3_6 T hTH h38 h37 h28 hB h)

end GroupApproximation.BirmanGenusThree.Section3
