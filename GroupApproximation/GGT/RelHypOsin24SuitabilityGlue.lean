import GroupApproximation.GGT.RelHypOsin24Glue

/-!
# Suitability glue for Osin's Theorem 2.4

Osin's suitable-subgroup condition already implies the finite-normalizer clause
in Hull's suitable-subgroup condition, even when the ambient group has torsion.
If a finite subgroup `F` is normalized by a suitable subgroup `H`, conjugation
by either Osin witness permutes `F`.  A positive power of that permutation is
the identity, so every element of `F` belongs to the Osin elementary closure of
both witnesses.  Their elementary closures meet trivially, so `F = 1`.

This is the group-theoretic part needed to generalize the torsion-free Hull
packaging in the relatively hyperbolic specialization.  No torsion-free
hypothesis occurs below.  The final section also packages the exact mapped
witness data which remains to be obtained from preservation of the elementary
closures in the quotient.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section FiniteNormalizer

variable {G : Type u} [Group G]

/-- Conjugation by an element of `H`, restricted to a finite subgroup
normalized by `H`.  The inverse is conjugation by the inverse element, which
also belongs to `H`. -/
def finiteNormalizerConjugation {H F : Subgroup G} (s : G) (hs : s ∈ H)
    (hnorm : ∀ y ∈ H, ∀ x ∈ F, y * x * y⁻¹ ∈ F) : F ≃* F where
  toFun x := ⟨s * x * s⁻¹, hnorm s hs x x.property⟩
  invFun x :=
    ⟨s⁻¹ * x * (s⁻¹)⁻¹, hnorm s⁻¹ (H.inv_mem hs) x x.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    simp
  right_inv := by
    intro x
    apply Subtype.ext
    simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    change s * (↑x * ↑y) * s⁻¹ =
      (s * ↑x * s⁻¹) * (s * ↑y * s⁻¹)
    group

/-- The `n`-th power of restricted conjugation is conjugation by `s^n`.
Only the equality after coercion to the ambient group is needed. -/
theorem coe_pow_finiteNormalizerConjugation {H F : Subgroup G}
    (s : G) (hs : s ∈ H)
    (hnorm : ∀ y ∈ H, ∀ x ∈ F, y * x * y⁻¹ ∈ F)
    (n : ℕ) (x : F) :
    ↑(((finiteNormalizerConjugation s hs hnorm) ^ n) x) =
      s ^ n * x * (s ^ n)⁻¹ := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      change ↑(((finiteNormalizerConjugation s hs hnorm) ^ n)
          (finiteNormalizerConjugation s hs hnorm x)) =
        s ^ (n + 1) * x * (s ^ (n + 1))⁻¹
      rw [ih]
      change s ^ n * (s * x * s⁻¹) * (s ^ n)⁻¹ =
        s ^ (n + 1) * x * (s ^ (n + 1))⁻¹
      rw [pow_succ]
      group

/-- Every element of a finite subgroup normalized by `H` belongs to the Osin
elementary closure of each element of `H`.  Conjugation on the finite subgroup
has finite order, and its order supplies the positive exponent in Osin's
definition. -/
theorem mem_osinElementaryClosure_of_mem_finite_normalized
    {H F : Subgroup G} (hF : Finite F)
    (hnorm : ∀ y ∈ H, ∀ x ∈ F, y * x * y⁻¹ ∈ F)
    {s : G} (hs : s ∈ H) {x : G} (hx : x ∈ F) :
    x ∈ osinElementaryClosure s := by
  letI : Finite F := hF
  let c : F ≃* F := finiteNormalizerConjugation s hs hnorm
  obtain ⟨n, hn, hpow⟩ :=
    isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite c)
  have happ : (c ^ n) (⟨x, hx⟩ : F) = ⟨x, hx⟩ := by
    have heval := congrArg (fun e : F ≃* F => e (⟨x, hx⟩ : F)) hpow
    simpa using heval
  have hconj : s ^ n * x * (s ^ n)⁻¹ = x := by
    have hcoe := congrArg Subtype.val happ
    change ↑(((finiteNormalizerConjugation s hs hnorm) ^ n)
      (⟨x, hx⟩ : F)) = x at hcoe
    rw [coe_pow_finiteNormalizerConjugation s hs hnorm n ⟨x, hx⟩] at hcoe
    exact hcoe
  refine ⟨n, hn, Or.inl ?_⟩
  calc
    x⁻¹ * s ^ n * x = x⁻¹ * (s ^ n * x * (s ^ n)⁻¹) * s ^ n := by
      group
    _ = s ^ n := by rw [hconj]; simp

/-- Osin suitability implies Hull's condition that the subgroup normalizes no
nontrivial finite subgroup.  This replaces the torsion-free shortcut used by
the generic Hull filling package. -/
theorem IsSuitableSubgroup.normalizesNoNontrivialFinite
    {i : Type v} {Hfam : i → Subgroup G} {H : Subgroup G}
    (hH : IsSuitableSubgroup Hfam H) :
    HullSuitable.NormalizesNoNontrivialFinite H := by
  obtain ⟨f₁, hf₁, f₂, hf₂, _hhyper₁, _hhyper₂,
    _hord₁, _hord₂, _hnc, hinter⟩ := hH
  intro F hF hnorm
  apply (Subgroup.eq_bot_iff_forall F).mpr
  intro x hx
  have hx₁ : x ∈ osinElementaryClosure f₁ :=
    mem_osinElementaryClosure_of_mem_finite_normalized hF hnorm hf₁ hx
  have hx₂ : x ∈ osinElementaryClosure f₂ :=
    mem_osinElementaryClosure_of_mem_finite_normalized hF hnorm hf₂ hx
  exact hinter x hx₁ hx₂

end FiniteNormalizer

/-! ## Exact quotient suitability constructor -/

/-- The mapped pair data needed after the quotient is constructed gives
Osin's suitability conclusion directly.  This theorem isolates the geometric
preservation work: hyperbolicity relative to the mapped original peripherals,
infinite order, non-commensurability, and the intersection of the two mapped
elementary closures. -/
theorem isOsin24SuitabilityConclusion_of_mapWitnesses
    {G : Type u} [Group G] {Q : Type v} [Group Q] {i : Type*}
    {Hfam : i → Subgroup G} {H : Subgroup G} (eta : G →* Q)
    {f₁ f₂ : G} (hf₁ : f₁ ∈ H) (hf₂ : f₂ ∈ H)
    (hhyper₁ : IsHyperbolicElement (fun l ⇒ (Hfam l).map eta) (eta f₁))
    (hhyper₂ : IsHyperbolicElement (fun l ⇒ (Hfam l).map eta) (eta f₂))
    (hord₁ : ∀ n : ℕ, 0 < n → eta f₁ ^ n ≠ 1)
    (hord₂ : ∀ n : ℕ, 0 < n → eta f₂ ^ n ≠ 1)
    (hnc : ¬ OsinCommensurable (eta f₁) (eta f₂))
    (hinter : ∀ q, q ∈ osinElementaryClosure (eta f₁) →
      q ∈ osinElementaryClosure (eta f₂) → q = 1) :
    IsOsin24SuitabilityConclusion Hfam H eta := by
  refine ⟨eta f₁, ?_, eta f₂, ?_, hhyper₁, hhyper₂,
    hord₁, hord₂, hnc, hinter⟩
  · exact Subgroup.mem_map_of_mem eta hf₁
  · exact Subgroup.mem_map_of_mem eta hf₂

end RelHyp
end GGT
end GroupApproximation
