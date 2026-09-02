import GroupApproximation.GGT.RelHypOsin24Glue
import GroupApproximation.GGT.DGOProposition433Finite
import GroupApproximation.GGT.HullSCRelatorWord
import GroupApproximation.GGT.HullSCUnionGeometryVirtuallyCyclic

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
    change s⁻¹ * (s * ↑x * s⁻¹) * (s⁻¹)⁻¹ = ↑x
    group
  right_inv := by
    intro x
    apply Subtype.ext
    change s * (s⁻¹ * ↑x * (s⁻¹)⁻¹) * s⁻¹ = ↑x
    group
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

/-! ## Quotient form of Osin Theorem 2.1 -/

/-- The precise quotient consequence of Osin Theorem 2.1 used for suitability:
an infinite-order member of a hyperbolically embedded peripheral has its Osin
elementary closure inside that peripheral.

This is strictly smaller than quotient suitability.  It mentions neither a
suitable subgroup nor a pair of witnesses; it is the maximality property for
one already-preserved elementary subgroup. -/
def OsinTheorem21QuotientClosureStatement : Prop :=
  ∀ (Q : Type u) (_ : Group Q) (Λ : Type v) (D : RelGenSet Q Λ),
    (∀ x ∈ D.base, x⁻¹ ∈ D.base) → D.IsHyperbolicallyEmbedded →
      ∀ (lam : Λ) (g : Q), g ∈ D.fam lam →
        (∀ n : ℕ, 0 < n → g ^ n ≠ 1) →
          osinElementaryClosure g ⊆ D.fam lam

/-- DGO Proposition 4.33 proves the quotient closure statement.

If `c` conjugates a positive power of `g` to that power or its inverse and
`c` were outside the peripheral, almost malnormality would make
`H ∩ H^c` finite.  All natural powers of that positive power lie in the
intersection, while infinite order makes the power map injective, a
contradiction. -/
theorem osinTheorem21QuotientClosureStatement :
    OsinTheorem21QuotientClosureStatement := by
  intro Q _ Λ D hbaseInv hemb lam g hg hord c hc
  by_contra hcP
  have hfinite :
      {x : Q | x ∈ D.fam lam ∧ c⁻¹ * x * c ∈ D.fam lam}.Finite :=
    finite_conj_inter D hbaseInv hemb (fun hbad => hcP hbad.2)
  obtain ⟨n, hn, hsame | hinverse⟩ := hc
  · have hpowInfinite : ¬ IsOfFinOrder (g ^ n) := by
      intro hfin
      obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
      exact hord (n * m) (Nat.mul_pos hn hm) (by rw [pow_mul, hpow])
    have hinj : Function.Injective (fun k : ℕ => (g ^ n) ^ k) :=
      HullSC.injective_pow_of_not_isOfFinOrder hpowInfinite
    have hsub : Set.range (fun k : ℕ => (g ^ n) ^ k) ⊆
        {x : Q | x ∈ D.fam lam ∧ c⁻¹ * x * c ∈ D.fam lam} := by
      rintro x ⟨k, rfl⟩
      refine ⟨pow_mem (pow_mem hg n) k, ?_⟩
      change c⁻¹ * (g ^ n) ^ k * c ∈ D.fam lam
      have hconj : (c⁻¹ * g ^ n * c) ^ k =
          c⁻¹ * (g ^ n) ^ k * c := by
        simpa only [inv_inv] using
          (@conj_pow Q _ k (c⁻¹) (g ^ n))
      rw [← hconj, hsame]
      exact pow_mem (pow_mem hg n) k
    exact Set.infinite_range_of_injective hinj (hfinite.subset hsub)
  · have hpowInfinite : ¬ IsOfFinOrder (g ^ n) := by
      intro hfin
      obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
      exact hord (n * m) (Nat.mul_pos hn hm) (by rw [pow_mul, hpow])
    have hinj : Function.Injective (fun k : ℕ => (g ^ n) ^ k) :=
      HullSC.injective_pow_of_not_isOfFinOrder hpowInfinite
    have hsub : Set.range (fun k : ℕ => (g ^ n) ^ k) ⊆
        {x : Q | x ∈ D.fam lam ∧ c⁻¹ * x * c ∈ D.fam lam} := by
      rintro x ⟨k, rfl⟩
      refine ⟨pow_mem (pow_mem hg n) k, ?_⟩
      change c⁻¹ * (g ^ n) ^ k * c ∈ D.fam lam
      have hconj : (c⁻¹ * g ^ n * c) ^ k =
          c⁻¹ * (g ^ n) ^ k * c := by
        simpa only [inv_inv] using
          (@conj_pow Q _ k (c⁻¹) (g ^ n))
      rw [← hconj, hinverse]
      exact pow_mem (inv_mem (pow_mem hg n)) k
    exact Set.infinite_range_of_injective hinj (hfinite.subset hsub)

/-! ## Distinct joint peripherals preserve hyperbolicity and separation -/

/-- An infinite-order element in one member of a hyperbolically embedded
family is hyperbolic relative to any disjointly indexed subfamily.

If it were conjugate into another labelled peripheral, all its powers would
lie in a twisted intersection which DGO Proposition 4.33 makes finite. -/
theorem isHyperbolicElement_of_mem_distinct_jointPeripheral
    {Q : Type u} [Group Q] {Lambda : Type v} (D : RelGenSet Q Lambda)
    (hbaseInv : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hemb : D.IsHyperbolicallyEmbedded)
    {I K : Type*} (original : I → Lambda) (selected : K → Lambda)
    (hdisjoint : ∀ i k, original i ≠ selected k)
    {k : K} {g : Q} (hg : g ∈ D.fam (selected k))
    (hord : ∀ n : ℕ, 0 < n → g ^ n ≠ 1) :
    IsHyperbolicElement (fun i => D.fam (original i)) g := by
  rintro ⟨i, c, hc⟩
  have hfinite :
      {x : Q | x ∈ D.fam (selected k) ∧
        c⁻¹ * x * c ∈ D.fam (original i)}.Finite :=
    finite_conj_inter D hbaseInv hemb (by
      rintro ⟨heq, -⟩
      exact hdisjoint i k heq.symm)
  have hnot : ¬ IsOfFinOrder g := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    exact hord n hn hpow
  have hinj : Function.Injective (fun n : ℕ => g ^ n) :=
    HullSC.injective_pow_of_not_isOfFinOrder hnot
  have hsub : Set.range (fun n : ℕ => g ^ n) ⊆
      {x : Q | x ∈ D.fam (selected k) ∧
        c⁻¹ * x * c ∈ D.fam (original i)} := by
    rintro x ⟨n, rfl⟩
    refine ⟨pow_mem hg n, ?_⟩
    have hconj : (c⁻¹ * g * c) ^ n = c⁻¹ * g ^ n * c := by
      simpa only [inv_inv] using (@conj_pow Q _ n c⁻¹ g)
    rw [← hconj]
    exact pow_mem hc n
  exact Set.infinite_range_of_injective hinj (hfinite.subset hsub)

/-- Infinite-order elements in two distinct members of one hyperbolically
embedded family remain non-commensurable.  A conjugacy between nonzero powers
would again put infinitely many powers in the finite twisted intersection. -/
theorem not_osinCommensurable_of_mem_distinct_jointPeripherals
    {Q : Type u} [Group Q] {Lambda : Type v} (D : RelGenSet Q Lambda)
    (hbaseInv : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hemb : D.IsHyperbolicallyEmbedded)
    {lam₁ lam₂ : Lambda} (hne : lam₁ ≠ lam₂)
    {g₁ g₂ : Q} (hg₁ : g₁ ∈ D.fam lam₁)
    (hg₂ : g₂ ∈ D.fam lam₂)
    (hord₁ : ∀ n : ℕ, 0 < n → g₁ ^ n ≠ 1) :
    ¬ OsinCommensurable g₁ g₂ := by
  rintro ⟨p, q, c, hp, hq, heq⟩
  have hfinite :
      {x : Q | x ∈ D.fam lam₁ ∧ c⁻¹ * x * c ∈ D.fam lam₂}.Finite :=
    finite_conj_inter D hbaseInv hemb (by
      rintro ⟨hlam, -⟩
      exact hne hlam.symm)
  have hg₁Infinite : ¬ IsOfFinOrder g₁ := by
    intro hfin
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    exact hord₁ n hn hpow
  have haInfinite : ¬ IsOfFinOrder (g₁ ^ p) :=
    HullSCUnionGeometry.not_isOfFinOrder_zpow hg₁Infinite hp
  have hinj : Function.Injective (fun n : ℕ => (g₁ ^ p) ^ n) :=
    HullSC.injective_pow_of_not_isOfFinOrder haInfinite
  have hsub : Set.range (fun n : ℕ => (g₁ ^ p) ^ n) ⊆
      {x : Q | x ∈ D.fam lam₁ ∧ c⁻¹ * x * c ∈ D.fam lam₂} := by
    rintro x ⟨n, rfl⟩
    refine ⟨pow_mem (zpow_mem hg₁ p) n, ?_⟩
    have hconj : (c⁻¹ * g₁ ^ p * c) ^ n =
        c⁻¹ * (g₁ ^ p) ^ n * c := by
      simpa only [inv_inv] using (@conj_pow Q _ n c⁻¹ (g₁ ^ p))
    rw [← hconj, heq]
    exact pow_mem (zpow_mem hg₂ q) n
  exact Set.infinite_range_of_injective hinj (hfinite.subset hsub)

/-- Two preserved source peripherals with trivial intersection give trivial
intersection of the Osin elementary closures of their infinite-order marked
elements.  Peripheral-union injectivity is exactly what lets the two quotient
preimages be identified. -/
theorem eq_one_of_preserved_osinElementaryClosures
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Λ : Type*}
    (eta : G →* Q) (D : RelGenSet Q Λ)
    (hbaseInv : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hemb : D.IsHyperbolicallyEmbedded) (lam₁ lam₂ : Λ)
    (E₁ E₂ : Subgroup G)
    (hfam₁ : D.fam lam₁ = E₁.map eta)
    (hfam₂ : D.fam lam₂ = E₂.map eta)
    (hinj : Set.InjOn eta ((E₁ : Set G) ∪ (E₂ : Set G)))
    {f₁ f₂ : G} (hf₁ : f₁ ∈ E₁) (hf₂ : f₂ ∈ E₂)
    (hord₁ : ∀ n : ℕ, 0 < n → eta f₁ ^ n ≠ 1)
    (hord₂ : ∀ n : ℕ, 0 < n → eta f₂ ^ n ≠ 1)
    (hinter : ∀ x, x ∈ E₁ → x ∈ E₂ → x = 1)
    {q : Q} (hq₁ : q ∈ osinElementaryClosure (eta f₁))
    (hq₂ : q ∈ osinElementaryClosure (eta f₂)) : q = 1 := by
  have hf₁Q : eta f₁ ∈ D.fam lam₁ := by
    rw [hfam₁]
    exact Subgroup.mem_map_of_mem eta hf₁
  have hf₂Q : eta f₂ ∈ D.fam lam₂ := by
    rw [hfam₂]
    exact Subgroup.mem_map_of_mem eta hf₂
  have hqE₁ : q ∈ E₁.map eta := by
    rw [← hfam₁]
    exact osinTheorem21QuotientClosureStatement Q inferInstance Λ D
      hbaseInv hemb lam₁ (eta f₁) hf₁Q hord₁ hq₁
  have hqE₂ : q ∈ E₂.map eta := by
    rw [← hfam₂]
    exact osinTheorem21QuotientClosureStatement Q inferInstance Λ D
      hbaseInv hemb lam₂ (eta f₂) hf₂Q hord₂ hq₂
  obtain ⟨x₁, hx₁, hx₁q⟩ := hqE₁
  obtain ⟨x₂, hx₂, hx₂q⟩ := hqE₂
  have hxeq : x₁ = x₂ := hinj (Or.inl hx₁) (Or.inr hx₂)
    (hx₁q.trans hx₂q.symm)
  subst x₂
  have hx1 : x₁ = 1 := hinter x₁ hx₁ hx₂
  subst x₁
  simpa using hx₁q.symm

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
    (hhyper₁ : IsHyperbolicElement (fun l => (Hfam l).map eta) (eta f₁))
    (hhyper₂ : IsHyperbolicElement (fun l => (Hfam l).map eta) (eta f₂))
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
