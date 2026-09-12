import GroupApproximation.Algebra.NaiveFreeProductProperty
import GroupApproximation.Algebra.PingPongTranslates

/-!
# Property `P_naive` gives ping-pong families of conjugates

If the canonical homomorphism `⟨f⟩ ∗ ⟨y⟩ →* G` is injective, `f ≠ 1`, and `y` has
infinite order, then for every `n` the conjugates

    yⁱ f y⁻ⁱ   (0 ≤ i < n)

form a ping-pong family in `G` (`isPingPongFamily_conj_pow_of_injective`).  So
`NaiveFreeProductProperty G` gives `PingPongConjugateProperty G`: for every finite
`F ⊆ G ∖ {1}` and every `n` there are `g₀, …, g_{n-1}` (namely `gᵢ = yⁱ`) such
that for each `f ∈ F` the family `gᵢ f gᵢ⁻¹` is a ping-pong family.

## The argument

The free product acts on its reduced words (`Monoid.CoprodI.Word`).  Let `X₁` be
the words whose first letter comes from `⟨f⟩` and `X₂` those whose first letter
comes from `⟨y⟩`.  Then `X₁ ∩ X₂ = ∅`; a nontrivial power `yᵏ` prepended to a word
beginning in `⟨f⟩` gives a word beginning in `⟨y⟩`, so `yᵏ • X₁ ⊆ X₂`; and `f⁻¹`
prepended to a word not beginning in `⟨f⟩` gives a word beginning in `⟨f⟩`, so
`f⁻¹ • (Ω ∖ X₁) ⊆ X₁`.  `PingPongTranslates.isPingPongOn_conj_pow` turns these
three facts into a ping-pong family on the words, the orbit map at the empty word
pulls it back to the free product, and injectivity pushes it forward to `G`.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace NaiveFreeProduct

open scoped Pointwise
open PingPongTranslates

universe u

variable {G : Type u} [Group G]

/-- **Ping-pong families of conjugates by one averaging family.**  For every
finite `F ⊆ G ∖ {1}` and every `n > 0` there are `g₀, …, g_{n-1}` such that for
each `f ∈ F` the conjugates `gᵢ f gᵢ⁻¹` form a ping-pong family. -/
def PingPongConjugateProperty (G : Type u) [Group G] : Prop :=
  ∀ F : Finset G, (1 : G) ∉ F → ∀ n : ℕ, 0 < n →
    ∃ g : Fin n → G, ∀ f ∈ F, IsPingPongFamily (fun i ↦ g i * f * (g i)⁻¹)

/-- The family of the two cyclic factors, as types.  Stating letters and words
over this constant (rather than over `fun b ↦ ↥(cyclicPair f y b)`) lets
`Monoid.CoprodI.of` infer its index family by first-order unification. -/
abbrev cyclicFamily (f y : G) : Bool → Type u :=
  fun b ↦ ↥(cyclicPair f y b)

/-- The letter `f` of the factor `⟨f⟩`. -/
def fLetter (f y : G) : cyclicFamily f y false :=
  ⟨f, Subgroup.mem_zpowers f⟩

/-- The letter `y` of the factor `⟨y⟩`. -/
def yLetter (f y : G) : cyclicFamily f y true :=
  ⟨y, Subgroup.mem_zpowers y⟩

section Words

variable {f y : G} [∀ b : Bool, DecidableEq (cyclicFamily f y b)]

/-- Prepending a nontrivial letter from factor `i` to a word that does not begin
in factor `i` gives a word beginning in factor `i`. -/
theorem fstIdx_of_smul_of_ne {i : Bool} {m : cyclicFamily f y i} (hm : m ≠ 1)
    {w : Monoid.CoprodI.Word (cyclicFamily f y)}
    (hw : w.fstIdx ≠ some i) :
    ((Monoid.CoprodI.of m : Monoid.CoprodI (cyclicFamily f y)) • w).fstIdx = some i := by
  rw [Monoid.CoprodI.Word.of_smul_def, Monoid.CoprodI.Word.equivPair_eq_of_fstIdx_ne hw]
  simp [Monoid.CoprodI.Word.rcons, hm]

end Words

/-- **The conjugates `yⁱ f y⁻ⁱ` form a ping-pong family in `G`** whenever
`f ≠ 1`, `y` has infinite order, and `⟨f⟩ ∗ ⟨y⟩ →* G` is injective. -/
theorem isPingPongFamily_conj_pow_of_injective {f y : G} (hf : f ≠ 1)
    (hy : ∀ k : ℤ, k ≠ 0 → y ^ k ≠ 1) (hinj : Function.Injective (cyclicPairLift f y))
    (n : ℕ) : IsPingPongFamily (fun i : Fin n ↦ y ^ (i : ℕ) * f * (y ^ (i : ℕ))⁻¹) := by
  classical
  let X₁ : Set (Monoid.CoprodI.Word (cyclicFamily f y)) :=
    {w | w.fstIdx = some false}
  let X₂ : Set (Monoid.CoprodI.Word (cyclicFamily f y)) :=
    {w | w.fstIdx = some true}
  have hdisj : Disjoint X₁ X₂ := by
    refine Set.disjoint_left.mpr fun w h₁ h₂ ↦ ?_
    have h₁' : w.fstIdx = some false := h₁
    have h₂' : w.fstIdx = some true := h₂
    rw [h₁'] at h₂'
    exact absurd h₂' (by simp)
  have hyX : ∀ k : ℤ, k ≠ 0 →
      (Monoid.CoprodI.of (yLetter f y) : Monoid.CoprodI (cyclicFamily f y)) ^ k • X₁ ⊆ X₂ := by
    intro k hk
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w.fstIdx = some false := hw
    show ((Monoid.CoprodI.of (yLetter f y) : Monoid.CoprodI (cyclicFamily f y)) ^ k • w).fstIdx
      = some true
    rw [← map_zpow]
    refine fstIdx_of_smul_of_ne ?_ (by rw [hw']; simp)
    intro h1
    apply hy k hk
    have h2 := congrArg (fun z : cyclicFamily f y true ↦ (z : G)) h1
    simpa [yLetter] using h2
  have hfX : (Monoid.CoprodI.of (fLetter f y) : Monoid.CoprodI (cyclicFamily f y))⁻¹ • X₁ᶜ ⊆ X₁ := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w.fstIdx ≠ some false := hw
    show ((Monoid.CoprodI.of (fLetter f y) : Monoid.CoprodI (cyclicFamily f y))⁻¹ • w).fstIdx
      = some false
    rw [← map_inv]
    refine fstIdx_of_smul_of_ne ?_ hw'
    intro h1
    apply hf
    have h2 := congrArg (fun z : cyclicFamily f y false ↦ (z : G)) h1
    simpa [fLetter] using h2
  have hK := (isPingPongOn_conj_pow
    (Monoid.CoprodI.of (fLetter f y) : Monoid.CoprodI (cyclicFamily f y))
    (Monoid.CoprodI.of (yLetter f y) : Monoid.CoprodI (cyclicFamily f y)) X₁ X₂ hdisj hyX hfX
    n).isPingPongFamily (Monoid.CoprodI.Word.empty : Monoid.CoprodI.Word (cyclicFamily f y))
  have hG := hK.map_of_injective (cyclicPairLift f y) hinj
  simpa [cyclicPairLift, Monoid.CoprodI.lift_of, fLetter, yLetter] using hG

/-- **`P_naive` gives ping-pong families of conjugates**, with `gᵢ = yⁱ`. -/
theorem pingPongConjugateProperty_of_naiveFreeProductProperty
    (h : NaiveFreeProductProperty G) : PingPongConjugateProperty G := by
  intro F hF n _
  obtain ⟨y, hy, hinj⟩ := h F hF
  refine ⟨fun i ↦ y ^ (i : ℕ), fun f hfF ↦ ?_⟩
  have hf : f ≠ 1 := fun h1 ↦ hF (h1 ▸ hfF)
  exact isPingPongFamily_conj_pow_of_injective hf hy (hinj f hfF) n

end NaiveFreeProduct
end GroupApproximation

open GroupApproximation.NaiveFreeProduct

#audit_axioms PingPongConjugateProperty
#audit_axioms cyclicFamily
#audit_axioms fstIdx_of_smul_of_ne
#audit_axioms isPingPongFamily_conj_pow_of_injective
#audit_axioms pingPongConjugateProperty_of_naiveFreeProductProperty
