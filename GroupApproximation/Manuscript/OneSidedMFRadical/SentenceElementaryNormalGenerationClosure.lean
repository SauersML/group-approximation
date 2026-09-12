import GroupApproximation.Manuscript.OneSidedMFRadical.RankTwelveSimplicity

/-!
# Printed elementary normal-generation sentences

This module gives standalone names to manuscript census rows 228--232.  The
commutators are stated as the literal four-factor products printed in the
paper, and the final theorem records both propagation to every root and
generation of the whole elementary group.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u v

/-! ## Row 228: the scalar branch -/

/-- **Sentence 228.**  Every central unit of the exact binary Leavitt
coefficient ring over `𝔽₂` is the identity. -/
theorem manuscriptSentence228_centralUnit_eq_one
    (z : RankTwelveEndpoint.Rˣ)
    (hz : ∀ r : RankTwelveEndpoint.R,
      (z : RankTwelveEndpoint.R) * r = r * (z : RankTwelveEndpoint.R)) :
    z = 1 :=
  BinaryLeavitt.central_units_trivial z hz

/-! ## Row 229: a sandwiched root normally generates -/

/-- **Sentence 229, normal-generation clause.**  A normal subgroup containing
one elementary root whose coefficient sandwiches to `1` is the whole
elementary group. -/
theorem manuscriptSentence229_sandwichedRoot_normalGenerates
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι S)) [N.Normal]
    {i j : ι} (hij : i ≠ j) {x : S}
    (hx : elGen i j hij x ∈ N)
    (hsandwich : ∃ a b : S, a * x * b = 1) :
    N = ⊤ :=
  elementaryGroup_normal_eq_top_of_elGen_mem
    hcard N hij hx hsandwich

/-- **Sentence 229, reduction clause.**  Once every nontrivial normal subgroup
contains a nonzero root, the sandwich property closes the printed simplicity
argument. -/
theorem manuscriptSentence229_simplicity_reduces_to_rootDetection
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (hcard : 3 ≤ Fintype.card ι)
    (hdivide : ∀ x : S, x ≠ 0 → ∃ a b : S, a * x * b = 1)
    (hnontrivial : Nontrivial (elementaryGroup ι S))
    (hdetect : ElementarySimplicity.RootDetection ι S) :
    IsSimpleGroup (elementaryGroup ι S) :=
  ElementarySimplicity.isSimpleGroup_of_rootDetection
    hcard hdivide hnontrivial hdetect

/-! ## Row 230: the two commutators producing a unit root -/

/-- **Sentence 230.**  The two displayed Steinberg commutators first attach
the right sandwich coefficient and then the left one, producing a unit root. -/
theorem manuscriptSentence230_unitRootCommutators
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (i j k : ι) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {a x b : S} (hsandwich : a * x * b = 1) :
    elGen i j hij x * elGen j k hjk b * (elGen i j hij x)⁻¹ *
          (elGen j k hjk b)⁻¹ = elGen i k hik (x * b) ∧
      elGen j i hij.symm a * elGen i k hik (x * b) *
          (elGen j i hij.symm a)⁻¹ * (elGen i k hik (x * b))⁻¹ =
        elGen j k hjk 1 := by
  constructor
  · exact elGen_commutator i j k hij hjk hik x b
  · calc
      elGen j i hij.symm a * elGen i k hik (x * b) *
            (elGen j i hij.symm a)⁻¹ * (elGen i k hik (x * b))⁻¹ =
          elGen j k hjk (a * (x * b)) :=
        elGen_commutator j i k hij.symm hik hjk a (x * b)
      _ = elGen j k hjk 1 := by rw [← mul_assoc, hsandwich]

/-! ## Row 231: source and target moves -/

/-- **Sentence 231.**  The printed source and target commutators move a unit
root to either adjacent root line while attaching an arbitrary coefficient. -/
theorem manuscriptSentence231_sourceTargetMoves
    {ι : Type u} {S : Type v} [Fintype ι] [DecidableEq ι] [Ring S]
    (u v w : ι) (huv : u ≠ v) (hwu : w ≠ u)
    (hwv : w ≠ v) (hvw : v ≠ w) (huw : u ≠ w) (r : S) :
    elGen w u hwu r * elGen u v huv 1 * (elGen w u hwu r)⁻¹ *
          (elGen u v huv 1)⁻¹ = elGen w v hwv r ∧
      elGen u v huv 1 * elGen v w hvw r * (elGen u v huv 1)⁻¹ *
          (elGen v w hvw r)⁻¹ = elGen u w huw r := by
  constructor
  · simpa using elGen_commutator w u v hwu huv hwv r (1 : S)
  · simpa using elGen_commutator u v w huv hvw huw (1 : S) r

/-! ## Row 232: repeating the moves reaches every generator -/

/-- **Sentence 232.**  Killing one unit root kills every elementary generator;
because those roots generate the elementary group, the homomorphism is
trivial on every group element. -/
theorem manuscriptSentence232_movesGiveEveryElementaryGenerator
    {ι : Type u} {S : Type v} {Q : Type*}
    [Fintype ι] [DecidableEq ι] [Ring S] [Group Q]
    (hcard : 3 ≤ Fintype.card ι)
    (phi : elementaryGroup ι S →* Q)
    {p q : ι} (hpq : p ≠ q)
    (hbase : phi (elGen p q hpq 1) = 1) :
    (∀ (l k : ι) (hlk : l ≠ k) (c : S),
        phi (elGen l k hlk c) = 1) ∧
      ∀ g : elementaryGroup ι S, phi g = 1 := by
  have hall : ∀ (l k : ι) (hlk : l ≠ k) (c : S),
      phi (elGen l k hlk c) = 1 :=
    elGen_map_eq_one_all hcard phi hpq hbase
  exact ⟨hall, elementaryGroup_hom_eq_one_of_gens phi hall⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
