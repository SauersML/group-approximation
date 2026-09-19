import GroupApproximation.Sofic.HullSuitabilityGeometry

/-!
# `ExistsIndependentConjugate`, reduced to one conjugator outside the
commensurator

`Manuscript.NonMF.OsinNormalReduction.ExistsIndependentConjugate` asks that a
loxodromic `q` admit a conjugator `a` with `q` and `a q a⁻¹` independent.  This
module proves it from the third fact of that reduction — `AxisDichotomy`, which
is owned elsewhere — together with the single statement that *some* element
fails to commensurate `⟨q⟩`.

## The argument

`AxisDichotomy` applied to the pair `(q, a)` says that either `q` and
`a q⁻¹ a⁻¹` are independent, or `a qᵐ a⁻¹ = qⁿ` with both exponents nonzero.
Independence is insensitive to inverting either element — the defining Gromov
products are quantified over all of `ℤ`, which is `independent_inv_right`
below — and `a q⁻¹ a⁻¹ = (a q a⁻¹)⁻¹`, so the first branch is already the
conclusion.  The second branch says exactly that `a` commensurates the cyclic
group `⟨q⟩`.  So a conjugator that commensurates nothing lands in the first
branch, and that is the whole proof.

## What is left

`NotCommensurated q` — that some `a` satisfies `a qᵐ a⁻¹ ≠ qⁿ` for all nonzero
`m, n` — is the statement that the elementary closure `E(q)` is a proper
subgroup.  Under a non-elementary acylindrical action it is true and standard:
`E(q)` is virtually cyclic, while the group contains two independent
loxodromics, so it is not.  It is not proved here, and it is not a consequence
of the definitions in `Sofic.HullSuitabilityGeometry` as they stand: nothing
there converts "two independent loxodromics exist" into "some element moves the
endpoint pair of `q`".  `exists_notCommensurated_of_actsNonElementarily` is the
missing implication, stated so that the residue is one named proposition rather
than a paragraph.

## Status

**Not compiled**, written while builds were frozen, and unwired for that reason.
-/

namespace GroupApproximation
namespace GGT
namespace ElementaryFill

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## Independence ignores inversion -/

/-- **Independence is insensitive to inverting the second element.**  The
defining bound quantifies over every integer exponent, so replacing `k` by `k⁻¹`
only reindexes it. -/
theorem independent_inv_right {g k : G} {x : X} (h : Independent g k x) :
    Independent g k⁻¹ x := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun n m => ?_⟩
  have hk : (k⁻¹ : G) ^ m = k ^ (-m) := by
    rw [inv_zpow, ← zpow_neg]
  rw [hk]
  exact hC n (-m)

/-- The same for the first element. -/
theorem independent_inv_left {g k : G} {x : X} (h : Independent g k x) :
    Independent g⁻¹ k x := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun n m => ?_⟩
  have hg : (g⁻¹ : G) ^ n = g ^ (-n) := by
    rw [inv_zpow, ← zpow_neg]
  rw [hg]
  exact hC (-n) m

/-! ## Commensuration -/

/-- **`a` commensurates the axis of `q`**: a nonzero power of `q` is conjugated
by `a` to a nonzero power of `q`.  This is the second branch of `AxisDichotomy`,
named. -/
def Commensurates (q a : G) : Prop :=
  ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ a * q ^ m * a⁻¹ = q ^ n

/-- **Some element commensurates nothing**: the elementary closure of `q` is a
proper subgroup.  Nothing below inhabits this. -/
def NotCommensurated (q : G) : Prop :=
  ∃ a : G, ¬ Commensurates q a

/-! ## The conjugate -/

/-- **A loxodromic element with a non-commensurating conjugator has an
independent conjugate.**

The hypothesis `hdich` is
`Manuscript.NonMF.OsinNormalReduction.AxisDichotomy G x` written out; that
module is not imported here, so that this development stays below the manuscript
layer. -/
theorem exists_independent_conjugate_of_notCommensurated
    {x : X}
    (hdich : ∀ g c : G, IsLoxodromic g x →
      Independent g (c * g⁻¹ * c⁻¹) x ∨
        ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ c * g ^ m * c⁻¹ = g ^ n)
    {q : G} (hq : IsLoxodromic q x) (hnc : NotCommensurated q) :
    ∃ a : G, Independent q (a * q * a⁻¹) x := by
  obtain ⟨a, hane⟩ := hnc
  rcases hdich q a hq with hind | ⟨m, n, hm, hn, hpow⟩
  · refine ⟨a, ?_⟩
    have hrw : a * q⁻¹ * a⁻¹ = (a * q * a⁻¹)⁻¹ := by group
    rw [hrw] at hind
    simpa using independent_inv_right hind
  · exact (hane ⟨m, n, hm, hn, hpow⟩).elim

/-- **The named fact, from the dichotomy and properness of the elementary
closure.**  The conclusion is
`Manuscript.NonMF.OsinNormalReduction.ExistsIndependentConjugate G x` written
out.  Non-elementarity is consumed only through `hproper`, which is where it
belongs: the dichotomy is a statement about a single axis and knows nothing
about the ambient group. -/
theorem existsIndependentConjugate_of_notCommensurated
    {x : X}
    (hdich : ∀ g c : G, IsLoxodromic g x →
      Independent g (c * g⁻¹ * c⁻¹) x ∨
        ∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ c * g ^ m * c⁻¹ = g ^ n)
    (hproper : ActsNonElementarily (⊤ : Subgroup G) x →
      ∀ q : G, IsLoxodromic q x → NotCommensurated q) :
    ActsNonElementarily (⊤ : Subgroup G) x →
      ∀ q : G, IsLoxodromic q x → ∃ a : G, Independent q (a * q * a⁻¹) x := by
  intro hne q hq
  exact exists_independent_conjugate_of_notCommensurated hdich hq
    (hproper hne q hq)

/-! ## What the residue says about a commensurating group -/

/-- **If nothing commensurates fails, every element commensurates.**  Recorded
so that the residue can be attacked in the contrapositive: an ambient group all
of whose elements commensurate `⟨q⟩` is its own elementary closure, and that is
the configuration a non-elementary action has to rule out. -/
theorem forall_commensurates_of_not_notCommensurated {q : G}
    (h : ¬ NotCommensurated q) (a : G) : Commensurates q a := by
  by_contra hcon
  exact h ⟨a, hcon⟩

end ElementaryFill
end GGT
end GroupApproximation
