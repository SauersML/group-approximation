import GroupApproximation.GroupTheory.HydeLodha.QTwoLemmaFourSixCaseOne

/-!
# Hyde–Lodha Lemma 4.6: the piece statements

Hyde–Lodha, Lemma 4.6 (label `FPlem3`): "For all `Γ` satisfying `Q_n ≤ Γ ≤ Γ_n` and `I = [a, b] ⊂ ℝ`
with `|I| ≤ 1`, `Υ_Γ(I)` is of type `F_∞`."  Proposition 4.7 consumes finite presentation at grid
endpoints, `UpsilonFinitelyPresented` (`QTwoFinitePresentationStabK`).

The proof: "We will prove the lemma by isolating a group `H ≅ F_{η_n}` such that `⟨f, H⟩, Υ_{Γ_n}(I)` is
a casing pair for `Υ_Γ(I)`, which will imply that `Υ_Γ(I)` is of type `F_∞` using Lemma 4.2."
The pieces:

* `LemmaFourSixDynamicsStatement`: tex 873–877 and 887–888, in the unit frame `0 < a < b < 1`.
  "Using Lemma 4.3, we find `f ∈ Υ_{Q_n}(I)` such that `a·f'_+, b·f'_- > 1`. ... there exists a closed
  interval `J ⊂ (0,1) ∩ (a, b)` with endpoints in `ℤ[1/η_n]` so that `J·f ⊂ J` and
  `⋃_{n ∈ ℕ} J·f^{-n} = (a, b)`. ... Let `J_0 = J·f`.  We choose `s_i ∈ Υ_{F_{η_n}'}(J) ≤ Υ_Γ(I)` such that
  `{J_i = J_0·s_i | 1 ≤ i ≤ η_n}` are pairwise disjoint intervals in `J \ J_0`."
  Here `J = [e₁, e₂]`, `J·f ⊆ [c, d]`, the germ `t ↦ a + 6 (t - a)` at `a⁺` is the slope condition
  at `a`, and the covering property is stated in the form Case 1 consumes: every `k ∈ Υ^c_{Γ₂}(I)` has
  a conjugate `f^n k f^{-n}` in `Υ^c_{Γ₂}([c, d])`.
* `LemmaFourSixCaseOneStatement`: the casing subgroup `N = ⟨f, H⟩` in the unit frame.  "`⟨f, H⟩` is an
  ascending HNN extension of `H`, and hence of type `F_∞`" and "`Υ_{Γ_n}(I)' ⊆ ⋃_{n ∈ ℕ} f^n H f^{-n}`".
  It follows from the dynamics, `exists_twisted_generators` and `pow_conj_mem_commutator_upsilon`.

`UpsilonFinitelyPresented` follows from `LemmaFourSixCaseOneStatement` through Lemma 4.2
(`isFinitelyPresented_of_commutator_le`), conjugation into the unit frame and, for `|I| = 1`, an
ascending HNN extension over a shorter interval as in `QTwoFinitePresentationLong`.

Permutations compose right to left: the paper's `J·f` is `f '' J` and its `f^{-n} k f^n` is
`f ^ n * k * (f ^ n)⁻¹`.
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

/-- **Hyde–Lodha, proof of Lemma 4.6, tex 873–877 and 887–888**, in the unit frame: the contracting
element `f ∈ Υ_{Q₂}([a, b])`, the intervals `J = [e₁, e₂]` and `[c, d] ⊇ J·f`, and the elements
`s_i ∈ Υ_{Q₂}(J)` moving `(c, d) + ℤ` to pairwise disjoint sets off itself. -/
def LemmaFourSixDynamicsStatement : Prop :=
  ∀ a b : ℚ, (∃ M, a ∈ Grid 6 M) → (∃ M, b ∈ Grid 6 M) → 0 < a → a < b → b < 1 →
    ∃ f ∈ upsilon qTwo a b, (∃ ε : ℚ, GermLeft 4 a 1 ε f) ∧
      ∃ e₁ e₂ c d : ℚ, (∃ M, c ∈ Grid 6 M) ∧ (∃ M, d ∈ Grid 6 M) ∧
        a < e₁ ∧ e₁ < c ∧ c < d ∧ d < e₂ ∧ e₂ < b ∧ c ≤ f e₁ ∧ f e₂ ≤ d ∧
        (∀ k ∈ upsilonc gammaTwo a b, ∃ n : ℕ, f ^ n * k * (f ^ n)⁻¹ ∈ upsilonc gammaTwo c d) ∧
        ∃ s : Fin 6 → Equiv.Perm ℚ, (∀ i, s i ∈ upsilon qTwo e₁ e₂) ∧
          (∀ i, Disjoint (s i '' perIoo c d) (perIoo c d)) ∧
          (∀ i j, i ≠ j → Disjoint (s i '' perIoo c d) (s j '' perIoo c d))

/-- **Hyde–Lodha, proof of Lemma 4.6, Case 1**, in the unit frame: a finitely presented `N ≤ Υ_{Q₂}(I)`
containing `Υ_{Γ₂}(I)'`, so that `N, Υ_{Γ₂}(I)` is a casing pair for every `Υ_Γ(I)`. -/
def LemmaFourSixCaseOneStatement : Prop :=
  ∀ a b : ℚ, (∃ M, a ∈ Grid 6 M) → (∃ M, b ∈ Grid 6 M) → 0 < a → a < b → b < 1 →
    ∃ N : Subgroup (Equiv.Perm ℚ), Group.IsFinitelyPresented ↥N ∧ N ≤ upsilon qTwo a b ∧
      ⁅upsilon gammaTwo a b, upsilon gammaTwo a b⁆ ≤ N

end HydeLodha
end GroupApproximation
