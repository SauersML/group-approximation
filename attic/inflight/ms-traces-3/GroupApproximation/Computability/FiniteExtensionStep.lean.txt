import GroupApproximation.Computability.OracleUse
import GroupApproximation.Meta.AxiomGuard

/-!
# The finite-extension step

For the antichain sentence of corollary `cor:wp` in `simple_kazhdan_sofic_group.tex`: "The Turing
degrees contain an antichain of size continuum [Odifreddi, Chapter V]".

Strings of bits are initial segments of sets of naturals (`Extends`).  For an oracle program `c` and
strings `σ`, `τ`, there are extensions `σ'` of `σ` and `τ'` of `τ` such that `c`, with any oracle
extending `τ'`, computes no set extending `σ'` (`exists_diag`).  The proof looks at the fresh
position `n = |σ|`.

* If some set extending `τ` makes `c` converge at `n`, the use principle fixes an initial segment
  `τ'` of that set, and `σ'` extends `σ` by the bit that disagrees with the output.
* Otherwise `c` diverges at `n` with every oracle extending `τ`, while the oracle of a set is total.

Requirements persist under extension (`Diag.mono`).
-/

namespace GroupApproximation
namespace OracleUse

open Classical

/-- The set `B` extends the string `σ`: the bits of `σ` are the memberships in `B` below `|σ|`. -/
def Extends (σ : List Bool) (B : Set ℕ) : Prop :=
  ∀ m, m < σ.length → σ[m]? = some (decide (m ∈ B))

theorem Extends.agreeBelow {σ : List Bool} {B C : Set ℕ} (hB : Extends σ B) (hC : Extends σ C) :
    AgreeBelow σ.length B C :=
  fun m hm => decide_eq_decide.1 (Option.some.inj ((hB m hm).symm.trans (hC m hm)))

theorem Extends.of_prefix {σ σ' : List Bool} {B : Set ℕ} (h : Extends σ' B) (hp : σ <+: σ') :
    Extends σ B := by
  intro m hm
  rw [List.prefix_iff_eq_take.1 hp, List.getElem?_take_of_lt hm]
  exact h m (lt_of_lt_of_le hm hp.length_le)

/-- The initial segment of length `N` of a set. -/
noncomputable def restrict (C : Set ℕ) (N : ℕ) : List Bool :=
  List.ofFn fun m : Fin N => decide ((m : ℕ) ∈ C)

theorem length_restrict (C : Set ℕ) (N : ℕ) : (restrict C N).length = N :=
  List.length_ofFn

theorem getElem?_restrict (C : Set ℕ) (N m : ℕ) :
    (restrict C N)[m]? = if _h : m < N then some (decide (m ∈ C)) else none := by
  unfold restrict
  exact List.getElem?_ofFn

theorem extends_restrict (C : Set ℕ) (N : ℕ) : Extends (restrict C N) C := by
  intro m hm
  rw [getElem?_restrict, dif_pos (lt_of_lt_of_eq hm (length_restrict C N))]

theorem prefix_restrict {τ : List Bool} {C : Set ℕ} {N : ℕ} (hC : Extends τ C)
    (hN : τ.length ≤ N) : τ <+: restrict C N := by
  refine List.prefix_iff_eq_take.2 (List.ext_getElem? fun m => ?_)
  rw [List.getElem?_take]
  by_cases hm : m < τ.length
  · rw [if_pos hm, getElem?_restrict, dif_pos (lt_of_lt_of_le hm hN)]
    exact hC m hm
  · rw [if_neg hm, List.getElem?_eq_none (Nat.le_of_not_lt hm)]

/-- The requirement: `c`, with any oracle extending `τ`, computes no set extending `σ`. -/
def Diag (c : OCode) (σ τ : List Bool) : Prop :=
  ∀ A C : Set ℕ, Extends σ A → Extends τ C → c.eval (setOracle C) ≠ setOracle A

/-- **Requirements persist under extension.** -/
theorem Diag.mono {c : OCode} {σ τ σ' τ' : List Bool} (h : Diag c σ τ) (hσ : σ <+: σ')
    (hτ : τ <+: τ') : Diag c σ' τ' :=
  fun A C hA hC => h A C (hA.of_prefix hσ) (hC.of_prefix hτ)

/-- **The finite-extension step.** -/
theorem exists_diag (c : OCode) (σ τ : List Bool) :
    ∃ σ' τ' : List Bool, σ <+: σ' ∧ τ <+: τ' ∧ Diag c σ' τ' := by
  by_cases hconv : ∃ (C : Set ℕ) (x : ℕ), Extends τ C ∧ x ∈ c.eval (setOracle C) σ.length
  · obtain ⟨C, x, hC, hx⟩ := hconv
    obtain ⟨N, hN⟩ := mem_eval_of_agreeBelow c C σ.length x hx
    refine ⟨σ ++ [decide (x = 0)], restrict C (max N τ.length), List.prefix_append _ _,
      prefix_restrict hC (le_max_right _ _), fun A C' hA hC' heq => ?_⟩
    have hagree : AgreeBelow N C C' :=
      ((extends_restrict C (max N τ.length)).agreeBelow hC').mono
        (by rw [length_restrict]; exact le_max_left _ _)
    have hx' : x ∈ c.eval (setOracle C') σ.length := hN C' hagree
    rw [heq] at hx'
    have hbit := hA σ.length (by simp)
    rw [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero] at hbit
    have e : decide (x = 0) = decide (σ.length ∈ A) := Option.some.inj hbit
    simp only [setOracle, Part.mem_some_iff] at hx'
    by_cases h0 : x = 0
    · rw [decide_eq_true h0] at e
      rw [if_pos (of_decide_eq_true e.symm)] at hx'
      exact absurd (h0.symm.trans hx') (by decide)
    · rw [decide_eq_false h0] at e
      rw [if_neg (of_decide_eq_false e.symm)] at hx'
      exact h0 hx'
  · refine ⟨σ, τ, List.prefix_refl σ, List.prefix_refl τ, fun A C hA hC heq => hconv ?_⟩
    refine ⟨C, if σ.length ∈ A then 1 else 0, hC, ?_⟩
    rw [heq]
    exact Part.mem_some _

end OracleUse
end GroupApproximation

#audit_axioms GroupApproximation.OracleUse.prefix_restrict
#audit_axioms GroupApproximation.OracleUse.exists_diag
