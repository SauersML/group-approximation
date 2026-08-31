import GroupApproximation.GGT.HullSCRelatorSeparation2Inputs

/-!
# The unrestricted block-count input is false

`RelatorBlockCountInputOne₂` currently quantifies over every exponent list.
Taking an arbitrarily long list of zero exponents makes every component letter
spell the identity.  With base word `[1]`, the full relator path is closed at
`1`, contradicting any fixed additive block-count constant.  The active API
must therefore scope the count to the jointly chosen deep exact design.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section Counterexample

variable {G : Type u} [Group G]
  {A : HullGeneratingSet G} {N : Subgroup G}

/-- A block word whose exponents are all zero spells the identity. -/
theorem listVal_blockWord_replicate_zero (h₀ h₁ : G) (s : Bool) :
    ∀ n : ℕ,
      GGT.RelLetter.listVal (blockWord h₀ h₁ s (List.replicate n 0)) = 1 := by
  intro n
  induction n generalizing s with
  | zero => rw [List.replicate_zero, blockWord_nil, GGT.RelLetter.listVal_nil]
  | succ n ih =>
      rw [List.replicate_succ, blockWord_cons, RelWord.listVal_cons,
        GGT.RelLetter.val, pow_zero, one_mul]
      exact ih (!s)

/-- No finite constant satisfies the current all-list block-count predicate. -/
theorem not_relatorBlockCountInputOne₂
    (E : HypEmbeddedCore₂ A N) (cnt : ℕ) :
    ¬ RelatorBlockCountInputOne₂ E cnt := by
  intro hcount
  let p : List G := [1]
  let ms : List ℕ := List.replicate (cnt + 2) 0
  let v := relatorWord₂ p (E.lox false) (E.lox true) ms
  have hv : RelWord.Sym
      (relatorWord₂ p (E.lox false) (E.lox true) ms) v := by
    exact RelWord.Sym.base
  have hval : GGT.RelLetter.listVal v = 1 := by
    rw [show v = relatorWord₂ p (E.lox false) (E.lox true) ms from rfl,
      listVal_relatorWord₂]
    change ([1] : List G).prod * GGT.RelLetter.listVal
      (blockWord (E.lox false) (E.lox true) false
        (List.replicate (cnt + 2) 0)) = 1
    rw [listVal_blockWord_replicate_zero]
    simp
  have hbad := hcount p (by simp [p]) ms v hv 0 v.length
    (Nat.zero_le _) (le_refl _)
  have hv0 : GGT.OsinComponents.vertex (1 : G) v 0 = 1 := by
    rw [GGT.OsinComponents.vertex_zero]
  have hvend : GGT.OsinComponents.vertex (1 : G) v v.length = 1 := by
    rw [GGT.OsinComponents.vertex_eq_mul_listVal_take, List.take_length,
      hval, mul_one]
  rw [Nat.sub_zero, hv0, hvend, wordDist_self, Nat.zero_add,
    blockConst] at hbad
  have hvlen : v.length = cnt + 3 := by
    simp only [v, p, ms, length_relatorWord₂, List.length_singleton,
      List.length_replicate]
    omega
  have hplen : p.length = 1 := by simp [p]
  rw [hvlen, hplen] at hbad
  omega

/-- In particular, the quantified existence requested by the former exact
separation endpoint is contradictory. -/
theorem not_exists_relatorBlockCountInputOne₂
    (E : HypEmbeddedCore₂ A N) :
    ¬ ∃ cnt : ℕ, RelatorBlockCountInputOne₂ E cnt := by
  rintro ⟨cnt, hcnt⟩
  exact not_relatorBlockCountInputOne₂ E cnt hcnt

end Counterexample

end HullSC
end GroupApproximation
