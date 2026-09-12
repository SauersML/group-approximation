import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The stack dichotomy at arbitrary arity

`KOne/StackDichotomy.lean` is the branching device of the binary pencil elimination:
over a field the stacked matrix `[B₀; B₁]` either has a scalar left inverse or a
nontrivial kernel vector.  At arity `d` the pencil carries one `s`-coefficient matrix
for each letter, so the stack is `[B_z]_{z : μ}`, indexed by the alphabet.  The proof is
the same linear algebra with the two-block sum type replaced by the product `μ × ι`.
-/

namespace GroupApproximation

/-- **The stack dichotomy.**  A family `B z : ι → κ → k` of rectangular scalar matrices,
one per letter `z`, either admits scalar matrices `G z : κ → ι → k` with
`∑_z G_z B_z = 1`, or has a nonzero common kernel vector. -/
theorem stack_left_inverse_or_kernel_ary {k : Type*} [Field k]
    {μ ι κ : Type*} [Fintype μ] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : μ → ι → κ → k) :
    (∃ G : μ → κ → ι → k, ∀ j j' : κ,
      (∑ z, ∑ i, G z j i * B z i j') = if j = j' then 1 else 0) ∨
    (∃ v : κ → k, v ≠ 0 ∧ ∀ z i, ∑ j, B z i j * v j = 0) := by
  classical
  set M : Matrix (μ × ι) κ k := Matrix.of (fun p j ↦ B p.1 p.2 j) with hM
  by_cases hker : LinearMap.ker M.mulVecLin = ⊥
  · left
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin hker
    set N : Matrix κ (μ × ι) k := LinearMap.toMatrix' g with hN
    refine ⟨fun z j i ↦ N j (z, i), fun j j' ↦ ?_⟩
    have hcol : (fun p ↦ M p j') = M.mulVec (Pi.single j' 1) := by
      funext p
      simp [Matrix.mulVec_single]
    calc (∑ z, ∑ i, N j (z, i) * B z i j')
        = ∑ p : μ × ι, N j p * M p j' := by
          rw [Fintype.sum_prod_type]
          rfl
      _ = (N.mulVec (fun p ↦ M p j')) j := by
          simp [Matrix.mulVec, dotProduct]
      _ = (N.mulVec (M.mulVec (Pi.single j' 1))) j := by rw [hcol]
      _ = (g.comp M.mulVecLin) (Pi.single j' 1) j := by
          rw [hN]
          have h1 : ∀ x : μ × ι → k,
              (LinearMap.toMatrix' g).mulVec x = g x := by
            intro x
            rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
          rw [h1]
          have h2 : M.mulVec (Pi.single j' 1) =
              M.mulVecLin (Pi.single j' 1) := rfl
          rw [h2]
          rfl
      _ = if j = j' then 1 else 0 := by
          rw [hg]
          simp [Pi.single_apply]
  · right
    obtain ⟨v, hvmem, hv⟩ := Submodule.ne_bot_iff _ |>.mp hker
    refine ⟨v, hv, fun z i ↦ ?_⟩
    have h := congrFun (LinearMap.mem_ker.mp hvmem) (z, i)
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hM] using h

end GroupApproximation
