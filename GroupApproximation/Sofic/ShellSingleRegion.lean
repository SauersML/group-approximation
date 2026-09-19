import GroupApproximation.Sofic.CurvatureAssembly
import GroupApproximation.Sofic.GreendlingerDeepInduction

/-!
# The one-region case of the shell

`Sofic/CurvatureAssembly` reduces the sharp Greendlinger gate to
`ShellFromMinimal`: for a `C'(λ)` family and a reduced nonempty `w` with a
minimal conjugate-product expression, produce a symmetrized relator `r` split as
`δ ++ p₁ ++ p₂ ++ p₃` with `δ` an infix of `w` and each `pᵢ` an interior run.
That is Greendlinger's lemma in shell form, and the classical proof of it is an
induction whose base is the diagram with a single region.

This file proves that base, unconditionally.

## The statement

When the minimal expression is a single factor, `w` *is* a palindrome
`c ++ r ++ invRev c` for a symmetrized `r`, so `r` occurs in `w` outright and the
shell is degenerate: `δ = r` and all three interior runs empty.  `InteriorRun`
admits the empty word (`p = [] ∨ IsPiece ...`), which is exactly the slot this
case needs, and `length_lt_of_interiorRun` prices an empty run at `0 < λ·|r|` --
so the arithmetic of `CurvatureAssembly` goes through with nothing to subtract.

## Where the work is

Only in identifying `w`.  `GreendlingerWeight.exists_palindrome_factor` puts the
single factor into palindromic normal form, giving `c` and a rotation `r` of the
relator with `palindrome c r` **reduced** and spelling the same element as the
factor.  Since the expression evaluates to `mk w` and `w` is reduced too, the two
reduced words spelling one element are equal (`FreeGroup.reduce.sound` against
`IsReduced.reduce_eq` on both sides), so `w = palindrome c r` on the nose and `r`
is an infix by construction.

Minimality is used only through validity -- the factor's word is symmetrized.
Neither the length nor the weight clause is read, so the result holds for any
one-factor expression whose palindrome is reduced, which is what
`shell_of_singleton_conjValid` records.

Nothing here closes `ShellFromMinimal`: the content of that statement is the
induction step, where the diagram has at least two regions and the curvature
count decides which one is a shell.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*} [DecidableEq α]

/-- **The one-region shell.**  A single-factor expression for a reduced `w`
exhibits its own relator as an infix of `w`, with all three interior runs
empty. -/
theorem shell_of_singleton_conjValid {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {w : List (α × Bool)} {x : FreeGroup α} {s : List (α × Bool)}
    (hw : FreeGroup.IsReduced w) (hs : s ∈ symmetrization R)
    (heval : conjEval [(x, s)] = FreeGroup.mk w) :
    ∃ r ∈ symmetrization R, r ≠ [] ∧ ∃ δ p₁ p₂ p₃ : List (α × Bool),
      r = δ ++ (p₁ ++ (p₂ ++ p₃)) ∧ δ <:+: w ∧
        InteriorRun R r p₁ ∧ InteriorRun R r p₂ ∧ InteriorRun R r p₃ := by
  obtain ⟨c, r, hr, hredp, hconj, -⟩ := exists_palindrome_factor hR hRne hs x
  have hev : FreeGroup.mk (palindrome c r) = FreeGroup.mk w := by
    rw [mk_palindrome, hconj, ← heval, conjEval_cons, conjEval_nil, mul_one]
  have heq : palindrome c r = w := by
    have h := FreeGroup.reduce.sound hev
    rwa [hredp.reduce_eq, hw.reduce_eq] at h
  have hinf : r <:+: w := by
    rw [← heq]
    exact ⟨c, FreeGroup.invRev c, rfl⟩
  refine ⟨r, hr, ne_nil_of_mem_symmetrization hRne hr, r, [], [], [], by simp,
    hinf, ?_, ?_, ?_⟩ <;>
    exact ⟨List.nil_infix, Or.inl rfl⟩

/-- The same at a minimal expression, which is how `ShellFromMinimal` presents
its instances.  Only the validity clause of minimality is read. -/
theorem shell_of_singleton_minimal {R : Set (List (α × Bool))}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    {w : List (α × Bool)} {x : FreeGroup α} {s : List (α × Bool)}
    (hw : FreeGroup.IsReduced w)
    (hmin : IsMinimalConjExpr R [(x, s)] (FreeGroup.mk w)) :
    ∃ r ∈ symmetrization R, r ≠ [] ∧ ∃ δ p₁ p₂ p₃ : List (α × Bool),
      r = δ ++ (p₁ ++ (p₂ ++ p₃)) ∧ δ <:+: w ∧
        InteriorRun R r p₁ ∧ InteriorRun R r p₂ ∧ InteriorRun R r p₃ := by
  obtain ⟨hvalid, heval, -, -⟩ := hmin
  exact shell_of_singleton_conjValid hR hRne hw (hvalid (x, s) (by simp)) heval

end SmallCancellationRouter
end GroupApproximation
