import GroupApproximation.Sofic.MatchingRunStructure

/-!
# Folding a stem breaks planarity

`MatchingStemContraction` shows the cactus stems cannot be **deleted**: a
matching in which no pair joins a diagram letter to a stem letter forces
`mk (t₁ ⋯ tₙ) = mk w`, the relators spelling `w` with no conjugation at all.

The remaining hope was the classical move — **fold** rather than delete.  The
`conj k` and `stem k` blocks are two readings of one conjugator, letterwise
inverse in opposite order, so they carry an identification `σ`, and a diagram
matching would be obtained by composing: from a relator letter follow the
matching; if it lands on a stem letter, cross `σ` to the other copy and follow
the matching again.  That is exactly what folding a stem does to a van Kampen
diagram.

**It does not work, and the obstruction is planarity.**  `σ` identifies a `conj`
letter, which sits *before* the relator block of its factor, with a `stem`
letter, which sits *after* it.  So the fold moves a matched endpoint **across the
relator letters of that factor**, and any pair with one end among them is crossed
by the composite.

## The witness

`exists_stem_fold_crossing` exhibits it.  The tree is the free-cancellation
matching of the cactus word of a genuine `C'(λ)` family — for every `λ > 0`, so
`C'(1/6)` in particular — and a genuine *minimal* expression.  Over `F(a, x₁,
x₂, x₃, z)` take

    `R = {x₁x₂x₃, az}`,   `e = [(a, x₁x₂x₃), (1, az)]`,   `w = a x₁x₂x₃ z`.

Every rotation and formal inverse of the two relators begins with a different
letter, so the family has **no nonempty piece at all** and satisfies `C'(λ)` for
every positive `λ`.  The expression is minimal: `|w| = 5` is not `|r| + 2|c|`
for any single symmetrized relator with a reduced conjugator, so the factor count
is two; and no two-factor expression has weight `0`, since no product of two
symmetrized relators spells `w`.  So this is not a degenerate configuration.

The cactus word is

```text
   a  x₁ x₂ x₃  a⁻¹ ‖ a  z  ‖ z⁻¹ x₃⁻¹ x₂⁻¹ x₁⁻¹ a⁻¹
   0   1  2  3    4    5  6     7    8    9    10   11
  conj ── rel 1 ──stem   rel 2   ────── boundary ──────
```

and its cancellation matching is `(0,11) (1,10) (2,9) (3,8) (4,5) (6,7)`, which
is `stemWitness`.  The stem identification is `σ : 0 ↔ 4`.

Folding it replaces the two pairs `(4,5)` and `(0,11)` by the single pair
`(5,11)` — relator 2's letter `a` comes to lie on the boundary, which is
geometrically right.  But the pair `(3,8)` survives untouched, and

    `3 < 5 < 8 < 11`

is exactly the configuration `MatchingPositions.pairIdx_noncrossing` forbids.
The folded matching is **not** non-crossing, so it is not a `DTree` and the whole
positional API is unavailable on it.

## What this rules out, and what it leaves

It rules out obtaining the diagram from the cactus by any operation that keeps
the letters and their order and only re-pairs them.  Deleting fails
(`MatchingStemContraction`), folding fails (here), and those are the only two
letter-level moves available.

What the witness also shows is *why* the diagram is still fine: after folding,
relator 2 meets the boundary at `w`-positions `0` and `4` — **two separated
arcs**.  That is the classical multi-arc phenomenon, and it is precisely the
configuration `MatchingRunStructure.run_contiguous` excludes for the cactus.  So
the two objects genuinely differ: contiguity is a property of the *cactus*
matching, not of the diagram, and `CurvatureAssembly.three_arc_shortfall`
describes the diagram after folding.

The consequence for the count is that it has to run on the cactus, with the
`conj` and `stem` blocks as vertices of the block graph, and produce a relator
block that is **stem-free** — no run to any `conj` or `stem` block — with at most
three relator neighbours.  A relator block with a stem run has a run that is a
common subword of a relator and a *conjugator*, which is not a piece, so both
`CurvatureAssembly.InteriorRun` and the seven-run bound fail for it.

Unconditional: this file asserts nothing about relators or small cancellation.
It exhibits a tree and three of its pairs.
-/

namespace GroupApproximation
namespace SmallCancellationRouter
namespace DTree

/-- **The witness.**  The free-cancellation matching of the cactus word
`a x₁x₂x₃ a⁻¹ · a z · invRev w` of the header, with the letters replaced by their
positions. -/
def stemWitness : DTree ℕ :=
  .wrap 0 11 (.wrap 1 10 (.wrap 2 9 (.wrap 3 8
    (.wrap 4 5 .nil (.wrap 6 7 .nil .nil)) .nil) .nil) .nil) .nil

theorem word_stemWitness :
    stemWitness.word = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by rfl

theorem pairIdx_stemWitness :
    stemWitness.pairIdx = [(0, 11), (1, 10), (2, 9), (3, 8), (4, 5), (6, 7)] := by
  rfl

/-- **Folding a stem breaks planarity.**

`c` and `s` are the two copies of one conjugator letter — `c` in the `conj`
block, `s` in the `stem` block — so the relator letters of that factor lie
strictly between them, and `p` is one of them.  The matching sends `c ↦ y`,
`s ↦ x` and `p ↦ q`.

Folding the stem identifies `c` with `s`, which replaces the two pairs `(c, y)`
and `(s, x)` by the single pair `(x, y)`.  The conclusion `p < x < q < y` is
exactly the configuration `pairIdx_noncrossing` forbids, so the folded pairing
`(x, y)` and `(p, q)` cross.

The tree is `stemWitness`, whose group-theoretic origin the header records: a
`C'(λ)` family for every `λ > 0`, and a minimal expression. -/
theorem exists_stem_fold_crossing :
    ∃ (T : DTree ℕ) (c p s x q y : ℕ),
      c < p ∧ p < s ∧
      (c, y) ∈ T.pairIdx ∧ (s, x) ∈ T.pairIdx ∧ (p, q) ∈ T.pairIdx ∧
      p < x ∧ x < q ∧ q < y := by
  refine ⟨stemWitness, 0, 3, 4, 5, 8, 11, by omega, by omega, ?_, ?_, ?_,
    by omega, by omega, by omega⟩ <;>
    · rw [pairIdx_stemWitness]
      simp

/-- **The folded pairing really is forbidden.**  `pairIdx_noncrossing`'s
conclusion, read at the two pairs the fold produces: it fails outright. -/
theorem not_noncrossing_of_fold {p q x y : ℕ}
    (h₁ : p < x) (h₂ : x < q) (h₃ : q < y) :
    ¬ ((p = x ∧ q = y) ∨ q < x ∨ y < p ∨ (p < x ∧ y < q) ∨ (x < p ∧ q < y)) := by
  omega

end DTree
end SmallCancellationRouter
end GroupApproximation
