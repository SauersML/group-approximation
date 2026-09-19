import GroupApproximation.GGT.HullSCRelatorSeparation2Statement

/-!
# Quasi-geodesicity of the alternating relator, reduced to a count

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, §6; Osin,
*Acylindrically hyperbolic groups*, Lemma 4.2.

Over one subgroup the relator is not quasi-geodesic at all
(`HullSC.not_quasiGeodesic_relatorWord`): its run spans a single edge.  Over two
the obstruction is gone, since each block letter is its own component
(`HullSC.isComp_relatorWord₂`), and what has to be shown instead is the positive
statement.  This module reduces it to one count and proves the rest.

## The reduction

The relator is `|p|` base letters followed by `|ms|` block letters, so a range
`[i, j)` of positions contains `j - max i |p|` block letters, and that is at
least `(j - i) - |p|`.  If the geodesic between the two endpoints has to
*account* for those block letters up to a constant --

  `j - max i |p| ≤ d(vertexᵢ, vertexⱼ) + c`

-- then `(j - i) - (|p| + c) ≤ d`, which is the quasi-geodesic lower bound with
`mu = 1` and `b = |p| + c`.  That is `quasiGeodesic_relatorWord₂_of_blockCount`,
and it is arithmetic.

## What the count is, and why it is the geometric part

`hcount` is the only input.  It is the standard consequence of the
isolated-component bound: each block letter of the range is a *deep* component
of the path, so it cannot be isolated in the polygon formed by the subword and a
geodesic between its endpoints -- Osin's Lemma 4.2 would bound its `d̂` by a
constant -- so it is connected to a component of the geodesic; the geodesic has
at most `d` components; and the assignment is injective because two distinct
block letters of the alternating relator are not connected to each other, which
is what the exponent design and the spacing of
`HullSC.exists_long_base_spelling` are for.  So the count is `≤ d + c` with `c`
depending on `E` alone.

Three things are worth separating in that sentence, because only the first is
geometric: the non-isolation of a deep component (Lemma 4.2, osin-ah4's
polygon leaf), the bound on the number of components of a geodesic (elementary,
one per letter), and the injectivity (the design, on this side).  A version of
`hcount` that names the geodesic would let the last two be proved here; as
stated it packages all three, which is the weakest thing this reduction can
consume.

## What is not yet here

The same statement for the members of the symmetrized closure, which is what a
polygon side actually is.  It differs only in that the base letters of a
rotation are no longer an initial segment, so `j - max i |p|` becomes a count;
the count is still `|p|`, because rotation permutes the letters and formal
inversion carries base letters to base letters.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

section QuasiGeodesic

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}

omit [Group G] in
/-- **A range of the relator contains at least `(j - i) - |p|` block letters.**
The base letters are an initial segment of length `|p|`, so the block letters of
`[i, j)` are the positions from `max i |p|` up to `j`. -/
theorem blockCount_ge (p : List G) (i j : ℕ) (hij : i ≤ j) :
    j - i ≤ (j - max i p.length) + p.length := by
  omega

/-- **The alternating relator is `(1, |p| + c)`-quasi-geodesic, once the block
letters of a range are accounted for by the distance between its endpoints.**

The hypothesis is the count; everything else is arithmetic.  Note where the
constants come from: `mu` is `1`, and `b` is `|p| + c` with `c` depending only
on `E` -- so `b` is fixed by the spacing requirement and the geometry before the
relator is chosen, and in particular does not grow with `ms`.  That is what
`HullSC.not_quasiGeodesic_relatorWord` shows fails over one subgroup, where the
defect grows with the exponent list. -/
theorem quasiGeodesic_relatorWord₂_of_blockCount (E : HypEmbeddedCore₂ A N)
    (p : List G) (ms : List ℕ) (c : ℕ)
    (hcount : ∀ i j : ℕ, i ≤ j →
      j ≤ (relatorWord₂ p (E.lox false) (E.lox true) ms).length →
        j - max i p.length ≤
          wordDist E.rel.alphabet.carrier
            (GGT.OsinComponents.vertex 1
              (relatorWord₂ p (E.lox false) (E.lox true) ms) i)
            (GGT.OsinComponents.vertex 1
              (relatorWord₂ p (E.lox false) (E.lox true) ms) j) + c) :
    ∀ i j : ℕ, i ≤ j →
      j ≤ (relatorWord₂ p (E.lox false) (E.lox true) ms).length →
        ((j - i : ℕ) : ℝ) / 1 - ((p.length + c : ℕ) : ℝ) ≤
          (wordDist E.rel.alphabet.carrier
            (GGT.OsinComponents.vertex 1
              (relatorWord₂ p (E.lox false) (E.lox true) ms) i)
            (GGT.OsinComponents.vertex 1
              (relatorWord₂ p (E.lox false) (E.lox true) ms) j) : ℝ) := by
  intro i j hij hj
  have h1 := hcount i j hij hj
  have h2 : j - i ≤
      wordDist E.rel.alphabet.carrier
        (GGT.OsinComponents.vertex 1
          (relatorWord₂ p (E.lox false) (E.lox true) ms) i)
        (GGT.OsinComponents.vertex 1
          (relatorWord₂ p (E.lox false) (E.lox true) ms) j) + c + p.length := by
    omega
  have h3 : ((j - i : ℕ) : ℝ) ≤
      ((wordDist E.rel.alphabet.carrier
        (GGT.OsinComponents.vertex 1
          (relatorWord₂ p (E.lox false) (E.lox true) ms) i)
        (GGT.OsinComponents.vertex 1
          (relatorWord₂ p (E.lox false) (E.lox true) ms) j) : ℕ) : ℝ)
        + (c : ℝ) + (p.length : ℝ) := by
    exact_mod_cast h2
  rw [div_one]
  push_cast
  linarith

end QuasiGeodesic

end HullSC
end GroupApproximation
