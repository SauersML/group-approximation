---
rg: 2
id: pointed-cube-categories-li-garside-proof
kind: route
title: Median joins and Niblo--Reeves normal cube paths give Li's Garside hypotheses for any free cocompact cubulation; in Z^2 the even-count subcategory has overlapping minimal common multiples
target: pointed-cube-categories-are-li-garside-categories
requires:
  - cubulated-groups-act-by-bisections-of-a-pointed-cube-category
---

**Sources.** Read in `src/kep/li-garside-II-2110.04505v2.tex`:
- the standing hypotheses of `intro:Gars` (l.596);
- Garside families and normality (l.990--1000);
- right cancellation up to `=^*` (l.950);
- condition (F) (l.1454);
- the word-problem corollary (l.608, l.1564).

**Standard cube-complex facts used, not re-read at source.**
- Pairwise crossing hyperplanes adjacent to `y` span a cube at `y` (flag), and cubes are
  convex.
- The order ideals of `(H(y,z), <)` are the sets `H(y,w)` with `w ∈ I(y,z)`. Here
  `H < H'` means `H ∩ H' = ∅` and `H` separates `y` from `H'`.
- `H ∈ H(y,z)` is adjacent to `y` iff it is `<`-minimal (Niblo--Reeves).

None of these uses specialness, so the argument covers self-crossing and
inter-osculating hyperplane orbits.

**Setup.** Fix a representative `(y, κ)` of each object `v`. Freeness makes morphisms
from `v` correspond to vertices `z` with `H(y,z) ∩ hyp(κ) = ∅`, and `a ≼ b` means
`z_a ∈ I(y, z_b)`.

**Item 1.**
- **Cancellation.** Left cancellation is item 3 of the parent. For right cancellation,
  write `ax = bx` with `x`'s representative fixed. Then both sides are triples ending at
  the same vertex with `G`-equivalent starts, so freeness gives `a = b`. Units are
  identities, so (F) holds and `=^*` is equality.
- **Lcms.** Suppose `z_a` and `z_b` have a common upper bound `w`. Flip the ultrafilter of
  `y` on `H(y,z_a) ∪ H(y,z_b)`.
  - Two flipped halfspaces meet at `w`.
  - A flipped `H` and an unflipped `H'` meet at `z_a` or `z_b`.
  - Only finitely many halfspaces are flipped (DCC).

  So this is a vertex `j` with `H(y,j) = H(y,z_a) ∪ H(y,z_b)`, in the cone of `v`: the lcm.
  Hence `aC ∩ bC ∈ {∅, lcm(a,b) C}`, which gives finitely aligned with disjoint mcms.
- **Right Noetherian.** `|H|` drops strictly along proper right divisors.
- **Garside family `S`.**
  - *Closed under right comultiples.* If `r, s ≼ a`, the hyperplanes of `r` and `s` lie in
    `Max(z_a, y)`, which spans a cube `t` with `r, s ≼ t ≼ a` (item 1 of the parent).
  - *`S^♯` closed under right divisors.* Cubes are convex, so right divisors of cube
    morphisms are faces.
  - *Normal forms.* The Niblo--Reeves path takes `s_k` spanned by `Max(z, y_k)`. For
    `r ∈ S` with `r ≼ s_k s_{k+1}`, the hyperplanes of `r` are adjacent to `y_k` and lie in
    `H(y_k, z)`, so `r ≼ s_k`. That is Li's normality. Local finiteness of `X` makes `S`
    locally finite.
- **Heights.** Adjacent means minimal, so `s_k` consists of the level-`k` hyperplanes and
  `‖a‖` is the height of `(H(y,z_a), <)`.
  - A product of `m` cubes has height at most `m`, since each cube is an antichain.
  - Left divisors correspond to order ideals, so they have height at most `‖a‖`.
  - So `(S^{≤L})^♯` is the set of morphisms of height at most `L`, and it is closed under
    left divisors.
- **Word problem.** `C_X` is computable from the finite complex `X/G` and the `=^*`-map is
  trivial, so Li's word-problem corollary applies.

**Item 2 (grading-free power).** Take `X = R²` with its square tiling and `G = Z²`. The
morphisms from the base object `[(o, {o})]` are the lattice points, ordered coordinatewise
within each quadrant; take the first quadrant.
- **The subcategory.** Let `C^{(2)}` consist of the morphisms with even hyperplane count
  `|x| + |y|`. It is closed under composition and has the same infinite paths, since
  boundary points are limits of even prefixes.
- **The counterexample.** `(1,1)` and `(2,0)` lie in `C^{(2)}`. Their common right
  multiples in `C^{(2)}` form `{x ≥ 2, y ≥ 1, x + y even}`, whose minimal elements are
  `(3,1)` and `(2,2)`.
- **Why no disjoint decomposition exists.** Both minimal elements must generate
  principal ideals in any decomposition of that set into principal ideals, and those two
  ideals share `(3,3)`.

So `C^{(2)}` does not have disjoint mcms, and Li's `intro:Gars` does not apply to it. The
same happens for every `M ≥ 2` and every complex containing a square.

## Lesson for general BH

Li's Garside hypotheses are "median lattice" hypotheses. Any geodesic combing with
conditional joins satisfies them, whatever the hyperplane combinatorics. They break as
soon as one coarsens time without a grading. So power operations for higher-rank hosts
must be built from the combinatorics of the hyperplane poset, since arithmetic on lengths
does not preserve the joins.
