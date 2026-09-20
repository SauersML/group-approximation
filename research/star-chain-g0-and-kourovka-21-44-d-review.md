---
rg: 2
id: star-chain-g0-and-kourovka-21-44-d-review
kind: claim
title: Referee review of 445210c1f5 (lemma G0, star chains in the H_31 complex) and 75f2516f86 (Kourovka 21.44 Proposition D) — G0 FAILS as stated (at the C-type apex of an A–B edge of the path the link set is not π-convex), the node does not overclaim (G); Proposition D (density of the A_5 Fabrykowski–Gupta analogue H) PASSES, and the corrected sentence (no finitely generated dense subgroups of iterated wreath products of Z/p) is correct
distinct_from:
  star-chains-along-fixed-trees-are-gallery-convex: lane node under review (lemma G0 added in 445210c1f5).
  kourovka-21-44-spinal-groups-over-a5-dense-regime: lane node under review (Proposition D and the corrected sentence added in 75f2516f86).
---

**ESTABLISHED (referee bh-ref-d, 2026-09-19).** No priority claimed.

## 1. Lemma G0 (`star-chains-along-fixed-trees-are-gallery-convex`, 445210c1f5): FAIL as stated

**No overclaim of (G).** (G) stays **OPEN** in the node. G0 is explicitly "CAT(0)-convexity. It does
**not** give (G)", and the commit title says the same.

**What is right.**
- Local convexity of a subcomplex at a vertex is π-convexity of its link.
- Local-to-global for closed, connected, locally convex subsets of CAT(0) spaces is standard.
- The one-vertex case holds. At an outer vertex `u` adjacent to a single vertex `w` of `ρ`, the link set
  is the closed star of `(uw)`, with `t, t′ ≤ α_u ≤ π/2`. So `t + t′ ≤ π`, and girth × angle = 2π makes
  it π-convex.
- At interior points of outer edges `U_ρ` may occupy several half-planes, not one, because edges
  branch. That union is still locally convex.

**The two-vertex case fails at `C`-type apexes.**
- The claimed bound needs `t + ε + t′ ≤ π`, where `ε = α_u` is the link edge between `a = (uw_i)` and
  `b = (uw_(i+1))`. This holds when `u` has type `A` (`3π/5`) or `B` (`3π/4`). It fails when `u` has type
  `C`, since `ε = π/2` gives up to `3π/2`.
- `u` has type `C` exactly when the edge `w_i w_(i+1)` of `ρ` is an `A–B` edge: each triangle has one
  vertex of each type.
- **Counterexample.** `L_u = K_(5,5)`, with `a` and `b` on opposite sides.
  - Take `c ≠ b` adjacent to `a`, and `d ≠ a` adjacent to `b`, with the far endpoints of `uc` and `ud`
    not on `ρ`. At least 4 − (number of other `ρ`-neighbours of `u`) choices exist on each side.
  - Then `c` and `d` lie on opposite sides, so `cd` is a link edge of length `π/2`, and `d(c, d) = π/2`.
  - The link edge `cd` is the triangle `(u, x_c, x_d)`, which contains no vertex of `ρ` and so is not in
    `U_ρ`.
  - So `Lk(u, U_ρ)` is not π-convex. Points near `u` on the edges `ux_c` and `ux_d` are joined by a
    geodesic that leaves `U_ρ`, so **`U_ρ` is not locally convex at `u`**.
- **Scope.** Rays of `Fix(a)` alternate `A`-type vertices with `B`- or `C`-type ones, so this occurs
  whenever the chain has a `B`-type vertex.

**Cases not treated.**
- `u` adjacent to two consecutive vertices of `ρ` without the triangle `(u, w_i, w_(i+1))`.
- `u` adjacent to non-consecutive vertices, or to three or more.

Geodesicity of `ρ` has to exclude these, or they have to be handled.

**Repair.**
- Restrict G0 to chains with no `A–B` edges, i.e. alternating `A` and `C`, and prove that the
  untreated adjacency configurations do not occur.
- For `A–B` edges, enlarge `U_ρ` by the stars of the `C`-type apexes, or by the triangles `(u, x_c, x_d)`,
  and recheck.

Since G0 feeds nothing proved, only the "Checks and partial steps" record changes.

## 2. Proposition D (`kourovka-21-44-spinal-groups-over-a5-dense-regime`, 75f2516f86): PASS

**Problem text.** Checked verbatim against the notebook's LaTeX source (arXiv 1401.0300, e-print
`21tkt.tex`, 21st issue):

> "Let `W_n = A_5 ≀ ⋯ ≀ A_5` be the n-times iterated permutational wreath product of `A_5` in its natural
> action (so `W_n` acts on `5^n` points), and let `W` be the inverse limit (infinite iterated wreath
> product of `A_5`). Does `W` contain a finitely generated dense subgroup of subexponential growth?"
> (S. Eberhard)

This matches the node's statement, so its "source caveat" can be removed.

**Setup.**
- `s ↦ d_s` is an injective homomorphism, by uniqueness of solutions of `x = (st, 1, 1, 1, x)`.
- `H ≤ P`: the pair `((s,s)_ω, (s,s)_(σω))` solves the same two-step recursion as `(d_s, d_s)`, and
  that solution is unique.
- Every kernel is trivial, so no letter of `H` ever vanishes.

**Density: correct.**
- `n = 1, 2`: conjugates of `d_s` act on level 2 as `s` in any single coordinate.
- Induction step, `n ≥ 3`:
  - The coordinate-5 projection of `ψ(St_H(1))` contains `d_s` and, through a conjugate, the rooted `s`,
    so it is `H`. Hence `L_5 ⊴ H`.
  - `[d_s, d_t^h] = (1, 1, 1, 1, d_([s,t]))` for `h = (1 2 3)`. Since `A_5` is perfect, `D ⊆ L_5`.
  - `π_(n−1)(d_u) ∈ St(1) ∖ St(2)` for `n − 1 ≥ 2`. By induction and Proposition N, `π_(n−1)(L_5)`,
    which is normal in `W_(n−1)`, contains `St_(W_(n−1))(1)`.
  - Rooted conjugation spreads this to every coordinate. The level-2 case gives the `A_5^5` quotient.
    So `π_(n−1)^(×5) ψ(St_H(1)) = W_(n−1)^5`, and `π_n(H) = W_n`.
- The node is right that the commutator with a rooted conjugate replaces the vanishing letter.
- `H` is 4-generated.
- The growth consequences are the standard subgroup monotonicity.
- "Minimal test object" is informal.

**The corrected sentence: correct.**
- For a transitive permutational wreath product, `(A ≀_X B)^ab = A^ab × B^ab`. So the iterated wreath
  product of `m` copies of `Z/p` has abelianization `(Z/p)^m`.
- A dense `Γ` surjects onto every level quotient, so onto `(Z/p)^m` for every `m`. For `d`-generated `Γ`
  this is impossible once `m > d`, since `Γ^ab/p` has rank at most `d`.
- The argument works for any vertex group with a nontrivial abelian quotient. So 21.44 genuinely needs a
  perfect vertex group, as the node now says.

**Priority lead** (not checked). Segal, "The finite images of finitely generated groups" (Proc. LMS,
2001), builds finitely generated dense subgroups of iterated wreath products of perfect transitive groups
from a rooted group and directed elements. The density of an `H` of exactly this form may already be
there. Credit it if so. The growth question is untouched either way.
