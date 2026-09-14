# Support-three zero divisors: global constraints (lane hl-zero-divisor, 2026-09-13)

Target: `kaplansky-zero-divisor-conjecture`, case `|supp alpha| = 3`, aiming at a
global argument rather than per-graph search. Built on
`zero-divisor-support-vertex-cones-contain-positive-relations` and the
support-three theory artifact `research/artifacts/zds-three-support-theory-2026-09-13.md`.

## 1. Landed claims (ESTABLISHED, not independently reviewed, no novelty claimed)

| id | content |
|---|---|
| `zero-divisor-supports-have-no-quasimorphism-isolated-extremes` | any support size, any field: no homogeneous quasimorphism has a minimum or maximum on the support separated from the rest by more than `2D` |
| `support-three-zero-divisor-differences-bounded-quasimorphism` | support three: `|phi(a_i^-1 a_j)| <= 3D(phi)` for every homogeneous quasimorphism; differences are rationally null-homologous and have `scl <= 3/2` when in `[G,G]` |
| `f2-support-three-zero-divisor-lifts-without-balanced-odd-cycle` | an F_2 support-three zero divisor whose Kaplansky graph has no balanced odd cycle gives a zero divisor `1 + s x + t y` with the same supports over every algebraically closed field of characteristic `!= 2` |

Bavard duality was pinned from Calegari's *scl* (the PDF fetched on MSI into
`/scratch.global/sauer354/hl-zero-divisor/`, text extracted with ghostscript):
Theorem 2.70 and Definition 2.15.

## 2. Reformulations used (F_2, `alpha = 1 + x + y`, `beta = 1_B`, `|B| = n`)

- **Even sets.** `alpha beta = 0` iff `B` meets every right triangle
  `{g, x^-1 g, y^-1 g}` in `0` or `2` points. Equivalently every `b in B` has
  exactly one point of each pair `{x^-1 b, y^-1 b}`, `{x b, y^-1 x b}`,
  `{y b, x^-1 y b}` in `B`. So the induced subgraph of `B` in the 6-regular
  Cayley graph for `{x, y, x^-1 y}` is cubic, and it is the Kaplansky graph.
- **Three functional graphs.** With `X, Y, Z` the partial maps `b -> xb`,
  `b -> yb`, `b -> y^-1 x b` restricted to `B`:
  `ran X ⊔ ran Y = dom X ⊔ dom Z = dom Y ⊔ ran Z = B`, all of size `n/2`.
  Hence `X ∪ Y` has in-degree exactly one, `X ∪ Z` and `Y ∪ Z^-1` have out-degree
  exactly one. Each component of each graph is unicyclic, and the cycles are the
  positive relations of the vertex-cone node.
- **Integral form.** `(1 + x + y) 1_B = 2 * 1_S` in `Z[G]` with `|S| = 3n/2`.

## 3. Attempts at a global contradiction

1. **Isoperimetry / spectrum: dead as a general method.** The even-set structure
   gives `<Delta 1_B, 1_B> = 3n` for the adjacency `Delta` of the 6-regular
   Cayley graph (`{x, y, x^-1 y}^(+-1)`), and `<Delta_2 1_B, 1_B> = 2n` for the
   4-regular one (`{x, y}^(+-1)`). So a counterexample needs `||Delta|| >= 3` and
   `||Delta_2|| >= 2`, i.e. random-walk spectral radius at least `1/2` for both
   generating sets. For the free group on `x, y` the 4-regular value is
   `2 sqrt 3 > 2`, so spectral bounds exclude nothing there. Only the
   combinatorial forest bound (`|∂B| >= 2n + 2`) kills trees, which orderability
   already covers.
2. **Quasimorphisms: landed, bounded, no amplification found.** The bound
   `|phi| <= 3D` on the differences is a genuine sieve. It does not force
   `phi = 0`:
   - left-multiplying `alpha` by `gamma` only enlarges the difference sets and
     weakens the constraints;
   - there is no support-three zero divisor with `x^m, y^m` to amplify through
     powers;
   - evaluating along the unicyclic functional graphs reproduces the same
     identities.
   What would finish: forcing `phi(x) = 0` for every homogeneous quasimorphism.
   Then in torsion-free hosts where every nontrivial element has positive scl
   (for example torsion-free hyperbolic groups, by Calegari--Fujiwara; not
   re-read here) support three would be settled. That is Steenbock's question
   for Rips--Segev groups at support three.
3. **Characteristic-zero lift: landed, conditional.** If the Kaplansky graph
   has no balanced odd cycle, an F_2 counterexample lifts to characteristic `0`,
   where Strong-Atiyah hosts are domains. The twist by a character of `G`
   (`r_g = chi(g)`) only covers bipartite graphs; the exponent-sum character of
   the free group covers the larger class landed.

## 4. Exact gap

- **General hosts.** A global argument that turns the three unicyclic
  functional graphs, plus torsion-freeness, into a contradiction. Local cycle
  relations stop excluding at length 5 (see the support-three theory artifact).
- **Amplification target.** Show that a support-three zero divisor forces
  `phi(x) = phi(y) = 0` for all homogeneous quasimorphisms, improving the landed
  `3D` bound to `0`. That would settle support three in every torsion-free host
  with positive scl on nontrivial elements.
- **Search candidate (not run).** For hosts where `C[G]` is known to be a
  domain, extend the per-graph sieve of the zero-divisor search with the
  balanced-odd-cycle requirement of the lift claim. For hyperbolic hosts, add
  Brooks-quasimorphism evaluations of `x`, `y`, `x^-1 y` against `3D`.
