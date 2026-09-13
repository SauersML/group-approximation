# Phases in the rank metric and in Hilbert--Schmidt: an exact theorem and the remaining curvature problem

Lane `ex-q34-collapse`, 2026-09-12.  Continues
`ex-q34-frame-extraction-2026-09-12.md` (soft kernels) and
`ex-q34-imprimitivity-witness-2026-09-12.md` (finitary forms).  Theorem R is
proved in full here, unreviewed by an independent verifier.  Section 3 is
open analysis.

## 0. Summary

Monomial models are permutations carrying phases.  How much damage can the
phases do?

- **Rank metric (Theorem R, established).**  Over *every* field, a group with
  linear sofic approximations by monomial matrices is sofic, and the
  separation constants are kept.  The phases never obstruct.  This extends
  `monomial-rank-models-are-hamming-models`, which covers finite fields, to all
  fields, including `C`.
- **Hilbert--Schmidt metric.**  The phases can separate at most an abelian
  normal subgroup (`block-monomial-hs-models-sofic-mod-amenable-soft-kernel`),
  and for Q3.4 as a whole they never obstruct
  (`hyperlinear-implies-sofic-via-frame-extraction`).  Whether every
  monomially hyperlinear group is sofic is open.  It is the claim
  `monomially-hyperlinear-groups-are-sofic`.  Section 3 isolates its analytic
  core: flatten a `U(1)`-connection with HS-small curvature on a finite
  Schreier 2-complex.

The difference between the two metrics is one sentence.  The rank metric sees
an exact phase disagreement on a column, while HS sees only its size.  So in
the rank metric the relators hold *exactly* on most columns, and an exact
multiplicative system can be rounded to roots of unity by torsion density.

## 1. Rank distance between monomial matrices over any field

Let `K` be a field, `Mon_N(K)` the monomial matrices, `A e_i = d_i e_(sigma(i))`,
`B e_i = d'_i e_(sigma'(i))`, and `Q = {i : A e_i != B e_i}`.

**Lemma 1.**  `|Q|/2 <= rank(A - B) <= |Q|`.

*Proof.*  The upper bound counts nonzero columns.  For the lower bound, each
column `i in Q` is supported on `{sigma(i), sigma'(i)}`.  Form the multigraph
on `[N]` with one edge (possibly a loop) per `i in Q`.  A vertex `v` is
`sigma(i)` for at most one `i` and `sigma'(i')` for at most one `i'`, so the
degrees are `<= 2`.  The components are loops, paths and cycles, with
pairwise disjoint supports.  A loop contributes rank `1`.  A path with `L`
edges contributes rank `L`, by triangularity along the path.  A cycle with
`L >= 2` edges contributes rank `>= L - 1 >= L/2`.  Ranks of disjointly
supported blocks add.  ∎

So normalized rank distance on monomials is the *column-Hamming distance*
`d_col(A, B) = |Q|/N` up to a factor `2`.  It is bi-invariant, and it counts a
column as different whenever the phase differs at all.

## 2. Theorem R

**Theorem R.**  Let `G` be countable.  Suppose for every finite `E ⊆ G` and
`eps > 0` there are `N` and `phi : E -> GL_N(K)` with
`rank(phi(g)phi(h) - phi(gh))/N <= eps` for `g, h, gh in E`,
`rank(phi(e) - 1)/N <= eps`, and `rank(phi(g) - 1)/N >= delta` for
`g in E \ {e}`, with every `phi(g)` within rank `eps N` of `Mon_N(K)`.  Here
`delta > 0` is fixed.  Then `G` is sofic.  More precisely, every window has
sofic approximations with separation `>= delta - O(eps)` and at most doubled
relator defects.

*Proof.*  Fix a finite generating window `S_0`, a finite set `R_0` of relators
(words in `S_0` trivial in `G`) and a finite set `E_0` of test words
(nontrivial in `G`), all inside the window.  Replace each `phi(s)`, `s in S_0`,
by a nearby monomial `M_s = (d_s; sigma_s)` and extend to words by products.
Rank is subadditive, so `rank(M_r - 1)/N <= C eps` for `r in R_0` and
`rank(M_w - 1)/N >= delta - C eps` for `w in E_0`, with `C` depending on the
window.  For a word `u` and column `x`, write `M_u e_x = hol_u(x) e_(sigma_u(x))`.
Here `hol_u(x) in K^x` is the product of generator phases along the path of `x`.

*Good and active columns.*  Put
`Good = {(r, x) : sigma_r(x) = x, hol_r(x) = 1}` and
`Act = {(w, x) : M_w e_x != e_x}`.  By Lemma 1, for each `r` the columns with
`(r, x)` not good have density `<= 2 C eps`, and for each `w` the active
columns have density `>= delta - C eps`.

*Step 1: move the phases to the circle.*  The finitely many entries
`d_s(x)` generate a finitely generated subgroup `Λ <= K^x`.  Its torsion is
cyclic (roots of unity in a field), so `Λ ≅ Z^a × Z/q`.  Let `Y ⊆ Λ` be the
finite set of values `hol_w(x) != 1` over `w in E_0` and columns `x` with
`sigma_w(x) = x`.  A character `psi = (theta, chi) in T^a × Hom(Z/q, U(1))`
with `chi` faithful has `psi(lambda) = 1` for a given `lambda in Y` only on a
proper closed subset of codimension `>= 1` in `theta`.  If `lambda` has
infinite order this is a codimension-1 condition.  If `lambda` is torsion,
`psi(lambda) = chi(t) != 1`.  So a generic `theta` gives `psi(lambda) != 1` on all
of `Y`.  Put `c_s(x) = psi(d_s(x)) in U(1)`.  Holonomies transform by the
homomorphism `psi`, so every good pair stays good, and every active pair
stays active.

*Step 2: torsion rounding.*  Let `Z ⊆ U(1)^(S_0 × [N])` be the closed subgroup
defined by the characters `c |-> hol^c_r(x)` for `(r, x) in Good`.  These are
characters because the paths depend only on the permutations.  `c in Z`, and
torsion points are dense in every closed subgroup of a torus.  The finitely
many conditions `hol^c_w(x) != 1` for active pairs with `sigma_w(x) = x` are
open.  So some torsion `c' in Z` of some order `m` keeps them all, and its values
lie in `mu_m`.

*Step 3: the skew product.*  Write `c'_s(x) = exp(2 pi i a_s(x)/m)` and let `s`
act on `[N] × Z/m` by `(x, j) |-> (sigma_s(x), j + a_s(x))`.  Words act by the
cocycle products, consistently with `hol^(c')`.
- Relators: for `(r, x) in Good`, `sigma_r(x) = x` and `hol^(c')_r(x) = 1`, so
  `r` fixes every `(x, j)`.  Relator Hamming defect `<= 2 C eps`.
- Test words: if `(x, j)` is fixed by `w`, then `sigma_w(x) = x` and
  `hol^(c')_w(x) = 1`, so `(w, x)` was not active.  So fixed densities are
  `<= 1 - delta + C eps`.
So the window has a finite almost-action with separation
`>= delta - C eps`.  Since the window and `eps` are arbitrary, `G` is sofic
(uniform weak separation suffices, by the Elek--Szabó amplification).  ∎

*Model tests.*  Over `F_2` monomials are permutation matrices and
Theorem R is trivial.  Over `C`, a diagonal model of `Z` by characters is a
rank model whose skew product is a cyclic rotation, sofic as expected.  A
nonsofic group has no monomial rank model over any field.  For the binary
Leavitt units this fences every permutation-type construction toward
`binary-leavitt-unit-group-is-f2-linear-sofic` and every complex-linear
analogue, whatever the phases.

*What is used and what is not.*  No gap on the labels, and no finiteness of
the field.  Only exactness of phase agreement on columns, which the rank
metric supplies and HS does not.

## 3. The Hilbert--Schmidt problem: curvature

Let `rho : G -> prod_omega U(1) wr S_n` be regular.  By the soft-kernel theorem
the permutation kernel `A` is abelian and normal, and `G/A` is sofic.  If
`A = 1`, `G` is sofic.  Otherwise a finite-stage model is an exact
free-group monomial representation `(c_s; sigma_s)` whose relator holonomies
satisfy `hol_r(x) ≈ 1` only in `L^2` over the columns with `sigma_r(x) = x`.

**Reduction.**  By Steps 1 to 3, it is enough to change the phases by `o(1)` in
`L^2` and discard `o(n)` columns so that the relator holonomies become
*exactly* `1` on the remaining good columns, keeping the trace separation.  So
`monomially-hyperlinear-groups-are-sofic` would follow from a stability
theorem for `U(1)`-local systems on finite Schreier 2-complexes.

**Linearized form.**  Write `c = exp(2 pi i theta)`, with curvature
`F = d theta - round(d theta)` on the good relator cells, `|F|` small on average.
One needs a real 1-cochain `B` with `d B = F` on all but `o(n)` cells and
`||B||_(ℓ^2, normalized) = o(1)`.  Minimal solutions satisfy
`||B||^2 <= <F, (d d^*)^+ F>`, provided `F ⊥ Z_2` (the 2-cycles).

- *Small 2-cycles are harmless.*  On a 2-cycle made of `<= L` cells, the flux
  is an integer of modulus `<= L max|F| < 1`, hence `0`.
- *Large 2-cycles carry integer flux.*  This is a Chern-class-type
  obstruction.  Deleting one cell per large cycle removes it at density cost
  `1/area`.
- *Amenable directions (band argument).*  On `Z^2`-like complexes, cut into
  bands of height `h`, deleting boundary cells (density `1/h`) and solving
  inside bands with `|B| <= h |F|`.  The cost is `(h|F|)^2 + 1/h`, which is
  `O(|F|^(2/3))` at `h ~ |F|^(-2/3)`.
- *Expanding directions (electrical flow).*  With a spectral gap `lambda` of
  the up-Laplacian on 2-cochains, `||B|| <= ||F||/sqrt(lambda)`.
- *General complexes.*  Mixed geometry, low-frequency curvature modes and
  large 2-cycles together are not handled by any of the above.  This is the
  open core.

**Model test on the Kun--Thom wreath.**  `W = (Z/2) wr_(G/Gamma) G` is
abelian-by-sofic and nonsofic (`kun-thom-nonsofic-wreath`, a preprint import).
So the claim predicts that `W` has no regular monomial HS model.  When all
lamps lie in the soft kernel, this already holds by
`block-monomial-coordinate-collapse`.  A model whose soft kernel is a proper
`G`-submodule of the lamp module is not covered by any current node.  It is
either a counterexample to the claim, which would give a hyperlinear nonsofic
group, or it is excluded by a Kun--Thom argument for quotient modules.

**Why the claim does not matter for Q3.4.**  Passing to `H * Z` removes every
abelian normal subgroup, so Theorem 4 of the frame-extraction artifact needs
no curvature control.  The claim is a group-by-group statement about which
abelian-by-sofic groups can be monomially hyperlinear.  Its failure would
itself be a separation.
