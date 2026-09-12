# Toms--Winter, disprove side: where a Bauer-simplex Gamma failure can live (2026-09-12)

Lane `toms-winter-bundle-hunter`, a helper for `toms-winter`.  The target is a
unital simple separable nuclear non-elementary C*-algebra with strict
comparison and without uniform property Gamma
(`gamma-failure-invisible-to-projection-comparison`).  Nothing here produces
such an algebra.  This artifact records verified sources, one short derivation
localizing Gamma failure on Bauer simplices, and the mechanisms tested.

## Sources and what was read

PDFs were fetched and converted to text on MSI
(`/projects/standard/hsiehph/sauer354/lit/tw-bundle-hunter/`, ghostscript
`txtwrite`).  Only the statements quoted were read.

- N. Ozawa, *Dixmier approximation and symmetric amenability for C*-algebras*,
  arXiv:1304.3523 (J. Math. Sci. Univ. Tokyo 20 (2013) 349--374).
  - Theorem 15: "Let M be a strictly separable continuous W*-bundle over K such
    that π_λ(M) ≅ R for every λ ∈ K. Then, the following are equivalent.
    (i) M ≅ C_σ(K,R) as a continuous W*-bundle. (ii) There is a sequence (p_n)_n
    in M such that 0 ≤ p_n ≤ 1, ‖p_n − p_n²‖_{2,u} → 0, ‖E(p_n) − 1/2‖ → 0, and
    ‖[p_n,a]‖_{2,u} → 0 for all a ∈ M. (iii) For every k, there is an
    approximately central approximately multiplicative embedding of M_k into M."
  - Corollary 16: "Let M be a strictly separable continuous W*-bundle over K. If
    every fiber π_λ(M) is isomorphic to R and K has finite covering dimension,
    then M ≅ C_σ(K,R) as a continuous W*-bundle."  Just before it: "It is
    unclear whether the finite-dimensionality assumption is essential."
- S. Evington, U. Pennig, *Locally trivial W*-bundles*, arXiv:1601.05964v2
  (Internat. J. Math. 2016).
  - Definition 2.10: "We say that a W*-bundle M over X is locally trivial if
    every x ∈ X has a closed neighbourhood Y such that M_Y is isomorphic to a
    trivial bundle over Y."  Restrictions `M_Y` to closed subsets are defined in
    Section 2 (Proposition 2.9), and the fibre maps at points of `Y` factor
    through the restriction map.
  - Theorem 4.10: "A locally trivial W*-bundle with all fibres isomorphic to the
    hyperfinite II_1 factor R is trivial."  The abstract: "There is no
    restriction on the covering dimension of X"; the proof uses Popa--Takesaki
    contractibility of Aut(R).
- J. Bosa, N. Brown, Y. Sato, A. Tikuisis, S. White, W. Winter, *Covering
  dimension of C*-algebras and 2-coloured classification*, arXiv:1506.03974.
  - Question 3.14: "Does there exist a nontrivial strictly-separable bundle M
    over a compact metrizable space K all of whose fibres are copies of R?"
    Triviality is known when K has finite covering dimension (Ozawa) and when
    M is the strict closure of a separable unital nuclear Z-stable algebra with
    Bauer trace simplex.
- J. Castillejos, S. Evington, A. Tikuisis, S. White, *Uniform property Gamma*,
  arXiv:1912.04207, introduction (text in
  `/projects/standard/hsiehph/sauer354/lit/toms-winter/`).  For Bauer `T(A)`,
  Question C is "is the W*-bundle obtained as the strict closure of A trivial?";
  by Ozawa's Theorem 15 triviality happens when the bundle has "an appropriate
  version of uniform property Γ (which in the case of bundles coming from strict
  closures of C*-algebras is precisely uniform property Γ for the C*-algebra)".
- K. Mommaerts, arXiv:2606.12134v1, introduction and Section 4.
  - Theorem A: the bundle over `N ∪ {∞}` with fibres `LF_∞`, sections in
    `C_σ(N ∪ {∞}, M_2(LF_∞))` with value at `∞` in the diagonal `LF_∞`, is not
    locally trivial.  The obstruction is failure of uniform w-spectral gap.
  - Remark 4.7: the same construction with `R` is trivial, and "if there exists
    a non-trivial W*-bundle with all fibres isomorphic to R, then the base space
    must have infinite covering dimension. The (non)-existence of such a bundle
    is not known."
  - Remark 4.8: no obstruction to local triviality other than the negation of
    uniform w-spectral gap is known.

## 1. Localization of nontriviality

**Setting.** `M` is a strictly separable continuous W*-bundle over a compact
metrizable `K` with every fibre isomorphic to `R`.  For `x ∈ K` say `M` is
*trivial near x* if some closed neighbourhood `Y` of `x` has `M_Y` trivial.  Put

```text
Z(M)   = { x in K : M is not trivial near x },
K_inf  = { x in K : no closed neighbourhood of x has finite covering dimension }.
```

**Proposition.**
1. `Z(M)` and `K_inf` are closed.
2. `M` is trivial if and only if `Z(M)` is empty.
3. `Z(M) ⊆ K_inf`.
4. `K_inf` is empty if and only if `K` has finite covering dimension.

So a nontrivial bundle is not locally trivial exactly on a nonempty closed set
of points at which the base is infinite-dimensional in every neighbourhood.
Corollary 16 is the case `K_inf = ∅`.  This sharpens Mommaerts's Remark 4.7,
which only asks the base to be infinite-dimensional.

**Proof.**
1. If `Y` is a closed neighbourhood of `x`, it is a closed neighbourhood of every
   point of its interior, so the complements of `Z(M)` and `K_inf` are open.
2. If `M ≅ C_σ(K,R)`, restriction of functions maps it into `C_σ(Y,R)`.  The
   unit ball of `R` with the 2-norm is a convex subset of a normed space, so by
   Dugundji's extension theorem every norm-bounded 2-norm-continuous function
   on the closed set `Y` extends to `K` with the same norm bound.  Hence the
   restriction of the trivial bundle to `Y` is the trivial bundle over `Y`,
   and `Z(M) = ∅`.  Conversely `Z(M) = ∅` is Definition 2.10 of local
   triviality, and Evington--Pennig Theorem 4.10 makes `M` trivial.
3. Let `x` have a closed neighbourhood `Y` with `dim Y < ∞`.  The restriction
   `M_Y` is a W*-bundle over `Y` whose fibres are the fibres of `M` at points of
   `Y`, hence copies of `R`.  The restriction map is contractive for the uniform
   2-norms, and it carries a countable strictly dense subset of `M` to a strictly
   dense subset of `M_Y`, so `M_Y` is strictly separable.  Ozawa's Corollary 16
   makes `M_Y` trivial, so `x ∉ Z(M)`.
4. If every point has a closed neighbourhood of finite dimension, finitely many
   interiors cover `K`, and the sum theorem for finitely many closed subsets of a
   metrizable space bounds `dim K` by the largest of them.  The converse is
   monotonicity of covering dimension on closed subsets.

**Step to check in review.**  Step 3 uses that the image of `M` in `M_Y` is
strictly dense.  The Evington--Pennig construction of `M_Y` before Proposition
2.9 is where this lives; it was read only at the level of the proof sketch.

## 2. Consequence for algebras with a Bauer trace simplex

Let `A` be unital, simple, separable, nuclear and non-elementary, with `T(A)` a
Bauer simplex, and `M` the strict closure of `A` over `K = ∂_e T(A)` (Ozawa,
Section 5).
- For extreme `τ`, `π_τ(A)''` is an injective finite factor.  It is not a matrix
  algebra, because a simple infinite-dimensional `A` has no finite-dimensional
  representation.  So it is `R` (Connes), and `M` satisfies the setting above.
- `A` has uniform property Gamma if and only if `M` is trivial (Ozawa Theorem 15
  (i)⟺(ii), with the CETW identification of (ii) with uniform Gamma of `A`).

**Corollary.** If `A` lacks uniform property Gamma, there is an extreme trace
`τ_0` such that for every closed neighbourhood `Y` of `τ_0` in `∂_e T(A)`, the
restricted completion `M_Y` admits no sequence as in Theorem 15 (ii), and `Y`
has infinite covering dimension.

With `uniform-gamma-algebras-satisfy-toms-winter`, every unital Toms--Winter
counterexample with a Bauer trace simplex has such a point, and its strict
closure answers BBSTWW Question 3.14 negatively.

## 3. Mechanisms tested

- **Cohomological invariants of the boundary: dead on Bauer simplices.**  A
  bundle glued from trivial pieces along `Aut(R)`-valued transition data is
  locally trivial, hence trivial (Evington--Pennig Theorem 4.10).  No
  characteristic class of `∂_e T(A)` built from the homotopy of `Aut(R)` can
  obstruct Gamma.  The obstruction must be failure of local triviality at points
  of `K_inf`, an analytic failure of uniform rates in Theorem 15 (ii).
- **Inclusion attachments over small bases: dead.**  Mommaerts's
  `M_2`-diagonal attachment with `R` fibres is trivial (Remark 4.7).  By the
  Proposition, any attachment whose non-local-triviality locus avoids points of
  infinite local dimension is trivial.
- **Uniform spectral gap: not available.**  Mommaerts's obstruction needs full
  fibres, and `R` has property Gamma.  Remark 4.8 records that no other
  obstruction to local triviality is known.
- **Villadsen- or Toms-type AH systems: dead at strict comparison.**
  `simple-ah-strict-comparison-is-z-stable` (Toms, arXiv:1102.0932) excludes
  every AH witness, and Toms's Gamma counterexample fails strict comparison
  (`toms-gamma-counterexample-fails-strict-comparison`).  A grep of the text of
  Toms arXiv:2606.12188 finds no statement on whether its trace simplex is Bauer.
  If it were, its strict closure would be a nontrivial `R`-fibre bundle and would
  answer Question 3.14; this was not checked.
- **Non-uniform Gamma rates, the owner's candidate.**  This is Theorem 15 (ii)
  itself, and the Proposition confines the degeneration of rates to
  neighbourhoods of points of `K_inf`.  The smallest base shape is the one-point
  compactification `K` of the disjoint union of the cubes `[0,1]^n`, n ≥ 1.
  Here `K_inf = {∞}`, so every nontrivial bundle over `K` is trivial over each
  cube and fails local triviality exactly at `∞`.  A witness of this shape needs
  the halving rate on the `n`-th cube to degenerate as `n → ∞`, while projection
  comparison in the tracial ultrapower holds.  No construction is known.
- **Non-Bauer trace simplices.**  There is no bundle picture and the Proposition
  does not apply.  The general form is CCEGSTW Question 1.5.
