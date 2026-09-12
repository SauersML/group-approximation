# Toms--Winter: rank density is the invariant a LIX-style counterexample must break (2026-09-11)

Lane `lix-toms-winter-2`.  This artifact carries the arguments behind:

- `ah-algebras-realize-ranks-approximately` (established, citation reading of
  Brown--Perera--Toms);
- `rank-density-and-strict-comparison-give-purity` (established, proof below);
- `ah-strict-comparison-z-stable-via-rank-density`, a second route into
  `simple-ah-strict-comparison-is-z-stable` that does not use Toms's
  arXiv:1102.0932 divisibility note;
- the negation root `stw27-strict-comparison-non-pure-algebra-exists` for part (1)
  of STW Problem XXVII, with routes from the K1-witness and to the XVIII
  negation root.

The companion lane `lix-toms-winter-1` landed the K1 region the same evening:

- `simple-ah-strict-comparison-is-k1-injective`;
- `stw59-lix-algebras-fail-strict-comparison`;
- `stw18-k1-witness-constraints`;
- the open witness `stw18-k1-witness-strict-comparison-not-k1-injective`.

See `research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md`.  Nothing
here duplicates those nodes.

## Sources and what was read

- N. P. Brown, F. Perera, A. S. Toms, *The Cuntz semigroup, the Elliott
  conjecture, and dimension functions on C*-algebras*, J. reine angew. Math.
  621 (2008), arXiv:math/0609182.  **Read in this lane from the arXiv PDF,
  pages 11--15**: Corollaries 4.5--4.7, Proposition 5.1, Lemma 5.2, Theorem
  5.3 with its complete proof, Lemma 5.4, Theorem 5.5.
- W. Winter, *Nuclear dimension and Z-stability of pure C*-algebras*, Invent.
  Math. 187 (2012), arXiv:1006.2731.  **Abstract read in this lane**: a
  separable simple nonelementary unital C*-algebra with locally finite nuclear
  dimension that is (m, m-bar)-pure absorbs Z.
- X. Fu, H. Lin, *Tracial oscillation zero and stable rank one*,
  arXiv:2112.14007.  **Abstract read in this lane**: for a separable simple
  C*-algebra with strict comparison, tracial approximate oscillation zero holds
  iff A has stable rank one and the canonical map Gamma is surjective.
- Lin's dichotomy for pure algebras, Rieffel's nonstable K1 theorem and
  Thiel's rank realization are **not re-read here**.  They are used only
  through the established Cairn claims `stw58-simple-pure-k1-bijective`,
  `strict-comparison-rank-surjectivity-forces-sr1` and
  `thiel-stable-rank-one-ranks-close-purity-with-comparison`.

## 0. Conventions

`A` is unital, simple, separable.  `T(A)` is its tracial state space and, for
`a in M_infty(A)_+`, `d_tau(a) = lim_n tau(a^(1/n))`.  For exact `A`,
Haagerup's theorem identifies quasitraces with traces.

- **Strict comparison.**  For `a, b in M_infty(A)_+`: if
  `d_tau(a) < d_tau(b)` for every `tau in T(A)`, then `a` is Cuntz subequivalent
  to `b`.
- **Rank density (RD).**  For every continuous strictly positive affine
  function `f` on `T(A)` and every `eta > 0` there is `y in M_infty(A)_+` with
  `|d_tau(y) - f(tau)| < eta` for all `tau in T(A)`.  RD is weaker than exact
  realization of ranks (STW XXIII) and weaker than surjectivity of the rank map.
- **Pure** (Winter).  `Cu(A)` is almost unperforated and almost divisible, the
  latter meaning: for `x in Cu(A)`, `k in N` and `x' << x` there is `y` with
  `k y <= x` and `x' <= (k+1) y`.  This is (0,0)-purity.

## 1. Every unital simple separable infinite-dimensional AH algebra has RD

This is a reading of Brown--Perera--Toms, not a new argument.

- Proposition 5.1: if `A_1 <= A_2 <= ...` have dense union in the simple `A`
  and `f` is continuous strictly positive affine on `T(A)`, then for each
  `eps > 0` there are `n` and `0 <= a in A_n` with `|f(tau) - tau(a)| < eps`.
- Lemma 5.2: if `B = p(C(X) tensor K)p` is homogeneous with `rank(p) = n` and
  `0 <= g <= 1` is continuous affine on `T(B)`, there is `a in M_infty(B)_+` with
  `0 <= g(tau) - d_tau(a) <= 1/n` on `T(B)`.  The element is
  `direct_sum_i f_i q` for a rank-one trivial projection `q` and bump functions
  `f_i` supported on `{g > i/n}`; no bundle structure of `p` is used.
- The first part of the proof of Theorem 5.3 combines these for an AH
  decomposition `A_i = direct_sum_j p_(i,j)(C(X_(i,j)) tensor K)p_(i,j)`.  It
  pulls `f` back to a stage, compresses so that `1/min_j rank(p_(i,j)) << eps`
  (simplicity and infinite dimensionality), applies Lemma 5.2 summand by
  summand, and pushes forward.  The result is `a in A_+` with
  `0 <= f - d(a) <= eps` on `T(A)`.
- **Stable rank one and strict comparison, the hypotheses of Theorem 5.3, enter
  only after this point**, through Theorem 4.4 and Corollary 4.7.  Those
  upgrade an approximating sequence to an exact preimage.

For bounded `f`, pick an integer `M >= sup f`, approximate `f/M` with error
`eps/M`, and take the `M`-fold direct sum.  Hence RD holds for every unital
simple separable infinite-dimensional AH algebra.

## 2. RD and strict comparison give purity

**Claim.**  Let `A` be unital simple separable exact and stably finite, with
strict comparison and RD.  Then `A` is pure.

*Almost unperforation.*  Strict comparison gives almost unperforation of
`Cu(A)` for simple exact algebras (Rordam's equivalence).

*Almost divisibility.*  Let `x = [a]`, `a in (A tensor K)_+`, `x' << x`, and
`k in N`.  We may assume `x' != 0`.

1. Choose `eps > 0` with `x' <= [(a - 2 eps)_+]`, and `b in M_n(A)_+` with
   `||a - b|| < eps/2`.
2. Since `||a - (b - eps)_+|| < 3 eps/2`, Kirchberg--Rordam gives
   `(a - 2eps)_+ <~ (b - eps)_+`; and `||b - a|| < eps/2` gives
   `(b - eps/2)_+ <~ a`.  So `x' <= [(b-eps)_+]` and `[(b - eps/2)_+] <= x`.
3. Let `phi: [0, infty) -> [0,1]` be continuous with `phi = 0` on `[0, eps/2]`
   and `phi = 1` on `[eps, infty)`, and put `h(tau) = tau(phi(b))`.  Then `h` is
   continuous affine and

   ```text
   d(x') <= d((b-eps)_+) <= h <= d((b-eps/2)_+) <= d(x).
   ```
4. Every trace of the simple unital `A` is faithful, `(b - eps)_+ != 0`, and
   `tau -> d_tau((b-eps)_+)` is lower semicontinuous on the compact `T(A)`.  So
   `c_0 := min_tau d_tau((b - eps)_+) > 0` and `h >= c_0`.
5. Apply RD to the continuous strictly positive affine function
   `g = h / (k + 1/2)` with `eta < c_0 / ((2k+1)(k+1))`, obtaining
   `y in M_infty(A)_+` with `|d(y) - g| < eta`.  Then, pointwise on `T(A)`,

   ```text
   k d(y)     < k h/(k+1/2) + k eta          < h <= d((b - eps/2)_+),
   (k+1) d(y) > (k+1) h/(k+1/2) - (k+1) eta  > h >= d((b - eps)_+),
   ```

   because `h/(2k+1) >= c_0/(2k+1) > (k+1) eta`.
6. Strict comparison, applied inside `M_infty(A)`, gives
   `k y <= [(b - eps/2)_+] <= x` and `x' <= [(b - eps)_+] <= (k+1) y`.

So `Cu(A)` is almost divisible and `A` is pure.

## 3. A second route to Toms--Winter for AH algebras

Let `A` be a unital simple separable infinite-dimensional AH algebra with
strict comparison.

1. AH algebras are nuclear, and `T(A)` is nonempty (an inverse limit of
   nonempty compact convex sets), so `A` is stably finite.
2. Section 1 gives RD and Section 2 gives purity.
3. AH algebras have locally finite nuclear dimension.  Each summand
   `p(C(X) tensor M_N)p` is approximated by images of summands over finite
   polyhedra `P_l` with `X = lim P_l`, and those images have finite nuclear
   dimension.
4. Winter's theorem gives `A = A tensor Z`.

The only difference from `simple-ah-strict-comparison-z-stable-citation` is
step 2.  There, almost divisibility is imported from Toms's note
arXiv:1102.0932.  Here it is derived from Brown--Perera--Toms's Lemma 5.2 and
the comparison argument of Section 2.

## 4. What rank density adds to the K1-witness constraints

`stw18-k1-witness-constraints` shows that a strict-comparison algebra that is
not K1-injective is not pure and has a non-surjective rank map.  Section 2 is
the contrapositive strengthening: such a witness fails even **approximate**
rank density.  Some continuous strictly positive affine function on `T(A)` has
no rank function within some fixed `eta` everywhere.

Strict comparison without purity is exactly a counterexample to part (1) of
STW Problem XXVII.  So the witness refutes XXVII(1).  That implication is
recorded as a route into the negation root
`stw27-strict-comparison-non-pure-algebra-exists`.  In the other direction, a
strict-comparison algebra that is not pure is not Z-stable: Z-stable simple
exact finite algebras have surjective rank maps (BPT Theorem 5.5, read here),
hence RD, hence purity by Section 2.  So the XXVII(1) negation root feeds the
XVIII negation root.

## 5. The invariant, for arbitrary algebras

Let `A` be unital simple separable exact stably finite non-elementary with
strict comparison.  Consider:

- (i) pure;
- (ii) RD;
- (iii) stable rank one;
- (iv) tracial approximate oscillation zero.

These are equivalent:

- (ii) ⟹ (i): Section 2.
- (i) ⟹ (iii): Lin's dichotomy, through `stw58-simple-pure-k1-bijective`,
  plus stable finiteness.
- (iii) ⟹ (ii): Thiel.
- (iii) ⟺ (iv): Fu--Lin.

With locally finite nuclear dimension they are also equivalent to
Z-stability.  A LIX-style counterexample breaks all four.  The most tractable
of them to test on a candidate is (ii): whether rank functions are dense in
the continuous affine functions on the trace simplex.

## 6. The ASH question

Every ASH algebra has locally finite nuclear dimension, so:

> **RD for all unital simple ASH algebras (no dimension-growth hypothesis)
> would prove Toms--Winter on the whole ASH class, and would exclude ASH
> witnesses for the K1 route.**

The BPT argument does not transfer directly.  In a recursive subhomogeneous
block the values on the attaching locus are forced by the lower blocks.
Extending a forced, possibly twisted, boundary element over the top cell while
keeping its normalized rank within `delta` of a prescribed profile is an
extension problem for positive matrix fields of variable rank.  It is
unobstructed once the allowed rank drop `n delta` is at least about half the
top-cell dimension, which is the slow-dimension-growth regime, where ASH
algebras are already known to be Z-stable.  It can be obstructed otherwise.
Whether such a gluing obstruction can coexist with strict comparison is the
candidate new non-Z-stable mechanism.  The analysis of this extension problem
continues in the ASH nodes of this lane.
