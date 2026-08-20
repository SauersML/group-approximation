# The Morse lemma: what it would take

Status: **not formalized.**  This note is the decomposition, written so the next
session starts from a lemma list rather than from the literature.

## Why it is the only gap left

**Correction (2026-08-19).**  This note used to open by saying that
`Algebra/HyperbolicSlimTriangles.lean` "proves slim triangles and the four-point
condition equivalent, with constants".  It does not, and never did: that module
states *both* directions as open `Prop`-valued definitions,
`SlimImpliesFourPoint` and `FourPointImpliesSlim`, and the name step 2 below
cites (`isSlimTriangles_of_isFourPointHyperbolic`) has never existed in this
repository --- `git log -S` finds no commit containing it.  What the module does
prove is the vocabulary: `IsBetween`, `exists_isBetween`,
`twiceGromovProduct_le_of_isBetween`, and slimness for bounded metrics.  Step 2
below therefore has an extra prerequisite: `FourPointImpliesSlim`.

What no reformulation gives is invariance under change of generating set, and
that is not a bookkeeping gap: transporting the four-point condition through a
`(K,C)`-quasi-isometry --- or through a plain bi-Lipschitz map, additive error
zero --- yields

    d(y1,y2) + d(y3,y4)  <=  K^2 * max(...) + const

and the `K^2` is fatal.  **This is now a theorem rather than a remark**:
`Hyperbolic.fourPoint_transport_of_biLipschitz` in `Algebra/MorseLemma.lean`
proves exactly that inequality, and
`Hyperbolic.isFourPointHyperbolic_of_isometry` proves that at `K = 1` it *is*
the four-point condition, so the boundary of what arithmetic reaches is
machine-checked.  The same module proves the transport that needs no geometry
at all --- `isFourPointHyperbolic_of_roughIsometry`, invariance under a
quasi-isometry with multiplicative constant `1`, at `δ ↦ δ + 6C`.  No reformulation in terms of points removes it: the
four-point condition is genuinely not a bi-Lipschitz invariant of a general
metric space, and what rescues it for word metrics is that they are geodesic.
Using that fact is exactly the Morse lemma.

## Statement to aim at

Discrete form, stated against `WordMetric` and the `IsBetween` vocabulary of
`Algebra/HyperbolicSlimTriangles.lean`.  **This is now in Lean**, as
`Hyperbolic.IsQuasiGeodesic` and `Hyperbolic.MorseLemma` in
`Algebra/MorseLemma.lean` (indexed by `ℕ` rather than by a `List`, which is the
same content and avoids `List.get` arithmetic); `isQuasiGeodesic_of_isGeodesicWord`
checks the definition is the intended one by exhibiting the prefixes of a
geodesic word as a `(1,0)`-quasi-geodesic.  Nothing assumes `MorseLemma`.

    A list `p : List G` is a `(K,C)`-quasi-geodesic when for all `i j` below its
    length,  `|i - j| / K - C <= d (p.get i) (p.get j) <= K * |i - j| + C`.

    MORSE.  If `S` satisfies the four-point condition at `δ`, then there is
    `R = R δ K C` such that for every `(K,C)`-quasi-geodesic `p` from `a` to `b`
    and every `q` with `IsBetween S a q b`, some entry of `p` is within `R` of
    `q`, and every entry of `p` is within `R` of some such `q`.

## The lemma chain

1. **Paths and length.**  `IsPath S l a b` (a list of letters of `S` spelling
   `a⁻¹b`) already exists as `WordMetric.IsWord`; what is missing is the
   *vertex sequence* `partialProducts` and the fact that consecutive vertices
   are at distance `<= 1`.  Small, purely combinatorial.

2. **Divergence.**  The crux, and the only step with real content:

       If `l` is a path from `a` to `b` every vertex of which avoids the ball of
       radius `r` about a point `m` with `IsBetween S a m b`, then
       `2 ^ (r / (8 * δ + 8)) <= l.length`.

   Proof is the standard bisection: cut the path in half, apply slimness of the
   triangle on the two halves and the geodesic, and recurse; the radius drops by
   a fixed additive amount each time while the length halves.  In this
   repository slimness is available in the exact form the recursion needs
   (`isSlimTriangles_of_isFourPointHyperbolic`), and the recursion is on
   `l.length` with a `Nat.strong_induction_on`.  Estimate: 200--400 lines, and
   the place where an unverified draft would go wrong.

3. **Morse from divergence.**  Let `q` be the point of the geodesic farthest
   from the quasi-geodesic, `D` that distance.  The quasi-geodesic avoids the
   ball of radius `D` about `q`, so step 2 gives an exponential lower bound on
   its length, while the quasi-geodesic upper bound `d <= K|i-j| + C` gives a
   linear one.  Comparing them bounds `D` by a function of `δ, K, C`.  Mostly
   arithmetic once step 2 exists.

4. **Quasi-isometry invariance.**  With Morse: transport a geodesic triangle in
   the target back through a quasi-inverse, use that images of geodesics are
   quasi-geodesics, apply Morse to replace them by geodesics, then apply
   slimness upstairs.  Gives `Hyperbolic.QuasiIsometryInvariant`, which by
   `independentOfGeneratingSet_of_quasiIsometryInvariant` gives independence of
   the generating set, and --- now as a proof rather than as a remark, see
   `FiniteIndex.hyperbolicFiniteIndexPermanence_of_quasiIsometryInvariant` and
   the quasi-isometry of `Algebra/FiniteIndexQuasiIsometry.lean` --- supplies
   `HyperbolicFiniteIndexPermanence`.

## Estimate

Steps 1, 3, 4 are routine given step 2.  Step 2 is where the work is.  Total is
a multi-session project **with a compiler in the loop** --- the estimates in
step 2 are the kind that cannot be checked by reading.
