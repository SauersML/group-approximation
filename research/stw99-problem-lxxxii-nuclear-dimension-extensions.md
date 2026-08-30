---
rg: 2
id: stw99-problem-lxxxii-nuclear-dimension-extensions
kind: claim
title: Nuclear dimension should be the maximum across an extension (STW Problem LXXXII)
root: true
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw82-one-color-gluing-audit-2026-08-30.md
  - research/artifacts/stw82-projectional-cut-obstruction-audit-2026-08-30.md
  - research/artifacts/stw82-transition-band-colour-graph-audit-2026-08-30.md
  - research/artifacts/stw82-order-zero-spectral-subdivision-audit-2026-08-30.md
---

**Problem LXXXII of Schafhauser--Tikuisis--White,
[arXiv:2506.10902v2](https://arxiv.org/abs/2506.10902).**  Given an arbitrary
extension

```text
0 -> I -> E -> D -> 0,
```

is

```text
dim_nuc(E) = max(dim_nuc(I), dim_nuc(D))?
```

The reverse inequality is automatic because nuclear dimension does not
increase on ideals or quotients.  Winter--Zacharias' general gluing argument
only gives

```text
dim_nuc(E) <= dim_nuc(I) + dim_nuc(D) + 1.
```

There is now an exact comparison invariant below nuclear dimension.
`stw81-continuous-trace-shadow-invariant` defines `ctdim` from the spectrum
dimensions of continuous-trace subquotients, and
`stw81-ctdim-extension-maximum` proves

```text
ctdim(E) = max(ctdim(I),ctdim(D)) <= dim_nuc(E).
```

Thus a counterexample to the formula in this problem cannot be caused by
topological dimension hidden across the extension; it must be a genuinely
noncommutative failure of approximation-color reuse.

As of 2026-08-30 this remains open in the stated generality.  The May 2026
version of the 99-problems paper still asks it.  A search of the primary arXiv
catalogue through that date found no later paper claiming the arbitrary
extension theorem; the latest directly targeted paper remains Evington--Ng--
Sims--White, [arXiv:2409.12872v2](https://arxiv.org/abs/2409.12872), which
proves the maximum formula for extensions with stable Kirchberg ideal and
commutative unital quotient.  Other established positive cases include
separable commutative extensions, AF-by-AF extensions, quasidiagonal
extensions, essential extensions of commutative algebras by the compacts
([Gardner--Tikuisis](https://arxiv.org/abs/2202.04695)), and the special
`O_infinity`-stable cases in
[Evington](https://arxiv.org/abs/2012.03650).

The repository now removes "separable" from the subhomogeneous case:
`stw82-subhomogeneous-maximum` proves
the formula whenever both endpoints are subhomogeneous, with no separability
hypothesis.  In particular, arbitrary commutative extensions obey the
maximum formula.

There is also a new unconditional middle-algebra class:
`stw82-one-dimensional-middle-forces-maximum` shows that every
ideal--quotient decomposition of an arbitrary algebra `E` with
`dim_nuc(E)<=1` satisfies the maximum formula.  The only possible low-end
failure would have both endpoints of dimension zero; AF extension closure
on the separable counterexample supplied by the reflection theorem rules
this out.  Consequently any counterexample has middle nuclear dimension at
least two.

The project reduction
`stw82-counterexamples-reflect-to-separable-extensions` shows that the word
"arbitrary" does not create a separate nonseparable frontier: every
counterexample would already have a separable subextension counterexample
with no larger endpoint dimensions.

The Busby-kernel reduction
`stw82-every-counterexample-essentializes` removes a second inessential
frontier.  For Busby map `tau`, enlarge the ideal from `I` to the preimage of
`ker(tau)`.  That new ideal is `I directSum ker(tau)`, is essential in the
same middle algebra, and has nuclear dimension no larger than the original
endpoint maximum.  Thus every failure already has a separable extension by
an essential ideal; the unresolved theorem may be attacked in that sharply
reduced setting.

Stabilization sharpens this once more:
`stw82-counterexamples-reduce-to-stable-essential-extensions` proves that a
failure exists if and only if there is a separable stable extension with
essential ideal that fails.  Exactness, all three nuclear dimensions, and
essentiality survive tensoring with the compact operators.  Hence the full
problem can be studied with an injective Busby map into the corona of a
separable stable ideal, without losing any possible counterexample.

There is a second localization from Problem LXXXI.
`stw81-finite-ideal-counterexample-forces-lxxxii-counterexample` shows that a
separable finite-ideal algebra of finite nuclear dimension at least two,
despite having only one-dimensional commutative hereditary shadows in all
quotients, would contain an extension counterexample here whose ideal and
quotient both have nuclear dimension at most one.

## Attempts

The established route
`stw82-separable-maximum-implies-arbitrary-maximum` removes nonseparability
from the problem.  What remains is the separable maximum theorem.  The
standard quasicentral-approximate-unit proof produces disjoint ideal and
quotient approximations but gives their colours separate labels, yielding
the sum-plus-one bound.  Known optimal proofs reuse colours only after
obtaining extra orthogonality from the extension (for example a
quasidiagonal projectional approximate unit, or the classification inputs in
the Kirchberg-ideal cases).  No mechanism currently supplies that
orthogonality for an arbitrary separable extension.

The exact local obstruction is now recorded in
`stw82-order-zero-direct-sum-support-criterion`: two order-zero maps merge by
the direct-sum construction precisely when their unit supports are
orthogonal.  For the complementary supports `h` and `1-h`,
`stw82-complementary-cutdowns-merge-iff-near-projections` proves, with
explicit estimates, that asymptotic orthogonalizability is equivalent to
`h` being asymptotically projectional.  This is not a consequence of
quasicentrality.  Indeed,
`stw82-commutative-max-formula-with-maximal-cutdown-overlap` shows that in
the interval endpoint extension every positive contractive quasicentral
approximate unit has overlap norm exactly `1/4`, although the maximum
formula holds.  Thus the unresolved gluing step must reorganize the colour
maps or absorb their transition region; perturbing the two raw cuts cannot
be a general proof.

The global form of this barrier is now exact.
`stw82-raw-two-cut-reuse-iff-quasidiagonal` proves that a separable
extension admits an asymptotically projectional quasicentral approximate
unit -- equivalently, its two raw complementary supports can be perturbed
to orthogonal supports -- if and only if the extension is quasidiagonal.
So raw-cut perturbation cannot enlarge the already known quasidiagonal
positive class.  After the separable/stable/essential reductions, the exact
remaining hinge is to redistribute the transition band among the endpoint
colours in a non-quasidiagonal extension, as the known optimal proofs do
using special classification input.

The transition-band obstruction has now been sharpened beyond one pair of
cuts.  `stw82-indivisible-order-zero-reuse-is-graph-colouring` proves that
for any finite family of fixed outgoing order-zero maps, the least number of
global colours obtainable by direct-sum relabelling is exactly the chromatic
number of the graph whose edges are nonorthogonal support pairs.  Thus a
fixed-map two-colour merger exists exactly when this support graph is
bipartite.  This is also an unconditional colour-reuse theorem: a family of
finite-dimensional approximations whose support graphs are uniformly
`(r+1)`-colourable compiles directly into nuclear dimension at most `r`,
with no additional colour.

Moreover, `stw82-two-by-two-colour-reuse-quantitative-obstruction` gives a
norm lower bound for perturbing two ideal and two quotient/transition
colours into any two-colour assignment.  It tests both internal support
overlaps and both possible cross matchings, and remains valid when the
assignment varies with the approximation stage.  Hence an odd-cycle or
positive matching obstruction cannot be removed by relabelling intact
colours.  The general quantitative form
`stw82-odd-support-cycle-stable-two-colour-obstruction` shows that an odd
cycle whose edge overlaps stay uniformly positive forces a fixed positive
perturbation error for every stage-dependent two-colour assignment.  This
still does not decide the problem: a universal proof may
split or replace the transition-band maps, as all known non-quasidiagonal
optimal proofs do under additional classification hypotheses.

There is nevertheless a genuinely nonprojectional positive colour-reuse
mechanism.  `stw82-spectral-interval-band-depth-reuses-colours` proves that
when the outgoing unit supports are functions of one positive contraction,
localized in spectral intervals of overlap depth `r+1`, the unchanged maps
regroup into `r+1` order-zero colours.  Thus any approximation scheme with
such band depth proves nuclear dimension at most `r`, exactly.  This moves
the universal hinge again: the missing theorem is a structure-free way to
subdivide arbitrary transition maps into common-cut spectral bands while
preserving their order-zero structure and approximation quality.

That local subdivision problem is now solved.
`stw82-quasicentral-cutdowns-repair-to-banded-order-zero` proves that a
finite-dimensional outgoing order-zero map can be cut by any finite
quasicentral multiplier partition of unity and perturbed, inside the
corresponding hereditary band algebras, to exact order-zero maps whose sum
approximates the original map.  The proof uses projectivity of the cone over
a finite-dimensional algebra, and requires no projectional cut or extension
regularity.

There is also an exact limitation.
`stw82-scalar-band-depth-floor` proves
that independently subdividing `N` original colours by scalar partitions of
unity produces band depth at least `N` at every spectral point.  Thus doing
this separately to all endpoint colours cannot improve the sum of their
colour counts to the desired maximum.  The remaining universal hinge is a
support-sensitive **coupled** subdivision: it must exploit operator
orthogonality or support vanishing across different endpoint colours, not
only scalar partitions of the common cut variable.
