---
rg: 2
title: STW LXXXII transition-band support-graph audit (2026-08-30)
kind: artifact
---

# Scope

This audit continues the LXXXII analysis after the proof that perturbing the
two raw complementary cuts is equivalent to quasidiagonality of the
extension.  It isolates what can be proved for an arbitrary finite family
of already chosen outgoing order-zero colours.  It does not claim that the
full extension maximum formula is solved.

# Exact support graph

For outgoing cpc order-zero maps `(phi_v)`, put an edge `v--w` exactly when
their unit supports have nonzero product.  A collection of the maps can be
directly summed into one cpc order-zero map exactly when its vertices form
an independent set.  Therefore the minimum number of global colours
obtainable by relabelling and summing the maps, while leaving every map
indivisible, is exactly the chromatic number of this overlap graph.

This packages all pairwise support conditions, not merely the complementary
pair `h,1-h`.  Two-colour reuse is equivalent to bipartiteness.  In
particular, an odd support-overlap cycle is an exact obstruction to an
indivisible two-colour merger.

The statement is also a positive compiler.  If arbitrarily accurate
finite-dimensional approximations have constituent support graphs
colourable with `r+1` colours, regrouping the unchanged maps along a graph
colouring proves nuclear dimension at most `r`.  This reuses colours with
no extra `+1`.

If the overlaps along an odd cycle all have norm at least `kappa`, then any
perturbation of the constituent maps into two global colours has error at
least `kappa/2`.  This remains true for stage-dependent cycles and
colourings.  It is therefore a stable obstruction rather than merely a
failure of one exact labelling.

# Quantitative four-map obstruction

For two ideal-side supports `h_0,h_1` and two quotient/transition-side
supports `k_0,k_1`, define

```text
mu=min(
 ||h_0h_1||,
 ||k_0k_1||,
 max(||h_0k_0||,||h_1k_1||),
 max(||h_0k_1||,||h_1k_0||)
).
```

Any perturbation by at most `delta` which assigns the four maps, without
splitting, to two order-zero colours satisfies `delta>=mu/2`.  The proof is
the two-colour pigeonhole principle plus the estimate

```text
xy=0, ||h-x||<=delta, ||k-y||<=delta
   => ||hk||<=2 delta.
```

The two cross maxima are both necessary: they are the two possible
matchings after each endpoint pair is forced to use both colours.  Thus this
bound remains valid when the colour assignment changes at every stage.

# Relation to the Brake--Winter transition band

An almost-idempotent quasicentral approximate unit gives three macro bands

```text
A_n=h_n I h_n,
B_n=(h_(n+1)-h_n) I (h_(n+1)-h_n),
C_n=(1-h_(n+1)) E (1-h_(n+1)).
```

The outer bands `A_n` and `C_n` are orthogonal, while the middle band can
overlap both.  At the macro level this is a path and hence bipartite.  The
difficulty arises after the maps through the endpoint algebras are each
decomposed into their own order-zero colours: the resulting support graph
can acquire odd cycles or require more than the endpoint maximum number of
colours.  The new theorem shows exactly what every no-splitting merger must
overcome.

Successful special-case proofs do not contradict the obstruction.  They
use classification or special extension structure to replace, split, and
move the transition-band maps until the required cross-support products
vanish.  The graph theorem identifies this reorganization, rather than
mere relabelling, as logically necessary whenever the obstruction number
has a positive lower bound.

# Remaining hinge

After the existing reductions, the universal case is a separable stable
essential non-quasidiagonal extension.  There are now two rigorously
excluded generic strategies:

1. orthogonalize the two raw complementary cuts -- this is equivalent to
   quasidiagonality;
2. keep four endpoint colours indivisible and merely relabel them into two
   colours -- this fails quantitatively whenever `mu` is bounded below.

What remains is a structure-free subdivision or replacement theorem for
transition-band order-zero maps which destroys all odd overlap cycles while
preserving the approximation.  No such theorem is supplied by the standard
quasicentral approximate-unit construction.
