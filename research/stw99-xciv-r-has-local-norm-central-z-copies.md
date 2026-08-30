---
rg: 2
id: stw99-xciv-r-has-local-norm-central-z-copies
kind: claim
title: R has local operator-norm central copies of Z
distinct_from:
  stw99-hyperfinite-factor-property-si: that is a small-to-large comparison property in a tracial relative ultrapower; this asks for actual homomorphisms into R with finite operator-norm commutator control.
  stw99-xciv-separable-zstability-iff-local-norm-central-z: that established theorem proves the general equivalence between local norm-central copies and separable Z-stability; it does not prove that R satisfies either equivalent condition.
---

For every finite `F subset R`, finite `G subset Z`, and `epsilon>0`, there is
a unital homomorphism `phi:Z->R` such that

```text
||[a,phi(z)]|| < epsilon       (a in F, z in G).
```

This is open.  By
`stw99-xciv-separable-zstability-iff-local-norm-central-z`, it is an exact
operator-norm reformulation of Problem XCIV, rather than an additional
assumption known from McDuffness.

## Attempts

McDuff tensor tails produce the displayed estimates in `2`-norm, but the
orthogonal-corner construction in
`stw99-xciv-two-norm-centrality-does-not-control-norm-centrality` shows that
such estimates do not select norm-central representatives, even relative to
one fixed element.  Exact commuting CAR copies do give the conclusion by
`stw99-xciv-commuting-car-seed-has-zstable-hull`, but this cannot be applied
to an arbitrary initial seed: a norm-separable weakly dense subalgebra of `R`
has scalar relative commutant in `R`.  The unresolved step is therefore to
construct actual `Z` embeddings with finite operator-norm control without
requiring an exact tensor tail.

It is now enough to centralize one fixed finite building block rather than
the whole of `Z`.  By
`stw99-xciv-single-prime-block-centrality-is-exact`, the open claim is
equivalent to finding, for every finite `F subset R` and `epsilon>0`, a
unital `psi:I_(2,3)->R` whose fixed finite generating set commutes with `F`
within `epsilon` in operator norm.  Repeating such local copies in a
commuting-column diagonal manufactures the missing central `Z` copy.  This
does not turn McDuff `2`-norm centrality into the required norm estimates.

There is a quantitative positive finite-test class.  By
`stw99-xciv-finite-dimensional-radius-controls-block-defect`, the least
commutator defect of a unital `I_(2,3)` copy against a finite tuple `F` is at
most twice the tuple's operator-norm distance to unital finite-dimensional
subalgebras of `R`.  Hence every norm-locally finite-dimensional tuple works;
this includes all finite tuples in uniformly bounded type-I von Neumann
subalgebras and, in particular, all commuting normal tuples.  Conversely any
negative fixed-block gap `delta` forces distance at least `delta/2` from
every finite-dimensional subalgebra.  Hyperfinite `2`-norm approximation
does not bound this norm radius.

The finite-dimensional route cannot cover all tests:
`stw99-xciv-some-finite-tuple-has-positive-fd-radius` proves that some finite
tuple has positive norm distance from every finite-dimensional subalgebra;
otherwise ucp retractions would make `R` nuclear as a C*-algebra.  A broader
route is `stw99-xciv-commutant-capacious-radius-controls-block-defect`.
Distance to any subalgebra whose relative commutant contains `I_(2,3)` gives
the same factor-two estimate.  This includes arbitrary diffuse tensor legs,
so it captures noncommuting tests with no matrix approximation.  Any
negative certificate must stay uniformly far from every such capacious
core, not merely from finite-dimensional algebras.

There is a distinct internal-core mechanism.
`stw99-xciv-zstable-core-radius-controls-block-defect` bounds the fixed-block
defect by twice the distance to separable unital `Z`-stable subalgebras of
`R`.  It covers simple nuclear infinite-dimensional finite-nuclear-dimension
norm cores.  This route does not require ambient commutant capacity: the
tracial GNS copy of `Z` is weakly dense in `R` and has scalar relative
commutant, yet every finite tuple in that copy has zero block defect through
approximately central maps internal to the copy.  Any negative certificate
must therefore avoid both exact-commutant cores and all nearby internally
`Z`-stable cores.
