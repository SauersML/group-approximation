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
