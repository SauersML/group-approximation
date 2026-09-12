---
rg: 2
id: gsc-does-not-separate-sign-double-cosets
kind: claim
title: Ordinary graphical small cancellation does not separate Pauli sign double cosets
distinct_from:
  colored-cayley-pauli-incidence-separation: that asks for relative subgroup and sign separation in one useful incidence host; this gives a sharp counterexample to obtaining that separation from an unqualified small-cancellation labeling.
  fp-cayley-expanders-give-bounded-occurrence-edges: that uses small cancellation only to obtain bounded-word embedded edges and makes no relative double-coset claim.
---

For every `lambda>0` there is a finite symmetrized classical
`C'(lambda)` presentation with disjoint finite alphabets

```text
D_X, D_Z, {p_0}, {p_1}
```

such that, in the presented group,

```text
<D_X> p_0 <D_Z>  intersect  <D_X> p_1 <D_Z>  != empty.          (GSC1)
```

The same example is a graphical small-cancellation presentation on one
labeled cycle.  Consequently, refining an Osajda label by the four finite
edge types `X`, `Z`, `0`, `1` preserves the piece bound but does **not** by
itself prove the relative separation required by
`colored-cayley-pauli-incidence-separation`.

The missing input really is a relative convexity/Freiheitssatz statement
using additional incidence combinatorics.  It is not a formal consequence
of `C'(lambda)`.

