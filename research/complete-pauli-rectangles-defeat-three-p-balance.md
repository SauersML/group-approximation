---
rg: 2
id: complete-pauli-rectangles-defeat-three-p-balance
kind: claim
title: Complete Pauli rectangles defeat uniform three-pair-edge balance
distinct_from:
  balanced-pauli-incidence-labeling: that asks for a pre-replaced incidence family satisfying uniform balance; this proves that the ordinary complete-table expander-cloud reduction does not.
  finite-offset-pauli-rectangles-violate-relative-gr-sixth: that uses a repeated two-syllable piece in relative length; this uses one short and one unbounded equality gap in ordinary word length.
---

Let a complete Pauli pair table be degree-reduced by replacing every logical
observable with a connected bounded-degree equality cloud.  If the cloud
sizes, hence some cloud diameters, tend to infinity, then the resulting
mixed rectangles do not satisfy `(BG2)` for any fixed `beta<1`.

Choose one equality edge between the occurrences for columns `r,s` in an X
cloud `q`; its equality gap has length one.  In the Z cloud for `r`, choose a
row `q'` at distance equal to the cloud diameter `L`.  Completeness supplies
the other two pair incidences, hence a rectangle on rows `q,q'` and columns
`r,s`.  Its four equality gaps include `1` and `L`, so its perimeter `T`
tends to infinity while its shortest gap is at most one.

On any four-pair-edge cyclic contour, an interval containing two pair edges
can cover all but the shortest equality gap (move its endpoints into the two
adjacent pair edges).  Its length fraction tends to at least

```text
1 - O(1/T) -> 1.                                                (CPB1)
```

This violates every uniform `beta<1` in `(BG2)`.

Therefore `balanced-greendlinger-separates-sign-cosets` remains a valid
closure theorem, but it requires a genuine replacement of the mixed Pauli
incidence geometry.  Independent expander-cloud consistency alone cannot
supply its balance hypothesis.

