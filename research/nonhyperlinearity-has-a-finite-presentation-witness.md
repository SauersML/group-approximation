---
rg: 2
id: nonhyperlinearity-has-a-finite-presentation-witness
kind: claim
title: Any nonhyperlinear group has a finitely presented nonhyperlinear witness
distinct_from:
  effective-fp-nonhyperlinearity-transfer: that embeds an effective witness in a finitely presented host with quantitative control; this uses only one bad finite multiplication window and need not embed the original group.
  canonical-profile-kleene-higman: that turns a recursive canonical-profile compiler into a finitely presented witness; this is a non-effective local equivalence for arbitrary groups.
  finite-support-corner-localizes-obstruction: that localizes a group-ring corner obstruction to a finitely generated subgroup; this replaces an arbitrary bad finite HS window by its finite partial-multiplication presentation.
---

If a discrete group `G` is nonhyperlinear, then there is a finitely
presented nonhyperlinear group `K`.  Consequently

```text
some group is nonhyperlinear
    iff
some finitely presented group is nonhyperlinear.              (FPW1)
```

The group `K` need not embed in `G`.  It is the universal group of one
finite multiplication window which already fails normalized-HS
approximation.  The canonical map `K -> G` is nevertheless injective on
the finitely many named elements of that window, which is exactly the
amount of separation needed to transfer a hypothetical microstate of `K`
back to the forbidden window in `G`.

Thus neither an infinitely presented diagonal nor an arbitrary countable
ambient group can evade the finite, dimension-independent obstruction
required by nonhyperlinearity.  If an infinite construction succeeds, one
finite multiplication window already contains a finitely presented
witness.  This is an existence reduction only: it does not compute the bad
window from a presentation of `G`.
