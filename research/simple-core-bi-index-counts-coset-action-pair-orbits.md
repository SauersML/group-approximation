---
rg: 2
id: simple-core-bi-index-counts-coset-action-pair-orbits
kind: claim
title: The coset action on a normally generating simple core is faithful and its pair-orbits are the double cosets
distinct_from:
  proper-normal-subgroups-miss-the-normally-generating-core: that is the lattice statement about proper normal subgroups; this is about the coset ACTION on Gamma/S -- its faithfulness and the count of its orbits on ordered pairs -- and it uses the lattice statement only to kill the normal core.
  twisted-brin-thompson-finite-presentation-criterion: that is the imported criterion saying which actions give finitely presented twisted Brin-Thompson groups; this checks two of that criterion's three hypotheses for one specific action and translates the third into a double-coset count.
artifacts:
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

Keep the hypotheses of
`proper-normal-subgroups-miss-the-normally-generating-core`: `S` nontrivial
simple, `S <= Gamma`, `Gamma = <<s>>_Gamma` for some `1 != s in S`.  Assume
also `S != Gamma`.  Consider the left multiplication action

    Gamma  acts on  Gamma/S .

Then:

1. the action is **faithful**;
2. its orbits on ordered pairs are in bijection with the double cosets
   `S \ Gamma / S`;
3. its point stabilizer is `S`, which is finitely generated whenever `S` is.

Write the **bi-index** of `S` in `Gamma` for `|S \ Gamma / S|`.  (Local
terminology; see the attribution note on
`twisted-brin-thompson-finite-presentation-criterion`.)

## What this reduces the second route to

`Gamma` is finitely presented and `S` is finitely generated, so clauses 1 and
3 already supply two of the three hypotheses of
`twisted-brin-thompson-finite-presentation-criterion` and the faithfulness
that makes `SV_Gamma` simple.  Clause 2 converts the remaining hypothesis —
finitely many pair-orbits — into a single arithmetic condition on the
subgroup pair, `|S \ Gamma / S| < infinity`.  That condition is
`ck-envelope-simple-core-has-finite-bi-index`, and it is the entire content
of `boone-higman-via-finite-bi-index-envelope`.

The trade is worth stating plainly: this route replaces a Noetherianity
question about the normal lattice with a finiteness question about double
cosets.  Neither is known, and there is no implication between them in either
direction that this audit could find.

## The degenerate case is not a gap

If `S = Gamma` then the coset space is a point and the claim is vacuous — but
in that case `Gamma` is itself a finitely presented simple group containing
the original group, and `boone-higman-conjecture` is proved outright for that
input.  So the hypothesis `S != Gamma` costs nothing.
