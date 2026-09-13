---
rg: 2
id: fp-simple-dehn-functions-have-no-recursive-upper-bound
kind: claim
title: No recursive function bounds the Dehn functions of all finitely presented simple groups
distinct_from:
  fp-simple-groups-with-arbitrarily-complex-word-problem: that asks for word problems beyond every recursive time bound; this asks only that Dehn functions escape every recursive bound, which that claim implies through the diagram-enumeration algorithm.
---

**OPEN.** For every recursive `f: N -> N` there is a finitely presented simple
group `S` with `delta_S ⋠ f`.

This is the weak reading of Zaremsky Problem 1.16. It is partial progress only:
it does not close `zaremsky-1-16-fp-simple-groups-with-large-dehn-functions`,
whose adopted reading is `fp-simple-dehn-functions-realize-every-recursive-lower-bound`.

Two routes lead here:

- `fp-simple-unbounded-dehn-via-complex-word-problem`, from the Boone–Higman
  complexity root `fp-simple-groups-with-arbitrarily-complex-word-problem`;
- `fp-simple-unbounded-dehn-from-realized-lower-bounds`, from the strong reading.

## Attempts

1. **Through word-problem complexity.** Wired as the first route above. Open
   because the complexity root is open; see that root for its attacks.
2. **Directly from Dehn-function geometry.** Any single example family with Dehn
   functions escaping every recursive bound would do, with no complexity input.
   The known quasi-retract examples stop at exponential; see the Attempts of
   `fp-simple-dehn-functions-realize-every-recursive-lower-bound`.
