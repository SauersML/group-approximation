---
rg: 2
id: dummy-padding-cannot-beat-the-random-guessing-floor
kind: claim
title: A decoding list of size proportional to the alphabet only reproduces the 2-to-1 game's own random-assignment value
invalidates:
  - rich-2to1-via-dummy-label-padding
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED.**  Let `G` be a 2-to-1 game whose constraints are 2-to-1 maps
`pi : [K] -> [K/2]`.  Independent uniform labels on the two sides satisfy a
given constraint with probability

```text
Pr_{a,b uniform}[ pi(a) = b ] = 1/(K/2) = 2/K,
```

so unconditionally

```text
OPT(G) >= 2/K.                                                          (F1)
```

Now suppose a hard core of alphabet size `K` is hidden inside a much larger
randomly matched dummy alphabet, and suppose the soundness decoder cannot
analytically orient the core fibers.  Its safe list is then the whole
`K`-element core, and choosing the right member of a 2-element fiber
succeeds at rate

```text
2/K.                                                                    (F2)
```

`(F2)` equals `(F1)`.  So a soundness argument obtained by "list the whole
exceptional core" can never contradict anything: it establishes exactly the
value a uniformly random assignment already achieves, and no gap survives.

**Consequence, and it is the design constraint on the whole region.**
Rich 2-to-1 hardness cannot be obtained from "mostly random" constraints
plus an alphabet-sized decoding list.  It needs an **alphabet-independent**
list of influential coordinates.  That is precisely the `|Q| <= L` with `L`
independent of `k` demanded by `affine-orientation-glue-lemma`, and it is
why the words "independent of k" there are load-bearing rather than
cosmetic.

The proof is `dummy-padding-random-guessing-floor-proof`.
