---
rg: 2
id: explicit-random-relator-witness-extraction
kind: claim
title: Extract and certify one concrete random-relator tuple from the entropy argument
artifacts:
  - research/artifacts/nonhyperlinear-random-presentation-and-matricial-separator-2026-08-18.md
  - experiments/random_word_return_strata.py
---

From the finite random-relator model and quantitative estimates in
`unitary-word-return-entropy-summability`, produce an **explicitly listed**
finite relator tuple `(r_1,...,r_m)` together with checkable constants
`R,delta,eps,eta` such that:

1. the relators satisfy the chosen short-word preservation condition (for
   example a directly verified `C'(1/6)` condition with `2R<L/2`); and
2. the same quantitative return/packing proof certifies that no
   `delta`-separated unitary model of the prescribed short ball can make every
   `r_i` have normalized-HS defect at most `eps`, in any matrix dimension.

The probabilistic inequality alone proves that some support point works, but
that is not enough for the repository's root wording **Exhibit an explicit
non-hyperlinear group**.  This node prevents the random route from closing the
root until a concrete word list and its quantitative certificate have actually
been written down.

## Attempts

- Make every estimate in `unitary-word-return-entropy-summability` effective
  with rational constants and use a deterministic finite support ordered
  lexicographically.  Strengthen the proof so it identifies a nonempty subset
  of support points by a finite/checkable certificate rather than only by a
  global expectation argument.
- Search small-cancellation support tuples numerically for unusually low
  worst-stratum return, then freeze promising relators and prove their bounds
  analytically stratum by stratum.  Randomness is a discovery device; the final
  Cairn witness must be a fixed finite presentation.
