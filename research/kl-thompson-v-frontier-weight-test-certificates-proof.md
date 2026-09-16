---
rg: 2
id: kl-thompson-v-frontier-weight-test-certificates-proof
kind: route
title: Search rational weights by linear programming, verify every short cycle by moved points, and apply the weight lemma
target: kl-thompson-v-frontier-weight-test-certificates
requires:
  - kl-relative-weight-test-gives-injectivity
artifacts:
  - research/artifacts/kl-thompson-v-census-weight-test-2026-09-16.md
---

Notation as in the target. The scripts, md5 sums, command lines and logs are in
the artifact.

**Hypotheses of the lemma.** For a listed word `w`:
- every exponent is `+-1`;
- opposite-sign corners carry a letter (`g_i != 1`), so `w` is cyclically
  reduced in the sense of `kl-relative-weight-test-gives-injectivity`;
- `deg_t(w) = sum e_i` lies strictly between `0` and `n`, so it is nonzero;
- `w` is not a proper power.

The verifier checks the last three on the parsed word. Not being a proper
power in `V * <t>` is checked as "no nontrivial rotation of the syllable
sequence fixes it". That is equivalent for a cyclically reduced word, because
a proper power `u^k` of a cyclically reduced word has a syllable sequence
invariant under rotation by `n/k`.

**Why the finite search proves (WT2).**
- Every `q_i >= 1/4`, so a closed path of weight `< 2` has at most `7` steps.
  The verifier enumerates, with an explicit stack, every cyclically reduced
  closed path of weight `< 2`:
  - from both vertices;
  - in every rotation and both directions;
  - never following a step by the same edge reversed.
- For each such path it takes the letter string `s` read along the path, with
  `b <-> B` swapped on backward steps and `a`, `c` their own inverses. It finds
  a binary point `p` (one of twelve fixed 200-bit strings) such that the
  sequential prefix replacement of the letters of `s` sends `p` to a string
  disagreeing with `p` within their common length. It does the same for the
  reversed string.
- The image of an infinite sequence `p zeta` is `x zeta`, where `x` is the
  final string, so a disagreement proves the element moves a point of the
  Cantor set and is not the identity.
- Checking both `s` and its reversal covers both conventions for multiplying
  in `V` (left or right actions), so the label is nontrivial in `V` whichever
  product the lemma uses.
- Hence no admissible path has weight `< 2`, which is (WT2). (WT1) and
  `q_i >= 0` are exact rational checks.

**Generators.** The verifier's prefix maps are the Bleak--Quick generators as
defined in the target:
- `a` swaps the cones `00` and `01`;
- `b` sends `01 -> 10 -> 11 -> 01`, and `B` is its inverse;
- `c` swaps `1` and `00`.

They act by homeomorphisms of the Cantor set and generate `V`. The subgroup
they generate is the coefficient group, so a nontrivial label in this action
is a nontrivial element of `V`.

**Conclusion.** By `kl-relative-weight-test-gives-injectivity`, each listed `w`
has `V -> (V * <t>)/<<w>>` injective. Rotation replaces `w` by a conjugate, and
`w -> sigma(w^(-1))` is an automorphism of `V * <t>` fixing `V`, so the
certificate covers the whole class.

**Frontier membership.** The listed ids come from the frontier list
reproduced in the artifact. This is bookkeeping only: injectivity of each
listed word does not depend on it.
