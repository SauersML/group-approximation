---
rg: 2
id: sampled-hash-pvm-matching-proof
kind: route
title: Correct a slow sample, cancel physical boundary in trace, and polar-match the hash PVMs
target: sampled-coordinate-joint-pvm-tracks-terminal-character-hash
requires:
  - weighted-code-character-hash
  - slowly-growing-reflection-sample-rounds-to-commuting
  - diagonal-sign-margin-controls-hash-overlap
  - pvm-overlap-polar-matches-large-labeled-carriers
---

Include in the coordinate cost used by the weighted hash both the
complete-pair row energy and the squared terminal diagonal sign error.
Choose `t->infinity` sufficiently slowly that

```text
t epsilon->0,       t sqrt(eta)->0,
```

and that the fixed-sample commuting correction has total squared movement
`o(1/t)`.  The hash collision tail then tends to zero as well.

Correct the sampled reflections jointly and let `(E_u)` be their PVM.  Let
`(F_v)` be the terminal PVM coarsened by sampled sign vector.  Cauchy--Schwarz
and the selected squared-error budget make the sum of diagonal sign norms
`O(t sqrt(eta))`; the sample correction norms are `o(1)`.  The diagonal-sign
overlap theorem therefore gives

```text
sum_(u!=v)tau(E_uF_v)=o(1).
```

Apply the labeled polar theorem.  It supplies one near-identity unitary
matching the two hash PVMs outside `o(1)` trace.  Conjugating the fine
terminal atoms by this unitary changes every bounded generator by `o(1)` in
normalized HS norm.  The weighted hash lemma bounds the remaining
different-character mass inside equal-hash buckets by `o(1)`.  Equal
characters may be merged, and the unmatched carrier is quarantined.  This
is exactly the asserted transported pinching match.
