---
rg: 2
id: finite-bi-index-kazhdan-subgroup-forces-nonamenability
kind: claim
title: An infinite finite-bi-index pair with Kazhdan stabilizer has nonamenable ambient group
distinct_from:
  hs-stable-finite-bi-index-kazhdan-pair-exists: that asks for the full stability and subgroup package; this is an elementary restriction which excludes every amenable ambient candidate before stability is considered.
  simple-core-bi-index-counts-coset-action-pair-orbits: that identifies pair orbits with double cosets; this combines double-coset finiteness with amenability and property (T) to rule out an entire class of pairs.
---

Let `H<L`, assume `H` has property (T), `[L:H]=infinity`, and
`|H\L/H|<infinity`.  Then `L` is nonamenable.

Indeed, if `L` were amenable then its subgroup `H` would be amenable.  An
amenable discrete property-(T) group is finite.  But every double coset of a
finite subgroup has at most `|H|^2` elements, so finitely many double cosets
would make `L` finite, contradicting `[L:H]=infinity`.

Consequently the stable-pair coherence route cannot use the broad amenable
families for which character criteria currently supply most positive
normalized-HS stability results.

