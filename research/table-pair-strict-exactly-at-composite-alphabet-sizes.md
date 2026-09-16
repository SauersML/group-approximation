---
rg: 2
id: table-pair-strict-exactly-at-composite-alphabet-sizes
kind: claim
title: A two-by-three table pair admits strict rules exactly over the alphabets of composite size
distinct_from:
  strict-rule-pairs-ascend-to-larger-alphabets: that asserts upward-closed admissible sizes for every table pair; this is one table pair admitting four symbols and no prime number of symbols, which refutes it.
  equal-label-table-is-strict-at-three-symbols-not-two: that is a two-by-two table whose admissible sizes are all n >= 3, an upward-closed set; this is a two-by-three table whose admissible sizes are the composite numbers, with a gap at every prime.
  strict-rule-pairs-pass-to-product-alphabets: that proves admissible sizes are closed under multiples for every table pair; this exhibits admissible sizes (the composites) closed under multiples but not upward closed, so closure under multiples does not extend to upward closure.
  copy-codes-make-one-sided-table-identities-strict: that gives the pairs strict at every size through a copied cell; here no copy code is strict, and at prime sizes every forward solution agrees with a relabelled copy code on every input the reverse identity reads.
artifacts:
  - research/artifacts/composite-size-strict-table-2026-09-16.md
---

**ESTABLISHED** by `table-pair-strict-exactly-at-composite-sizes-proof`. Elementary; no novelty is claimed.

Conventions of `boolean-core-is-uniform-single-demand-network-coding` (tables are arbitrary equivalence relations on
the cells). Take `S = {1, a}` and `M = {1, b, c}`.
- **Forward table `T_f`.** One nontrivial class `{(1,1), (1,b), (a,c)}`; every other cell is a singleton.
- **Reverse table `T_r`.** One nontrivial class `{(1,1), (b,1), (c,a)}`, the transpose; every other cell is a singleton.

In network form, with sources `o, e, f, g` and `o, u, v, w`:

    Dec(T_f):   nu( mu(o, o, e), mu(f, g, o) ) = o,
    Enc(T_r):   mu( nu(o, u), nu(o, v), nu(w, o) ) = o.

**Claim.** An alphabet with `n >= 2` symbols carries rules `(mu, nu)` with `Dec(T_f)` true and `Enc(T_r)` false exactly when
`n` is composite. The same holds with `T_r` replaced by any reverse table in which `(b,1)` and `(c,a)` are equivalent to
`(1,1)` and `(1,a)`, `(b,a)` are not equivalent to each other.

**Consequences.**
- **Refutation.** Strict rules exist over 4 symbols and not over 5, so `strict-rule-pairs-ascend-to-larger-alphabets` is
  false. Above every admissible size there is an inadmissible prime.
- **Not group data.** Every group labelling with `x_1 = 1` whose forward table contains `T_f` has `x_b = 1`, so its
  reverse table identifies `(1,a)` with `(b,a)`. The example says nothing against group-level ascent
  (`nonsurjunctive-alphabet-sizes-are-upward-closed`). A table pair realized in a group with a strict size would
  already refute Gottschalk's conjecture.
