---
rg: 2
id: infinitely-q-divisible-dvr-matrices-are-torsion
kind: claim
title: Over a mixed-characteristic DVR with finitely generated residue field, a matrix with q^j-th roots for every j has finite order
distinct_from:
  lifts-add-no-unipotent-divisibility: that shows central lifts of Q-free groups gain no divisible unipotents; this is a local statement about GL_N of one discrete valuation ring of residue characteristic q.
  fg-piecewise-linear-hosts-omit-natural-gl-n-q: that bounds the entries of derivative cocycles of finitely generated groups; this bounds divisibility inside GL_N(O) for a single valuation ring O, with no finiteness of the group.
---

**ESTABLISHED** through `infinitely-q-divisible-dvr-matrices-are-torsion-proof`.
Lane proof, not independently reviewed. The argument is a standard congruence
filtration argument; no priority is claimed.

**Statement.** Let `q` be a prime and let `O` be a discrete valuation ring whose
fraction field has characteristic 0, whose maximal ideal contains `q`, and whose
residue field `k` is finitely generated as a field over `F_q` (for example finite).
Let `N >= 1` and `g in GL_N(O)`. Suppose that for every `j >= 1` there is
`h_j in GL_N(O)` with `h_j^(q^j) = g`. Then `g` has finite order, and its order is
prime to `q`.

**Uses.**
- `z-localizations-embed-in-gl-n-only-along-inclusion`: `O = Z_(q)`.
- `infinite-prime-localizations-embed-in-no-fg-linear-group`: `O` a DVR through a
  finitely generated domain.
- Inside `SL_2(Z_(l))` no element of infinite order is infinitely `l`-divisible,
  so in `sl-2-q-is-an-amalgam-of-sl-2-z-localized-at-ell` the `l`-divisibility of
  `(Q,+) <= SL_2(Q)` is created by the amalgam and not by a vertex group.
