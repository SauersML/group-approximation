---
rg: 2
id: sl-odd-q-simple-inputs-for-gl-n-q-root
kind: claim
title: For odd m >= 3 the group SL_m(Q) is an infinite simple group containing GL_n(Q) for n < m, so the GL_n(Q) root has simple inputs
distinct_from:
  gl-n-q-targets-are-cofinal-in-n: that is the cofinality of GL_n, SL_n, PGL_n in n; this adds that the odd-degree members SL_m(Q) are simple, which is what lets simple-input tools (just-infinite hosts, one-element criteria) act on the root.
  gl-n-q-embeds-in-fp-simple-group: that is the embedding question itself; this only replaces its inputs by an equivalent family of simple groups.
---

**ESTABLISHED** by `sl-odd-q-simple-inputs-for-gl-n-q-root-proof` (classical
facts assembled; not independently reviewed; no novelty claimed).

## Statement

Let `m >= 3` be odd.

1. `SL_m(Q)` has trivial centre, so `SL_m(Q) = PSL_m(Q)`, and it is an infinite
   simple group.
2. For every `n` with `1 <= n <= m - 1`, the map
   `g ↦ diag(g, det(g)^-1, 1, ..., 1)` is an injective homomorphism
   `GL_n(Q) -> SL_m(Q)`.
3. Hence, for any property `P` inherited by subgroups (for example "embeds in a
   finitely presented simple group"), `P(GL_n(Q))` for every `n >= 2` holds iff
   `P(SL_m(Q))` holds for infinitely many odd `m`. For one fixed `n`,
   `P(SL_m(Q))` for a single odd `m >= n + 1` gives `P(GL_n(Q))`, and
   `P(GL_m(Q))` gives `P(SL_m(Q))`.
4. Every nontrivial homomorphism from `SL_m(Q)` to any group is injective.

**Why it matters for the swarm.** Clause 4 means a construction does not have to
*embed* the countable group: it only has to produce a nontrivial image of
`SL_m(Q)`, for example elements satisfying the defining relations of `SL_m(Q)`
with one nontrivial element. Clause 1 makes the per-input simple-group tools apply
to the root: `simple-group-in-fp-simple-iff-fp-just-infinite-host` and
`sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially`. `GL_n(Q)` itself is
not simple (the determinant), and for even `m` the centre of `SL_m(Q)` is `{±1}`,
so odd `m` is the natural choice.
