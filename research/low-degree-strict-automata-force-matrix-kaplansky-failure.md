---
rg: 2
id: low-degree-strict-automata-force-matrix-kaplansky-failure
kind: claim
title: A strict automaton over F_q with deg sigma * deg tau below q forces a matrix direct-finiteness failure of F_p over the group
distinct_from:
  stable-finiteness-failure-refutes-surjunctivity: that is the converse direction, a matrix one-sided pair gives a strict linear automaton; this proves that every low-degree strict automaton comes from such a pair.
  low-degree-strict-pairs-have-one-sided-linear-parts: that is the established dichotomy, a pair or a unipotent automaton; this is its consequence once the unipotent branch is shown never strict.
artifacts:
  - research/artifacts/low-degree-strict-pairs-linear-parts-2026-09-12.md
---

Let `G` be a group and `F = F_q` with `q = p^k`. Suppose `G` carries an injective, non-surjective
automaton `tau` over `F^m` with a left inverse `sigma` such that `deg sigma * deg tau < q`. Then
the linear parts satisfy `C A = I_m != A C`. So `M_m(F_q[G])` and `M_(mk)(F_p[G])` are not directly
finite.

**Contrapositive.** On any host where every `M_n(F_p[G])` is directly finite, every injective
automaton over `F_q^m` whose left inverse satisfies the degree bound is surjective.

**Why it matters.**
- Low-degree nonlinearity over large fields never gives a counterexample beyond the linear
  Kaplansky ones. Every design built as low-degree nonlinear functions of idempotent projections
  is a matrix Kaplansky pair in disguise.
- For invariant output this is `low-degree-invariant-output-reduces-to-corner-fullness`.
- Genuinely nonlinear counterexamples need degree product at least `q`. That covers every binary
  design, and every larger-field design whose decoder identity uses the reduction `x^q = x`.

Established 2026-09-12 by `low-degree-kaplansky-failure-via-unipotent-surjectivity`, from
`low-degree-strict-pairs-have-one-sided-linear-parts` and
`unipotent-automata-over-finite-fields-are-surjective`. Sections 2, 5 and 7 of the artifact.
