---
rg: 2
id: memorizer-superposition-has-large-sup-norm
kind: claim
title: Every superposition of pair memorizers with uniformly large coefficients has sup norm at least delta times the square root of the direction count
distinct_from:
  affine-memorizers-are-cross-direction-orthogonal: that is the disjoint-Fourier-support statement licensing the superposition and computing its L^2 norm; this is a sup-norm lower bound proved by evaluating at the linear points, and it is what stops the superposition from being renormalized.
  linear-pairing-memorizer-restricts-to-a-dictator: that concerns one direction and is a positive construction; this is a negative bound on the whole linear span.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED.**  Keep the notation of
`affine-memorizers-are-cross-direction-orthogonal`, `r` odd.  Let
`B subset Omega \ {0}` be any set of directions and `c_b` any real
coefficients.  Then

```text
|| sum_{b in B} c_b B_{b,r} ||_infty >= ( sum_{b in B} c_b^2 )^(1/2).      (S1)
```

In particular, if `|c_b| >= delta` for every `b in B`,

```text
|| sum_{b in B} c_b B_{b,r} ||_infty >= delta * |B|^(1/2),                 (S2)
```

and for `B = Omega \ {0}` with all `c_b = 1` the sup norm is exactly `N-1`,
attained at the all-ones point.

The mechanism is that on the `N` **linear** points `X = chi_t`,
`(chi_t)_u = (-1)^{<t,u>}`, the memorizers are literally the
`F_2`-characters:

```text
B_{b,r}(chi_t) = (-1)^{<t,b>}.
```

Parseval on `F_2^k` then gives `(S1)` at once.

**This closes the family as a source of counterexamples.**  A bounded
counterexample to `affine-orientation-glue-lemma` built from these pieces
would be a normalization `lambda * sum_{b in B} c_b B_{b,r}` with sup norm
at most 1 and every quotient dictator coefficient at least some fixed
`delta > 0` independent of `k`.  By `(S2)` that forces
`delta <= |B|^(-1/2)`, so on a direction set of density `alpha` the
coefficients are at most `(alpha(N-1))^(-1/2) -> 0`.  No sign pattern, no
choice of weights, and no positive density of directions escapes it.

The external dossier that opened this region observed only that the
all-ones superposition is unbounded and that saturating it by `tanh`
destroys the finite-degree description, leaving open whether some cleverer
normalization works.  It does not, and `(S1)` is the reason: the whole
**linear span** of the pair memorizers is closed.  Any counterexample must
be genuinely nonlinear in them, which is where boundedness and noise are
forced to do work no `L^2` or degree bookkeeping can do.

The proof is `memorizer-superposition-sup-norm-proof`.
