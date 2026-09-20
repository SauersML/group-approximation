---
rg: 2
id: fpbs-superset-pu-certificate-fails-on-237-triangle-group
kind: claim
title: One Remove move can push p_c of the subset above p_u of the gapped superset, so no Remove-step proof can pass through p_u of the superset
distinct_from:
  fpbs-gap-survives-product-generator-moves: that is the move-invariance claim, still OPEN, and its Remove half holds on this example; this refutes the sufficient condition p_c(T minus t) < p_u(T), which every recorded Remove-step certificate proves, and names the invariant that kills it.
  fpbs-lossless-move-comparison-fails-marginal-transfer: that refutes the marginal form of one comparison on the amenable move Z^2 to triangular and bounds its window by exponent 2; this is a nonamenable, gapped move where the target inequality p_c(S) < p_u(T) of every such comparison is false outright, by a margin of 0.03.
  fpbs-generating-set-threshold-comparison: that proves p_u(S) >= p_u(T) and power-map bounds for one move; this shows the inequality p_u(S) >= p_u(T) can be strict by a definite amount on the gapped Remove move, so p_u(T) is not a usable lower bound for p_u(S).
  fpbs-bs-planar-transitive-dual-threshold-identity: that is the imported planar duality theorem; this applies it to one explicit non-regular Cayley graph and adds a cactus-cover lower bound for p_c of the subset.
artifacts:
  - experiments/fpbs-superset-pu-certificate-2026-09-17/check.py
  - experiments/fpbs-superset-pu-certificate-2026-09-17/output.txt
---

**ESTABLISHED.** Proof in `fpbs-superset-pu-certificate-fails-on-237-triangle-group-proof`.

**Setting.** Let `Delta = <x, y | x^2, y^3, (xy)^7>` be the `(2,3,7)` triangle
group. Put

```text
S = {x, y, y^-1},        T = S ∪ {xy, (xy)^-1},        t = xy = uv with u = x, v = y.
```

So `T -> S` is one Remove move of `fpbs-gap-survives-product-generator-moves`:
`t ∈ T` and `u, v ∈ T \ {t, t^-1}`. Both Cayley graphs are transitive,
nonamenable, planar and one-ended, so both are gapped by
`fpbs-bs-planar-transitive-dual-threshold-identity`. In particular `T` is a
gapped superset.

**Theorem.**

```text
p_u(Cay(Delta,T)) <= 1 - 1/lambda = 0.606667... < 0.637277... = p* <= p_c(Cay(Delta,S)).
```

Here `lambda = 2.542374...` is the Perron root of the non-backtracking type
matrix of the planar dual of `Cay(Delta,T)`, and `p*` is the root in `(0,1)` of
`2p^2(1 + p - p^2) = 1`. In particular

```text
(R*)  p_c(T \ {t, t^-1}) < p_u(T)
```

fails on a gapped `T`, and `p_u(S) - p_u(T) >= p* - (1 - 1/lambda) > 0.0306`.

**What it kills.** `(R*)` is the sufficient condition for the Remove half that
the recorded threshold-comparison certificates prove:
- the power-map window of `fpbs-generating-set-threshold-comparison`
  (`p_c(T) < phi(p_u(T))` forces `p_c(S) < p_u(T)`);
- the lossless comparison (LL) with its window
  (`fpbs-lossless-move-comparison-fails-marginal-transfer`, Theorem C).

Each of these combines an upper bound on `p_c(S)` with the established
`p_u(S) >= p_u(T)`. The spectral margin certificate is intrinsic to each set
and is not of this form. It has its own recorded death, at `m(S) <= 0`. `(R*)`, applied along the Remove-only chain, would give
`fpbs-benjamini-schramm-universal`. The theorem shows that `(R*)` is false,
even on a planar hyperbolic group where the goal is known. So the whole class
of proofs of the form "upper-bound `p_c(S)` by data of `T`, then compare with
`p_u(T)`" is dead.

- **Invariant:** the dual threshold `p_c(T†) = 1 - p_u(T)`. The seven
  `xy`-chords inside each 14-gon face of `Cay(Delta,S)` cut it into one
  heptagon and seven triangles. That drops the dual degrees from 14 to at most
  7, and so raises `p_c` of the dual above `1 - p_c(S)`.
- **Failing step:** the inequality `p_u(S) >= p_u(T)`, used as the lower bound
  for `p_u(S)`.

Any proof of the Remove half must lower-bound `p_u(S)` intrinsically: through
`S`'s own dual or uniqueness structure, not through the superset.

**Scope.** This does not refute the Remove half. By the imported planar
theorem, `p_c(S) < p_u(S)` holds here. It shows that the gap of `S` sits
entirely above `p_u(T)`: both thresholds jump under the move, and the old
window `(p_c(T), p_u(T))` and the new window `(p_c(S), p_u(S))` are disjoint.
