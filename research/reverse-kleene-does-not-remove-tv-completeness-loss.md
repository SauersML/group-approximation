---
rg: 2
id: reverse-kleene-does-not-remove-tv-completeness-loss
kind: claim
title: Reverse Kleene cannot turn Taller--Vidick near-completeness into algebraic survival of J
artifacts:
  - research/artifacts/taller-vidick-reverse-kleene-endpoint-audit-2026-08-21.md
distinct_from:
  perfect-completeness-constant-soundness-lcs-compiler: that asks for the missing exact LCS compiler; this proves that self-reference does not exactify the published positive-noise presentation.
  halt-now-certificate-area-still-needs-a-crossing-envelope: that is the general moving-window matrix-microstate firewall; here the positive-noise Taller--Vidick presentation has an explicit two-equation certificate J=1 on every input.
  threshold-free-reverse-kleene-higman-diagonal: that works because HALT gives qualitative algebraic survival of the mark; Taller--Vidick gives only one near-perfect strategy and its positive-noise mark is algebraically trivial.
---

Apply the recursion theorem to a machine which searches for a formal proof
that the distinguished central involution `J` is trivial in its own
positive-noise Taller--Vidick output solution group. The hoped-for argument
would use failure to halt to infer `J!=1`, then combine this with NONHALT
soundness.

The hoped-for branch never occurs. By
`taller-vidick-positive-noise-collapses-central-sign`, every such output
contains an explicit two-equation proof of `J=1`: for a folded query `f`,
the two full-support masks `mu=f` and `mu=-f` give the same left-hand side
and opposite parity signs. The proof enumerator therefore halts on every
input, including its fixed point. This is independent of the source BCS and
of the repetition count.

There is no contradiction with near-perfect completeness. A derivation
`D` of `J=1` gives a computable, presentation-and-weight-dependent number
`gamma(D)>0` such that every finite-dimensional strategy has value at most
`1-gamma(D)`: telescope the approximate solution-group relators along
`D` and use the standard LCS strategy-to-approximate-representation
estimate. On a halting input Taller--Vidick also provide a strategy of value
at least `1-epsilon`. Hence necessarily

```text
gamma(D) <= epsilon.                                    (TVK1)
```

For the explicit two-mask certificate this is visible directly: its
weighted gap is controlled by the probabilities of the rare masks
`mu=f` and `mu=-f`. Thus the desired strict reverse inequality
`epsilon<gamma(D)` is not merely unproved for this certificate; it is
incompatible with the honest strategy.

If the self-referential machine instead waits only for proofs whose
quantitative gap exceeds `epsilon`, its failure to halt no longer implies
`J!=1`: the algebraic two-equation proof still exists, but does not satisfy
the extra numerical filter.

The paper's noise parameter cannot be sent algebraically to zero. For every
`epsilon>0` its Bernoulli mask has full support on all mask functions,
whereas at `epsilon=0` the support collapses to the single constant-one
mask. The two-mask certificate disappears only because the presentation
changes. At the same time the published decoder's factor
`4 epsilon delta^2` vanishes, and the main theorem chooses a repetition
count `u=u(epsilon)`.

For fixed `(u,B,pi)`, the support is constant throughout positive noise;
`taller-vidick-positive-noise-fixed-support-reweighting` records the
reweighting and weighted-certificate estimates. Reweighting cannot repair
completeness because it leaves the two contradictory parity equations in
the support. Deleting them reaches a different zero-noise presentation and
loses the published decoder.

Therefore a reverse-Kleene upgrade needs genuinely new finite equations or
a new zero-noise decoder. It does not follow from
`LIN*_(1-epsilon,s)=RE`. The earlier source audit is retained in
`taller-vidick-reverse-kleene-endpoint-proof`.
