---
rg: 2
id: fpbs-green-visit-criterion-universal
kind: claim
title: On every nonamenable Cayley graph an independent walk makes finitely many expected visits to its own cluster at some supercritical parameter
distinct_from:
  fpbs-pivotal-nonconcentration-universal: that asks for exponential decay of a_n at some p above p_c (lambda_L<1); this asks only that sum_n a_n(p) be finite, which also allows lambda=1 with summable decay, and NC implies it.
  fpbs-pivotal-budget-universal: that is a pointwise linear pivotal budget at every walk length; this has no pivotal or derivative content, and PB implies it.
  fpbs-nonamenability-bounds-critical-connectivity-operator: that asks for an l2-bounded connectivity operator; this needs only the linear pairing sum_x g(x) tau_p(x) with the l2 Green function to be finite, which tau_p in l2 already implies.
  fpbs-benjamini-schramm-universal: that is nonuniqueness at some p above p_c; this is a quantitative certificate for it, and no converse is known.
---

OPEN. Let `G=Cay(Gamma,S)` be nonamenable, `X_n` the simple random walk
independent of Bernoulli bond percolation, and `a_n(p)=P_p(e<->X_n)`. Prove
that some `p>p_c(G)` has

    A(p) = sum_(n>=0) a_n(p) = sum_x g(x) tau_p(x) = E #{n : X_n in C(e)} < infinity,

where `g` is the Green function. The lazy walk gives exactly `2A(p)`, so the
choice of walk does not matter. At `p=p_c`, `A <= 1/(1-rho)` by Schramm's
lemma. At every uniqueness parameter, `A=infinity`.

Placement, from Theorem 3.1 of
`research/artifacts/fpbs/docs/green-visit-kernel-2026-09-17.md`:

* PB implies GB, which implies this claim.
* NC implies this claim, and so does IS through NC.
* `p_c<p_(2->2)` implies GB, which implies this claim.
* `tau_p in l2` for some `p>p_c` implies this claim.
* This claim implies BS.

So it is the weakest kernel on the tip. A single nonamenable Cayley graph
where it fails would refute PB, IS, NC and `p_c<p_(2->2)` on that graph at
once. Equivalently, the claim says `p_A>p_c` for `p_A=sup{p : A(p)<infinity}`.

## Attempts

* **Continuity from the critical value (swarm-0917).** We have
  `A(p_c)<infinity`. Each `tau_p(x)` is right-continuous at `p_c`: it is the
  limit of the finite-ball `tau^R_p(x)`, and the error is at most
  `P_p(e<->boundary of B_R)`, which tends to `theta(p_c)=0`. So every finite
  truncation `sum_(|x|<=r) g(x) tau_p(x)` is right-continuous.
  - **Where it dies:** passing to `A(p)` needs the tail
    `sum_(|x|>r) g(x) tau_p(x)` to be small uniformly in `p in [p_c,p_c+eps]`.
    That is a quantitative uniform integrability estimate, and it is exactly
    what GB supplies through Russo.
  - `A` is only lower semicontinuous (a supremum of polynomials), so it can
    jump to `+infinity` immediately above `p_c`. Soft arguments of this kind
    are already ruled out by the soft-collapse families.
  - The linear pairing with the `l2` function `g` does not avoid this. A
    Russo bound on `A'` at `p_c` passes through `<g, tau*A*tau>`, which is
    controlled only by `||T_(p_c)||`, the critical l2 hypothesis. Beating it
    needs a bound on the Green-tilted pivotal count that does not go through
    the BK bubble.
