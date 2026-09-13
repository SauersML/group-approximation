---
rg: 2
id: selfless-real-rank-zero-iff-dense-k0-traces
kind: claim
title: A selfless tracial C*-algebra containing an element with atomless spectral measure has real rank zero iff its K_0 trace image is dense
distinct_from:
  selfless-projection-traces-equal-k0-trace-image: that computes the set of projection traces; this decides real rank zero from that set, through the Dykema--Rørdam comparison theorem.
  robert-tracial-selfless-regularity: that gives stable rank one and strict comparison; this adds the real rank dichotomy that those properties control.
---

**ESTABLISHED** by `selfless-real-rank-zero-iff-dense-k0-traces-proof`.

Let `(A, τ)` be a selfless C\*-probability space with `τ` a faithful trace.
1. If `τ_*(K_0(A))` is dense in `R`, then `RR(A) = 0`.
2. Conversely, suppose `A` contains a self-adjoint `x` whose spectral measure `μ_x` has no atoms and has an
   interval as support. If `RR(A) = 0`, then the projection traces of `A` are dense in `[0,1]`. So
   `τ_*(K_0(A))` is dense.

For `A = C*_r(Γ)` with `Γ` torsion-free and nontrivial, the element `x = λ(g) + λ(g)^*` qualifies for any
`g ≠ e`. Since `g` has infinite order, `μ_x` is the arcsine law on `[-2,2]`.

**Credit.** Item 1 is Dykema--Rørdam, *Projections in free product C\*-algebras, II*, Math. Z. 234 (2000),
Theorem 1.5(i). Their comparison hypotheses are supplied by Robert's strict comparison, their stable rank
hypothesis by Robert's Theorem 3.1(ii), and their density hypothesis by
`selfless-projection-traces-equal-k0-trace-image`. Item 2 is an elementary perturbation estimate. The
introduction of Dykema--Rørdam II records the necessity of small projections for simple algebras.
