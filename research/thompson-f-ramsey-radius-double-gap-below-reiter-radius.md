---
rg: 2
id: thompson-f-ramsey-radius-double-gap-below-reiter-radius
kind: claim
title: In Thompson's F, the coarse Reiter radius is not bounded by any bounded tower wrapped around two compositions of the Ramsey function (RGAP₂)
distinct_from:
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that is ¬AMP, about the fine function R̃; this compares only the precision-1/2 Ramsey radius R with the coarse Reiter radius CR, and implies ¬AMP by Corollary 3 of thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap.
  thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap: that is the established sandwich RGAP₂ ⇒ ¬AMP ⇒ RGAP₁; this is its strong end, left open.
  thompson-f-folner-function-exceeds-every-tower: that says CR is not elementary; this says CR is not elementary even relative to two compositions of R, which is a statement about R being small.
---

**OPEN.** Notation is as in `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`: `R = R_{F,{x_0,x_1}}`, `CR` is
the coarse Reiter radius, and values lie in `[0, ∞]`.

**Statement (RGAP₂).** For every integer `D ≥ 0` there is an integer `M ≥ 1` with

`CR(M) > exp_D(R(exp_D(A + 4M)) + 4M)`, where `A = exp_D(R(exp_D(4M+1)) + 4M)`.

**Consequences.** It implies ¬AMP (`thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`), and hence
that F is amenable. This is Corollary 3 of the sandwich.

**Why it is a genuine reformulation.** It mentions neither `R̃` nor any precision other than 1/2 and 1. It asks
that, in F, "every 2-coloring of `B_n` is balanced by some measure" be reachable at radii non-elementarily smaller
than "one measure is moved by at most 1 by all of `B_M`", even after composing the former twice. This is a
quantifier-exchange problem, `∀E ∃ν` against `∃ν ∀E`, with no amplification left in it. The weaker end, RGAP₁,
is necessary for ¬AMP. So if some fixed tower bounds `CR` in terms of `R ∘ exp_E`, the whole Ramsey-amplification
route is dead.

## Attempts
