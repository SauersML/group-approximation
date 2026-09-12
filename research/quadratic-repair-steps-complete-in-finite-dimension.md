---
rg: 2
id: quadratic-repair-steps-complete-in-finite-dimension
kind: claim
title: Three-halves repair steps with summable padding terminate in one finite matrix algebra
distinct_from:
  quadratic-descent-loss-is-admissible-linear-is-not: that accounts for the loss rate of a dimension-reducing operation against a fixed threshold; this accounts for a dimension-increasing repair iteration and proves it stops, converges, and yields a modulus.
  flexible-hs-metric-controls-words-and-padding: that supplies the metric facts -- word Lipschitz constants, the dimension charge, and the sharp upward-repair factor; this is the iteration built on top of them.
  second-order-step-beats-a-blocked-linearization: that produces one step of rate three halves from a neutral direction; this assumes such steps and shows what an infinite sequence of them adds up to.
artifacts:
  - research/artifacts/pde-transfer-quadratic-repair-2026-09-08.md
---

**ESTABLISHED.**  Let `C` be a class of unitary tuples closed in each fixed
dimension and closed under adding trivial summands, with defect
`e(U) = max_(w in W) ||w(U) - I||_(2,d)` for a
finite set `W` of words of length at most `L` (or any defect that is
`2L`-Lipschitz in the zero-padding metric `d_0`).  Suppose there are constants
`A, B` and a threshold `eps > 0` such that for **every** tuple `U` in `C` of
dimension `d` with `e(U) <= eps` there is a tuple `U^+` in `C` of dimension
`d + r` with

```text
(a)  e(U^+) <= A e(U)^(3/2),
(b)  max_s d_0(U_s^+, U_s) <= B sqrt(e(U)),
(c)  r <= B e(U) d.                                                     (RB1)
```

Then for every `U^(0)` in `C` with

```text
e_0 = e(U^(0)) <= min( eps, 1 / (4 A^2) )
```

there is an **exact** tuple `U^(inf)` (all words in `W` equal to the identity)
in a single finite dimension `D <= d_0 exp(2 B e_0)`, with

```text
max_s d_0( U_s^(0), U_s^(inf) ) <= (B / (1 - 2^(-1/2))) sqrt(e_0)
                                <= 3.42 B sqrt(e_0).                    (RB2)
```

Consequently the distance from `U^(0)` to the exact locus obeys the modulus

```text
D(U) <= f(e(U)),    f(x) = min( K sqrt x, 2 ),                          (RB3)
K = max(3.42 B, 2 / sqrt(tau)),   tau = min(eps, 1/(4A^2)).
```

for every input whenever the exact locus is nonempty. The enlarged
constant makes `f(x)=2` above the threshold `tau`, and
`lim_(x -> 0) f(x) = 0`. Take `A,B>0` without loss of generality.

**What is load-bearing.**  Hypothesis `(RB1)` must hold at every tuple of the
class, in particular at the outputs of its own steps, with the *same* constants;
a per-stage estimate that degrades from one stage to the next gives none of
this.  The padding clause `(c)` is what makes the dimensions summable, and
integrality is what makes them stop.  Nothing here supplies `(RB1)` for any
group.
