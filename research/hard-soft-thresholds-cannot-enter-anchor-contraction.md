---
rg: 2
id: hard-soft-thresholds-cannot-enter-anchor-contraction
kind: claim
title: Hard-tail replacement and quadratic soft anchoring demand incompatible thresholds for contraction
invalidates: [hard-tail-soft-anchor-multiscale-centralization]
distinct_from:
  operator-tail-contraction-misses-uniform-diffuse-matching: that shows the scalar tail recurrence is vacuous on a uniform profile; this proves the quantitative exponent conflict after adding hard replacement and the optimistic quadratic anchor estimate.
  sparse-anchor-odd-fourth-moment-is-the-renormalization-gate: that asks for an operator-valued fourth-moment estimate; this shows that a scalar q-tail cutoff cannot supply the relative smallness needed by that estimate.
  sparse-pauli-pair-defeats-random-order-blr: that shows sparse errors amplify under a full-table construction; this audits a direct hard-repair-then-anchor iteration without constructing a BLR table.
---

ESTABLISHED as a no-go for the scalar-threshold proof architecture.  Let

```text
E=(1/L)sum_i q_i^2,       U_t={i:q_i>=t}.                 (HST1)
```

Suppose coordinates in `U_t` are replaced at unit squared cost and the low
core is passed to a one-anchor Newton step.  Markov gives only

```text
hard_cost <= C |U_t|/L <= C E/t^2.                       (HST2)
```

Therefore vanishing accumulated hard-repair cost requires

```text
t/sqrt(E) -> infinity.                                   (HST3)
```

Now grant the soft step more than the established scalar cutoff actually
provides: assume every anchor-odd part on the retained core has operator norm
at most `t`.  The exact quadratic formulas in
`one-anchor-grading-makes-parity-damage-quadratic` then bound the normalized
nonlinear remainder by the optimistic scale

```text
soft_remainder <= C t sqrt(E)                            (HST4)
```

(and the cruder fourth-moment estimate gives `C t^2`).  To perturb a linear
step with fixed contraction `1-gamma`, one needs the remainder to be `o(E)`.
Even `(HST4)` therefore requires

```text
t/sqrt(E) ->0,                                            (HST5)
```

which contradicts `(HST3)`.  For a power schedule `t=E^alpha`, hard repair
requires `alpha<1/2`, while relative quadratic control requires
`alpha>1/2`.  No logarithmic correction repairs opposite strict limits at
the endpoint.

The all-local-dual scalar recurrence does not change this conclusion.  It
has the direction

```text
|U_((w-1)t+2rho)| <=lambda |U_t|+bad_floor,              (HST6)
```

so it contracts a tail only after **raising** the threshold.  It supplies no
upper bound on `|U_t|` when `t<<sqrt(E)`.  The admissible scalar profile
`q_i=sqrt(E)` for every `i` makes `U_t` equal to all coordinates throughout
that range, where the small-set hypothesis of `(HST6)` is false.  Starting
at `t>>sqrt(E)` makes hard replacement cheap, but every threshold generated
by `(HST6)` is still larger and hence moves farther from `(HST5)`.

The bad-row parameter has the same orientation.  Markov on parity defects
requires `rho` above their RMS scale to make the bad-row floor small, while
the update adds `2rho` to the next threshold.  It cannot create a descending
path into the soft basin.

This does not rule out a nonlinear rounding modulus.  The absolute
bookkeeping expression

```text
E/t^2+t sqrt(E)
```

does tend to zero, for example at `t=E^(1/4)`.  But the second term is then
larger than `E`, so it cannot be iterated as a contraction, and no existing
theorem turns that one-step absolute residual directly into an exact common
PVM.  Such a terminal theorem would itself solve
`multiplicity-space-centralization-after-code-block-pinching`.  Thus scalar
threshold scheduling alone does not prove it; progress requires an
operator-valued stopping inequality which makes the sparse quadratic
remainder `o(E)` **without** imposing `t<<sqrt(E)` on the same cutoff used
for hard repair.

