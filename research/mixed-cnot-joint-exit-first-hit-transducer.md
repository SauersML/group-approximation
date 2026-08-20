---
rg: 2
id: mixed-cnot-joint-exit-first-hit-transducer
kind: claim
title: Select the mixed-CNOT joint exit event into one E5 first-hit layer
distinct_from:
  mixed-central-cnot-completes-relative-rank-one-router: that produces exact equal active/exit halves and flag transport inside one finite packet; this must select only the joint violating exit half globally.
  hard-sign-transport-captures-exit-mass: that transports a projection already known to lie in one negative hard-sign sector; this must manufacture the appropriate target hard sign without also charging allowed or active sectors.
  robust-rank-one-endpoint-marginal-floor: that gives the quantitative failure floor once three endpoint-sharing transports exist; this must realize those transports by group words and bound their failures by relator energy.
  projected-hard-sign-bridge-selects-joint-exit: that already transports the joint exit after analytic right compression; this must additionally return the complementary active carrier.
---

For the mixed-central router on the marked carrier `Q=(I-J)/2`, write

```text
F=(I-K)/2,       X=F(I-b)/2,       A=I-X.              (MCF1)
```

Here `X` is exactly the violating exit half and `A` contains every allowed
`K=+1` sector together with the violating active half.  Construct a finite
group-word atlas, compatible with the product Fanizza/E5 clock, such that in
every sufficiently accurate normalized-HS microstate:

1. `A` returns to the next active carrier with only polynomial fixed-word
   drift;
2. `X` is transported into the next previously-undetected E5 hard layer;
3. the allowed sector `(I-F)(I-b)/2` is returned, not charged as an exit;
4. the three router contexts share their two endpoint flag marginals, and the
   sum of their contextual failure masses is bounded above by a fixed sparse
   sum of group-relator energies.

Then `robust-rank-one-endpoint-marginal-floor` and `(MCR5)` give a local exit
lower bound `tau(QF)/2-O(sqrt(E))`, while the active/exit partition gives the
upper source budget.  The E5 first-hit theorem supplies summability across
levels.  Combined with the factored C18 branch ledger, this is the remaining
finite-dimensional theorem needed before the final HS floor.

## Falsification boundary

- A bridge using only the sign `b` is false: it also sends allowed
  `K=+1,b=-1` characters to the reservoir.
- A bridge using only `K` is false: it sends both equal violating halves and
  destroys the active copy.
- Replacing `(MCF1)` by a scalar group word is the affine controlled-phase
  barrier in another guise.  The atlas must use the three endpoint contexts
  and rank-one marginal obstruction, or an explicitly equivalent
  non-Bass--Serre mechanism.
- The allowed exact model must extend with zero energy.  A candidate that
  deletes its `K=+1,b=-1` character fails finite-group induction and is not a
  solution.

## Attempts

- The single-sign bridges `K` and `b` fail for the two separate reasons above.
- The live attack is the three-context flag atlas in
  `mixed-cnot-joint-exit-first-hit-transducer-via-endpoints`; it is blocked
  only on `mixed-cnot-endpoint-failure-relator-certificate`.
- A strictly smaller alternate route is now available.  The exit half itself
  is closed by `projected-hard-sign-bridge-selects-joint-exit`; the only open
  clause on that route is `mixed-cnot-allowed-active-return`.
