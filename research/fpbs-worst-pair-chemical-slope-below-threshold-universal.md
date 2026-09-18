---
rg: 2
id: fpbs-worst-pair-chemical-slope-below-threshold-universal
kind: claim
title: On every nonamenable Cayley graph some t above p_c joins the critical worst pairs, given connection, by open paths of slope below log gr over log(t/p_c)
distinct_from:
  fpbs-worst-pair-connectivity-rate-positive-above-pc-universal: that is kernel (K), gamma(t) > 0; this is a conditional chemical-length statement at the p_c-minimisers that implies (K) by an established inequality, and can fail while (K) holds
  fpbs-uniform-chemical-stretch-above-pu: that is an unconditional linear stretch bound for all pairs above p_u; item 5 of fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff shows every unconditional stretch constant is at least log gr / log(t/p_c), so no unconditional stretch bound can reach this threshold
  fpbs-integrated-sensitivity-iff-subscale-chemical-saturation: that (SE) asks walk-averaged chemical slope o(1/epsilon) for all small epsilon; this asks slope below about p_c log(gr)/epsilon for one pair per radius at a single t
---

**OPEN (kernel CS).** Notation as in
`fpbs-worst-pair-critical-rate-and-chemical-slope-tradeoff`. For every Cayley
graph of a finitely generated nonamenable group there is `t in (p_c,1)` with

```text
l(t) log(t/p_c)  <  log gr .
```

Unpacked: for some `L < log(gr)/log(t/p_c)` and infinitely many `n`, some
`v_n in B_n` minimising `tau_(p_c)(o,.)` on `B_n` has
`P_t(d_omega(o,v_n) <= Ln | o <-> v_n) >= e^(-o(n))`.

**What it gives.** Item 3 of the tradeoff claim gives `gamma(t) > 0`, which is
kernel (K), and so `p_c < p_u`. The route is
`fpbs-worst-pair-rate-via-chemical-slope`.

**Why it is not (K) in disguise.**

- (CS) fails on any graph where the critical worst pairs are joined, given
  connection, only by long detours, even if `gamma(t) > 0` for other reasons.
  An example would be exponentially rare connections that are nevertheless
  long.
- The threshold is sharp: on `T_d` the tradeoff is an equality with `l = 1`.

**Invariant forced on any proof.** At `L < log(gr)/log(t/p_c)`, the tradeoff
proof gives the unconditional bound

```text
P_t(d_omega(o,v_n) <= Ln)  <=  (t/p_c)^(Ln) gr^(-n) ,
```

which is exponentially small. So (CS) is a statement about exponentially rare
connections: a proof must show that *given* the rare event `o <-> v_n`, a
short route is not much rarer.

**Class killed.** Every argument that bounds `P_t(d_omega <= Ln)` from below
without conditioning. This includes:

- linear stretch constants;
- (UCS);
- renormalised or sprinkled constructions of short paths that succeed with
  probability bounded below or `e^(-o(n))`.

Such arguments cannot reach the threshold. Item 5 of the tradeoff claim is the
precise form of this.

**Heuristic, not established.** In mean-field geometry an open path of
extrinsic length `xi ~ epsilon^(-1/2)` has chemical length `xi^2 ~ epsilon^(-1)`.
That suggests a conditional slope of order `epsilon^(-1/2)`, far below the
threshold `p_c log(gr)/epsilon` at `t = p_c + epsilon`. By item 4 of the
tradeoff claim, a collapse `p_c = p_u` must break this by a full factor
`epsilon^(-1/2)` on the critical worst pairs.

## Attempts

1. **Monotone coupling from `p_c` (2026-09-18, swarm-0917-w7-w7-bs-follow;
   dies as circular).**
   - *The bound.* `omega_(p_c) ⊆ omega_t` gives
     `s_t(v,R) >= s_(p_c)(v,R) tau_(p_c)(o,v)/tau_t(o,v)`. So a short critical
     slope, `s_(p_c)(v_n,Ln) >= e^(-o(n))`, gives (CS) as soon as
     `tau_t(o,v_n) <= e^(o(n)) tau_(p_c)(o,v_n)`.
   - *Where it dies.* That last condition gives `gamma(t) >= gamma(p_c)`,
     which is stronger than (K). The factor `tau_(p_c)/tau_t` is exactly the
     quantity (K) controls, so this attack cannot be the whole proof.
   - *What survives.* (CS) needs a conditional statement *at level `t`*: given
     `o <-> v_n` at `t`, a short route is not much rarer. Passing through
     level `p_c` loses this.
