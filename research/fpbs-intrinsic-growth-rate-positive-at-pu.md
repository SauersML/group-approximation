---
rg: 2
id: fpbs-intrinsic-growth-rate-positive-at-pu
kind: claim
title: On every nonamenable Cayley graph with p_u < 1, expected intrinsic balls grow exponentially at p_u with a rate that is uniform in the radius
distinct_from:
  fpbs-benjamini-schramm-universal: that is p_c < p_u; this implies it through fpbs-universal-intrinsic-l2-rate-route. It would be equivalent to it if lambda_1 > 0 on (p_c,1], which is expected from anchored expansion of supercritical clusters but is neither imported nor proved in the graph
  fpbs-intrinsic-l2-rate-bounded-below-above-pu: that is the l2 rate Lambda(p_u) > 0, which sees uniqueness and is strictly stronger than this l1 statement
  fpbs-supercritical-finite-susceptibility: that bounds finite clusters from above for p > p_c; this is a lower bound on all clusters at p_u, and the finite-cluster part contributes at most chi^f to it
---

**OPEN.**

Notation as in `fpbs-intrinsic-l2-rate-closed-zero-set`:
`lambda_1(t) = lim_R R^(-1) log E_t|B^int_R(o)| = inf_R R^(-1) log E_t|B^int_R(o)|`.

**Claim (IL1).** Let `G` be a Cayley graph of a finitely generated nonamenable
group with `p_u(G) < 1`. There is `delta > 0` such that
`E_(p_u)|B^int_R(o)| >= e^(delta R)` for every `R >= 1`. Equivalently
`lambda_1(p_u) > 0`, or `p_lambda1 < p_u`, or `inf_(t>p_u) lambda_1(t) > 0`.

The equivalences follow from items 1, 2 and 5 of the ESTABLISHED
`fpbs-intrinsic-l2-rate-closed-zero-set`.

**Status as a prerequisite.** (IL1) is the weakest of the three sufficient
conditions in the chain

```text
(UCS) fpbs-uniform-chemical-stretch-above-pu
  => (IL2) fpbs-intrinsic-l2-rate-bounded-below-above-pu
  => (IL1) this claim
  => p_c < p_u.
```

(IL1) is not believed to be much stronger than the flagship statement itself.
If every infinite cluster at every `t > p_c` has exponential intrinsic growth,
then `p_lambda1 = p_c` and (IL1) is equivalent to `p_c < p_u`. That hypothesis
is expected from the anchored expansion theorems for supercritical clusters on
nonamenable graphs, but no verbatim citation has been imported. The two
stronger conditions are the ones that can fail even on graphs that have a
window.

## Attempts

1. **Via the l2 rate and uniform chemical stretch (2026-09-17).** See
   `fpbs-intrinsic-growth-rate-via-l2-rate` and
   `fpbs-uniform-chemical-stretch-above-pu`, Attempts.
