---
rg: 2
id: high-degree-range-mass-is-exactly-tracial-ucp-liftability
kind: claim
title: Vanishing supercritical range mass is exactly coordinate ucp liftability
distinct_from:
  finite-range-block-mass-upgrades-diverging-positivity-to-ucp: that proves the nontrivial forward implication by replacing the supercritical blocks; this records the converse and hence the exact logical strength of the proposed Maslov condition.
  maslov-diverging-positive-lifts-have-vanishing-high-degree-mass: that is the open Maslov specialization; this is an unconditional equivalence for every finite-dimensional operator system and every tracial matrix quotient map.
---

Let `S` be a finite-dimensional operator system and let

```text
Theta:S -> prod_omega M_(d_n)
```

be ucp.  The following are equivalent.

1. `Theta` has coordinate ucp lifts `psi_n:S->M_(d_n)`.
2. There are integers `k_n->_omega infinity` and unital `k_n`-positive
   coordinate lifts `phi_n` of `Theta` such that, on writing

   ```text
   C^*(phi_n(S))=direct_sum_j(M_(r_(n,j)) tensor I_(m_(n,j))),
   ```

   the normalized trace mass of the blocks with `r_(n,j)>k_n` tends to
   zero along `omega`.

Thus `(MH1)` is not a weaker arithmetic proxy for the desired Maslov
generator ucp lift.  It is an exact reformulation of that liftability
assertion.  A proof of `(MH1)` still closes the Maslov route, but it must do
all of the genuinely nonamenable-to-amenable work of constructing the ucp
lift; character rigidity alone cannot make the reformulation easier.

