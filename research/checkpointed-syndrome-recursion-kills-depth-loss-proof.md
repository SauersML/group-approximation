---
rg: 2
id: checkpointed-syndrome-recursion-kills-depth-loss-proof
kind: route
title: Iterate the backward estimate only as far as the next checkpoint
target: checkpointed-syndrome-recursion-kills-depth-loss
requires: []
---

Put `q = c - t <= r` and iterate (BSR) `q` times.  Induction on `q`: the case
`q = 0` is trivial, and

```text
b_t <= L e_t + L b_(t+1)
     <= L e_t + L ( sum_(j=0)^(q-2) L^(j+1) e_(t+1+j) + L^(q-1) b_c )
     =  sum_(j=0)^(q-1) L^(j+1) e_(t+j) + L^q b_c.
```

Every exponent `j+1` in the sum satisfies `j+1 <= q <= r`, and `L >= 1`, so
each coefficient is at most `L^r`.  The tail term is `L^q b_c <= L^r A e_c`
by (CKP).  Adding the two gives (CK1).

Reading (CK1) as a local charge: set `L' = L^r max(1,A)` and
`N(t) = {t, t+1, ..., c}`, of cardinality at most `r+1`.  Then
`b_t <= L' sum_(s in N(t)) e_s`, and each layer index `s` lies in at most
`r+1` of these windows because the windows are intervals of length at most
`r+1` indexed by their left endpoint.
