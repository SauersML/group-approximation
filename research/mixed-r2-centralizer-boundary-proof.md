---
rg: 2
id: mixed-r2-centralizer-boundary-proof
kind: route
title: Substitute the private R2 cell and apply twisted Schreier properness
target: mixed-r2-boundary-is-one-finite-mark-centralizer-commutator
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Since `d=t_1t_0^(-1)`, one has `t_1=dt_0`.  Substitute this into the mixed
boundary and then replace `r^(-1)` using the private triangle:

```text
w=t_0^(-1)d^(-1)s_0dt_0r^(-1)
 =_q t_0^(-1)d^(-1)s_0d s_0^(-1)t_0.
```

This is `(MRB2)`.  Adding or deleting a diagram for `q` changes minimal area
by at most `A_0`, in either direction, proving `(MRB3)`.  When both boundaries
are trivial, `(MRB2)` says `d^(-1)s_0d=s_0`, so `d` centralizes the finite
mark `s_0`.

Conjugation by `g^(-1)` sends `s_0=b^g` to `b` and `d` to `dbar`.
Conjugating a van Kampen diagram preserves its number of cells.  Apply
`finite-mark-centralizer-commutator-area-is-proper` to the fixed word for
`b` and the word for `dbar`, then absorb the `A_0` private-cell cost.  This
is `(MRB5)`.

Finally, under one common conjugation of a fixed local diagram,
`d=(a_1a_0^(-1))^g`, so `(MRB6)` follows.  Its Schreier distance is constant,
showing exactly why properness rules out the separated escaping construction
but not an interacting fixed-local cancellation.

For `(MRB7)`, `t_1=(j q)` has support disjoint from `(i p)=s_0`, so it
centralizes `s_0`.  Cancelling `t_1^2` gives `(MRB8)`.  The two transpositions
`(i p)` and `(p q)` share exactly `p`, and their product is a three-cycle.
This proves the asserted nontriviality of the canonical mixed boundary.

