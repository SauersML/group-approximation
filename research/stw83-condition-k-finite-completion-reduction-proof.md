---
rg: 2
id: stw83-condition-k-finite-completion-reduction-proof
kind: route
title: Use Condition-(K) entrance completions and inductive-limit permanence
target: stw83-condition-k-finite-completion-reduction
requires: []
---

Faurot--Schafhauser, Proposition 2.3 and Theorem 2.4 in the 2026 revision of
[Nuclear dimension of graph C*-algebras with Condition (K)](https://arxiv.org/abs/2310.15073),
give the construction.  Starting from a finite subgraph, first add two return
paths at every relevant cyclic vertex so that Condition (K) is retained.  Then
add every edge of `E` received at a receiver already present.  Row-finiteness
makes this completion finite, and the last closure condition makes the graph
relations agree with those in `C*(E)`.  Since every vertex projection remains
nonzero and the completion has Condition (K), the Cuntz--Krieger uniqueness
theorem makes the canonical map into `C*(E)` faithful.

Exhausting the countable edge and vertex sets and repeating the completion gives
an increasing union containing every canonical generator, hence the asserted
inductive limit.  Winter--Zacharias, Proposition 2.3, gives

```text
dim_nuc(direct_limit_n C*(E_n))
    <= liminf_n dim_nuc(C*(E_n)).
```

No extension estimate is used in this final step, so the uniform constant `d` is
not enlarged.
