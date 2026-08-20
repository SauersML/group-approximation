---
rg: 2
id: finite-window-hs-tests-ignore-low-rank-generator-surgery
kind: claim
title: Fixed normalized-HS word tests are blind to vanishing-rank generator surgery
---

Let `A` be a finite alphabet and let `(U_a)_(a in A)` and `(V_a)_(a in A)`
be unitary `d x d` matrices.  Write `||.||_2` for normalized
Hilbert--Schmidt norm and suppose

```text
rank(V_a-U_a) <= r_a.
```

For every formal word `w=a_1^(eps_1)...a_L^(eps_L)`, `eps_i in {+1,-1}`,

```text
||w(V)-w(U)||_2
  <= 2 sum_(i=1)^L sqrt(r_(a_i)/d).
```

Consequently, if `max_a r_a/d -> 0`, every fixed finite family of word
relations has defect tending to zero after the surgery.  More generally the
same conclusion holds under generatorwise bounds `||V_a-U_a||_2 -> 0`, with
the right side replaced by the sum of those generator errors along the word.
Thus no fixed finite multiplication-table test in normalized HS can detect a
perturbation confined to vanishing relative rank.

## Attempts

- Direct telescoping in the bi-invariant Hilbert--Schmidt metric; the only
  estimate is `||T||_2 <= ||T||_op sqrt(rank(T)/d)`.
