---
rg: 2
id: orthogonal-centralizer-area-proof
kind: route
title: Sum the Galois Schreier norms before applying the fixed channel maps
target: orthogonal-centralizer-channels-retain-area-properness
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Choose the prime-order Galois local system from
`finite-mark-centralizer-commutator-area-is-proper`.  Its proof gives constants
`a>0,c>=0` such that

```text
||c_j||_(Gal,1) >= a d_(K\G)(K,Kh_j)-c                 (1)
```

for every `j`, independently of the representing word.  Equip the direct
sum of `q` copies with the sum norm.  Then

```text
||(c_1,...,c_q)|| = sum_j ||c_j||
 >= a sum_j d_(K\G)(K,Kh_j)-qc.                         (2)
```

The twisted boundary of one translated defining-relator cell has bounded
norm in one channel.  A fixed linear mixing map from that cell into the
`q` channels multiplies this bound by at most its operator norm for the sum
norm.  Because both the channel number and the family of allowed mixing maps
are fixed, there is one constant `C_q<infinity` bounding the vector boundary
of every mixed cell.  Hence an expression as a sum of `L` such cell
boundaries has norm at most `L C_q`.  Comparing with `(2)` gives `(OCP1)` with

```text
A_q=a/C_q,                 B_q=qc/C_q.
```

Unitary or orthogonal `A_5` channel changes are a special case: in fixed
dimension their sum-norm operator constants are uniformly bounded.  The
argument says nothing about a genuinely different combined edge boundary,
which is why the direct Carmichael-chart target remains open.
