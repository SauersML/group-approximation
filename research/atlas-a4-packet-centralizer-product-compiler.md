---
rg: 2
id: atlas-a4-packet-centralizer-product-compiler
kind: claim
title: The thirty shortest A4 atlas relations compile to thirty centralizer-product constraints on one unitary
---

Let

```text
rho_k = Reg(A8) tensor I_k
```

and represent the two atlas factors by `rho_k` and `Ad(U_k) o rho_k`.
For each of the thirty pair-cubes in `atlas-shortest-a4-triangle-packet`,
define a closed set `D_(j,k)` as follows.

- If the word is `(b_2 a_1)^3`, with `|a|=3`, `|b|=2`, set

  ```text
  D_(j,k)=U(rho_k(<a>)') U(rho_k(<b>)').
  ```

- If the word is factor-reversed `(b_1 a_2)^3`, set

  ```text
  D_(j,k)=U(rho_k(<b>)') U(rho_k(<a>)').
  ```

If all thirty normalized-HS pair-cube defects tend to zero along an arbitrary
sequence `k=k_n`, then

```text
max_(1<=j<=30) dist_2(U_(k_n),D_(j,k_n)) -> 0.        (A4-PACKET-CENT)
```

Thus all local finite-group stability and all local A4 representation-type
freedom can be removed from the atlas boundary simultaneously.  What remains
is one finite geometric agreement problem: a single amplified regular-A8
relative unitary must approach all thirty explicit centralizer-product sets
at once, while also satisfying the independent collision word `19243`.
