---
rg: 2
id: atlas-a4-packet-centralizer-product-compiler
kind: claim
title: The thirty shortest A4 atlas relations compile to thirty shifted centralizer-product constraints on one unitary
artifacts:
  - experiments/atlas_a4_reference_alignment.py
---

Let

```text
rho_k = Reg(A8) tensor I_k.
```

Fix once and for all the inner chart alignment `r_0 in A8` with matrix

```text
00000001000100000100000000000100
```

in the canonical `GL_4(F2)` realization, and put `R_k=rho_k(r_0)`.  The exact
finite audit `experiments/atlas_a4_reference_alignment.py` verifies that this
single alignment satisfies all thirty pair-cubes in
`atlas-shortest-a4-triangle-packet`.

Represent the two atlas factors by `rho_k` and `Ad(U_k) o rho_k`.  For each
pair-cube define a closed shifted double-coset set `D_(j,k)` as follows.

- If the word is `(b_2 a_1)^3`, with `|a|=3`, `|b|=2`, set

  ```text
  D_(j,k)=U(rho_k(<a>)') R_k U(rho_k(<b>)').
  ```

- If the word is factor-reversed `(b_1 a_2)^3`, set

  ```text
  D_(j,k)=U(rho_k(<b>)') R_k U(rho_k(<a>)').
  ```

If all thirty normalized-HS pair-cube defects tend to zero along an arbitrary
sequence `k=k_n`, then

```text
max_(1<=j<=30) dist_2(U_(k_n),D_(j,k_n)) -> 0.        (A4-PACKET-CENT)
```

The reference factor `R_k` is essential.  The two chart alphabets cannot be
identified naively: for several packet edges the same-chart order-two and
order-three labels commute and have product order six, while other packet
edges have product order two.  Therefore the unshifted sets
`U(rho(<a>)')U(rho(<b>)')` are not the correct A4 orbits.

With the shift inserted, all local finite-group stability and local A4
representation-type freedom are removed from the atlas boundary.  What remains
is one finite geometric agreement problem: a single amplified regular-A8
relative unitary must approach all thirty explicit shifted centralizer products
at once, while also satisfying the independent collision word `19243`.
