---
rg: 2
id: telescoping-involution-product-overlap-proof
kind: route
title: Telescope the normal product on the nontrivial spectral carrier
target: involution-normal-product-forces-one-factor-overlap
requires: []
---

The product telescopes as

```text
w-1=sum_(j=1)^k v_1...v_(j-1)(v_j-1).
```

Since every prefix is unitary and `v_j-1=-2p_j`, right multiplication by
`q` gives

```text
||(w-1)q||_2 <= 2 sum_j ||p_j q||_2
              = 2 sum_j sqrt(tau(q p_j)).            (NPP1)
```

On the other hand `(r-1)q=-2q`, so

```text
2sqrt(tau(q))
  <= ||(r-w)q||_2+||(w-1)q||_2
  <= eta+2 sum_j sqrt(tau(q p_j)).                    (NPP2)
```

Therefore

```text
max{sqrt(tau(q))-eta/2,0}
  <= sum_j sqrt(tau(q p_j))
  <= sqrt(k sum_j tau(q p_j)),                        (NPP3)
```

which is `(NPO1)`.  At least one of the `k` nonnegative summands is at least
their average, proving `(NPO2)`.  If `v_j=g_j z g_j^*`, then
`p_j=g_j(1-z)g_j^*/2`, giving the stated carrier interpretation.
