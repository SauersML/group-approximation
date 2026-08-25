---
rg: 2
id: finite-vn-toeplitz-coefficient-reconstruction-fails-proof
kind: route
title: Use the faithful regular representation and the non-direct Toeplitz corner
target: finite-vn-toeplitz-coefficient-reconstruction-fails
requires:
  - schur-idempotent-is-an-injective-toeplitz-defect
  - schur-toeplitz-envelope-has-proper-self-embedding
---

The proper self-embedding of `EL_5(R_f)` is injective, so Britton normal
form embeds the base in its ascending HNN extension `H_f`.  The left regular
representation of every discrete group is faithful and lands in the unitary
group of its finite group von Neumann algebra.  Hence `(FVR1)` is an exact
finite-tracial model of the full root table and stable-letter covariance.

If `a` belongs to `(FVR2)`, then in particular
`lambda(x_12(a))=1`.  Faithfulness of `lambda`, base injectivity, and
`x_12(a)=1+E_12a` imply `a=0`.  Thus `K_lambda=0`.

The defining Toeplitz equations give `yx=1` and `xy=1-P_f`; injectivity of
the packet algebra gives `P_f!=0`.  Therefore `R_f/K_lambda` is not directly
finite.  Every finite von Neumann algebra and every matrix amplification of
it is directly finite, which rules out a faithful unital coefficient map.

Finally, a faithful Sylvester matrix-rank function would force stable
finiteness.  If `yx=1`, its scalar ranks satisfy
`rk(x)=rk(y)=rk(xy)=1` by the product and Sylvester inequalities.  Rank is
additive on complementary idempotents, so

```text
1=rk(1)=rk(xy)+rk(1-xy)=1+rk(1-xy).
```

Thus `rk(1-xy)=0`; faithfulness gives `xy=1`, contradicting `P_f!=0`.
