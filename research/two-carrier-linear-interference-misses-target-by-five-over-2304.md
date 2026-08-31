---
rg: 2
id: two-carrier-linear-interference-misses-target-by-five-over-2304
kind: claim
title: Two-carrier linear interference misses the target by exactly 5/2304
artifacts:
  - research/two-carrier-linear-interference-rank-proof.md
distinct_from:
  two-c-conjugate-g2-mixed-carriers-collapse-to-one-orientation: that treats product words and shows their S letters cancel; this permits arbitrary complex linear interference between the two uncollected carriers.
  first-uncancelled-g2-mixed-carrier-has-no-hall-deficit: that bounds one hidden-sign carrier; this computes the join of two independent hidden-sign carriers.
---

Use the two `C`-conjugate carriers `Y_0,Y_1` and hidden signs
`Z_0,Z_1` from `(TCC1)--(TCC3)`. For `tau=+` put

```text
X_i=G_(sigma,+)Y_iG_(sigma,+),
K_i=X_i^*X_i=G_(sigma,+)(1+Z_i)/2.                     (LIF1)
```

Let `lambda_0,lambda_1` be arbitrary complex numbers and set

```text
X_lambda=lambda_0X_0+lambda_1X_1.
```

Every cross term in `X_lambda^*X_lambda` is allowed. Nevertheless its
initial support is bounded by the join

```text
L_sigma=K_0 join K_1
 =G_(sigma,+)(1-(1-Z_0)(1-Z_1)/4).                     (LIF2)
```

After the qutrit source cut `R=e_0+e_1`, the join has exact ranks

```text
tau(supp abs(L_+R))=41/768=123/2304,
tau(supp abs(L_-R))=13/256=117/2304.                   (LIF3)
```

Thus, for every qutrit target atom `e_b`, every integer `j`, and every
choice of the two complex coefficients,

```text
T=Ee_b g_2^j X_lambda R
```

satisfies

```text
tau(supp abs(T)) <=123/2304 <128/2304=1/18
                                                when sigma=+,

tau(supp abs(T)) <=117/2304 <128/2304=1/18
                                                when sigma=-. (LIF4)
```

Both negative-`tau` carriers vanish. Hence destructive or constructive
interference between the first two independent hidden signs cannot
produce a Hall excess. The all-plus row misses by exactly

```text
1/18-41/768=5/2304.                                    (LIF5)
```

This is the sharp two-carrier threshold: it treats arbitrary linear
combinations, not only group words. A capacity argument now needs a
third independent hidden-sign carrier, or a carrier obtained by moving
the positive `S` root as well as the negative `T` root.
