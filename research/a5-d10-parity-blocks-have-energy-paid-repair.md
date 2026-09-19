---
rg: 2
id: a5-d10-parity-blocks-have-energy-paid-repair
kind: claim
title: Native level-five parity blocks have an energy-paid one-line flexible repair
distinct_from:
  a5-d10-restriction-keeps-parity-charge: that computes the same-level lattice obstruction and the formal one-line type change; this proves a full residual-energy dichotomy and an exact joint completion, allowing an extension through another level when it exists.
  bs14-flexible-cross-packet-boundary-reconciliation: that asks for one uniform theorem over all moving packets and arbitrary cross-block mixing; this proves it for block-diagonal sums of the smallest native parity core.
  direct-sum-weil-compressions-have-quadratic-padding: that treats canonical compressed Weil blocks at unbounded prime levels using explicit cubic energy; this is a compact fixed-level theorem for the non-Weil determinant-two restriction hole.
---

**ESTABLISHED FIXED-FACE THEOREM.**  Let `sigma` be the five-dimensional
`D_10` representation

```text
h=epsilon+rho_1+rho_2,                                  (AER1)
```

with its exact BS generators `(R_h,S_h)`, and define on `U(5)` the
unnormalized four-relator energy

```text
E_h(Y)=||Y^2-1||_F^2+||YR_hY-R_h^(-1)||_F^2
      +||(YS_h^2)^3-1||_F^2+||(YR_hS_h)^3-1||_F^2.     (AER2)
```

There is a dichotomy which in either case gives flexible repair.

1. If the zero set `Z_h={Y:E_h(Y)=0}` is nonempty, then there is a modulus
   `f_h(t)->0` such that every `Y` is within `f_h(E_h(Y))` of an exact
   extension on the same core.
2. If `Z_h` is empty, then

   ```text
   delta_h=min_(Y in U(5)) E_h(Y)>0.                   (AER3)
   ```

   Adjoin one `D_10` sign line `epsilon`.  The restriction identity

   ```text
   h+epsilon=res_(D_10)^(A_5)(3 direct_sum 3')         (AER4)
   ```

   supplies an exact six-dimensional Iwahori endpoint, with both cubic
   rows and their joint Gram equations exact.  Its one-line padding cost
   obeys

   ```text
   1<=E_h(Y)/delta_h.                                  (AER5)
   ```

The first branch automatically permits an extension belonging to a
different congruence level: `Z_h` is defined by the full Iwahori relators,
not by factorization through `A_5`.  Thus `(AER3)--(AER4)` are used only
when no level supplies a same-core endpoint.

Consequently every block-diagonal direct sum of `h`-blocks, together with
an arbitrary exact background, has an energy-paid flexible repair.  In the
empty-zero-set branch, if `K` bad blocks occur then

```text
k=K<=delta_h^(-1) sum_(j=1)^K E_h(Y_j).                (AER6)
```

Changing the five old dimensions of each bad block arbitrarily and adding
one line per block has normalized-HS cost `O(sqrt(K/d))`; hence it tends to
zero whenever total normalized energy tends to zero.  In the nonempty
branch, correct every block inside its old core using `f_h`; boundedness and
a low/high energy split turn the pointwise modulus into a direct-sum
normalized-HS modulus.

This realizes the support-changing odd triple at the first native face and
shows exactly how residual energy pays it.  The construction is not uniform
over moving levels: `delta_h` and `f_h` come from compactness in fixed
dimension five.  Nor does it handle an `X` which mixes many native
restriction blocks before the blocks have been authenticated.  Those are
precisely the remaining quantitative and cross-packet parts of `(FBR2)`.

DERIVATION
a5-d10-energy-paid-repair-proof
