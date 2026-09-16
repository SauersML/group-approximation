---
rg: 2
id: stw83-cuntz-circle-graph-splits-iff-k-equals-n-minus-1
kind: claim
title: The circle-ideal Cuntz-quotient graph extension splits exactly when k equals n minus one
artifacts:
  - research/artifacts/stw99-constant-symbol-pullback-2026-09-16.md
distinct_from:
  stw83-circle-ideal-cuntz-quotient-dimension-two-bound: that gives the pullback model and the one-or-two range; this decides when the model extension has a *-homomorphic section, which does not change the dimension range.
  stw82-af-split-centralizer-extensions-obey-maximum: that needs an AF ideal and a section centralizing it; here the ideal is a circle field and the section never centralizes it.
---

Let `F_(n,k)` (`n>=2`, `k>=1`) have:
* vertices `u` and `v`;
* `n` loops at `u`;
* one loop at `v`;
* `k` edges from `u` to `v`.

The convention is `s_e^*s_e=p_(r(e))`.  Consider the extension

```text
0 -> I_{v} = C(T) tensor K -> C*(F_(n,k)) -> O_n -> 0.
```

1. **Criterion.**  It admits a *-homomorphic splitting `O_n->C*(F_(n,k))`
   if and only if `k=n-1`.
2. **Obstruction.**  In the model of
   `stw83-circle-ideal-cuntz-quotient-dimension-two-bound`, the row
   `[T_1 ... T_n]` of loop isometries is Fredholm of index `n-k-1`.  A
   splitting with complementary finite rank `r` would force `n-k-1=(n-1)r`.
3. **Splitting for `k=n-1`.**  The rank-one corrections
   `W_i=T_i+|xi_i><delta_v|`, with `xi=(delta_(g_1),...,delta_(g_(n-1)),delta_v)`,
   are Cuntz isometries in the fibre algebra.  They give

   ```text
   C*(F_(n,n-1)) = C(T,K) + rho(O_n) tensor 1.
   ```

In particular, the smallest ENSW model `F_(2,1)` of the circle-ideal /
Kirchberg-quotient entry is a split extension containing a unital copy of
`O_2`.

The six-term boundary maps vanish for every `k`, since `K_*(O_n)` is torsion
or zero.  `K`-theory still sees part of the obstruction.  `K_0(C*(F_(n,k)))`
is `Z^2/<(n-1,k)>`, and the extension `0->Z->K_0->Z/(n-1)->0` has class
`k mod (n-1)` up to sign.  A splitting splits this sequence, so `K_0` forces
`k = 0 mod (n-1)`.  The Fredholm index is finer.  It separates `k=n-1` from
the other multiples of `n-1`, and for `n=2` it is the only obstruction.
