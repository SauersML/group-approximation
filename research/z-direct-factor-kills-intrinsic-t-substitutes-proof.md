---
rg: 2
id: z-direct-factor-kills-intrinsic-t-substitutes-proof
kind: route
title: Tensor the involutive cyclic compression model with an arbitrary MF model of the uncompressed factor
target: z-direct-factor-kills-intrinsic-t-substitutes
requires:
  - finite-order-central-compression-defect-survives-mf
---

**Step 0 (input).** By `finite-order-central-compression-defect-survives-mf`
there are unitaries `A_n,B_n,C_n in U(2n)` whose classes `a,t,c` in
`Q_0=prod_n M_(2n)/sum_n M_(2n)` satisfy

```text
tat^-1=a^2,  a of infinite order,  c^2=1,  [a,c]=1,  [tct^-1,a]=-1.   (Z1)
```

Let `G_0=<a,t,c> <= U(Q_0)`.  For each `g in G_0` fix a unitary lift
`(V^0_n(g))_n`.  This is possible because a unitary in `Q_0` lifts to a
sequence of unitaries: lift to a contraction and take the unitary part of
its polar decomposition coordinatewise.  The lifts satisfy
`||V^0_n(gh)-V^0_n(g)V^0_n(h)||_op -> 0`, and `V^0_n(d) -> -I` for
`d=[tct^-1,a]`, both in operator norm.

**Step 1 (uncompressed factor).** Let `K` be countable and MF, with an
operator-norm asymptotic representation `W_n:K->U(k_n)`.  The trivial
representation `W_n=1`, `k_n=1`, is allowed; a faithful MF model works
equally well.

**Step 2 (product model).** Put `G=G_0 x K` and
`V_n(g,k)=V^0_n(g) (x) W_n(k) in U(2n k_n)`.  For unitaries,
`||X (x) Y - X' (x) Y'|| <= ||X-X'|| + ||Y-Y'||`, so

```text
||V_n((g,k)(h,l)) - V_n(g,k)V_n(h,l)||
   <= ||V^0_n(gh)-V^0_n(g)V^0_n(h)|| + ||W_n(kl)-W_n(k)W_n(l)|| -> 0.
```

So `(V_n)` is an operator-norm asymptotic representation of `G`.  It is
injective in the corona on `G_0 x 1`, and on all of `G` when `W` is
faithful, so `G` is MF whenever `K` is.

**Step 3 (compression data).** Let `L=<a> x K`, `u=(t,1)`, `c'=(c,1)`,
`l=(a,1)`.  By `(Z1)`, `uLu^-1=<a^2> x K`.  This is a proper subgroup of `L`
because `a` has infinite order, so `a notin <a^2>`.  The element `c'`
commutes with `<a> x 1` because `[a,c]=1`, and with `1 x K` trivially, so
`c' in C_G(L)`.  Hence

```text
d' = [uc'u^-1, l] = ([tct^-1,a], 1) = (d,1)  in D_G(L).                (Z2)
```

If `K` is finitely generated, then `L` is finitely generated.

**Step 4 (survival).** `V_n(d') = V^0_n(d) (x) W_n(1)`, and `W_n(1) -> I`
while `V^0_n(d) -> -I` in operator norm, so `V_n(d') -> -I`.  For the normalized
Hilbert--Schmidt norm, `||X||_2 <= ||X||_op` gives
`||V_n(d')-1||_2 -> ||-2I||_2 = 2`.  This contradicts part (i) of `(CC_P)`.  The
subgroup `{1,d'}` is central in `G`, so it is normal.  It is finite, so it has
property `(T)`.  It lies in `D_G(L)` by `(Z2)`.  Its image in the MF group `G`
(tautological MF image through `V`) is nontrivial.  This contradicts part (ii).

**Step 5 (properties of `Z x K`).** The claims below are standard facts:

* `Z x F_2`: nonamenable, since it contains `F_2`.  It is residually finite
  and linear as a product of such groups.  It is exact, and it is Haagerup
  because both factors are.
* `Z x SL_3(Z)`: the normal subgroup `1 x SL_3(Z)` is infinite and has
  `(T)` (Kazhdan), so `(L,1 x SL_3(Z))` has relative `(T)` and `L` is not
  Haagerup.  `SL_3(Z)` is residually finite, so it is MF, and Step 1 applies.
* Item (E) of the target uses Hayes' regularity theorem for 1-bounded
  entropy.  It is cited there and not re-proved here, and the target labels
  it as external.

Steps 0 to 4 use only `(Z1)`, which is established in the graph, and
elementary tensor estimates.  So `(CC_P)` is false for every `P` holding on
some `Z x K`.  QED.

**Calibration remark.** The model cannot exist when `G` is simple and
nonabelian, because then `G` has no direct factor `G_0`.  Nor can it exist
when `L` is ICC, because then `L` has no infinite central cyclic factor.
This is why the claim fences only substitutes that are intrinsic to the
subgroup, and does not bear on `EL_20(L_(F_2)(1,2))` directly.
