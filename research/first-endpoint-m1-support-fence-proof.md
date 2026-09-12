---
rg: 2
id: first-endpoint-m1-support-fence-proof
kind: route
title: Intersect the two signed planes in the literal first endpoint GL4 block
target: first-endpoint-m1-actor-preserves-missing-r-sign
requires:
  - native-whitehead-hecke-head-has-order-seven-anchor
  - native-j1-extension-gives-gl5-but-only-second-whitehead-gram
  - endpoint-whitehead-star-braid-synchronizes-native-gauges
---

The coefficient identities

```text
a_1b_1=q,       b_1a_1=e_1,
a_2b_2=q,       b_2a_2=e_2
```

identify the four summands in `(FEM1)`.  The order-seven calculation for
`M_1=J_1B_2A_1` is the native faithful `GL_3(F_2)` Singer block on the
first three.  Prefix cancellation makes `W_0=What_(7,2;1)` the
transposition of `e_1@7` and `e_2@2`.  A Singer `GL_3` together with this
one external transposition supplies all coordinate permutations and one
transvection, hence all elementary transvections of the four summands.
This proves `(FEM2)` without enumerating `GL_4(F_2)`.

Ordinary Steinberg collection on the row with target `5` gives `(FEM4)`.
The identical covector action occurs on the row with target `6`.  In the
ordered basis

```text
(h,w,s,w')=(x_64(q),x_67(a_1),x_68(a_2),x_62(a_2)),  (FEMP1)
```

the actor matrices therefore have the same four columns as on `(FEM3)`.

Let `A` denote the induced four-dimensional covector action of a signed
`K_2` return.  Its intersection with the target-five row is the signed
plane

```text
<C_2,v>,                 lambda(C_2)=-1, lambda(v)=+1.
```

Thus

```text
A(C_2) in {C_2,C_2v},             A(v)=v.             (FEMP2)
```

Its intersection with the target-six row is the positive plane `<w,s>`.
Using the identical coordinate action and `(FEMP2)` gives

```text
A(s) in {s,ws},
and hence A(r) in {r,vr}.                              (FEMP3)
```

There is one further vector condition.  The root `C_1=x_42(q)` has active
target `q@4` and source in the orthogonal `q`-part at coordinate `2`.
No other generator of `K_2` has that incidence, so a return must fix its
active target.  In the covector table this says that the image of `v'`
has no `C_2` component.  Invertibility then leaves exactly

```text
A(C_2): 2 choices,       A(r): 2 choices,
A(v'): 4 choices,        A(v)=v,                      (FEMP4)
```

or `16` returns.  Conversely every matrix in `(FEMP4)` fixes `C_1,C_3`,
preserves the two displayed source planes and their character, so these
are exactly the signed-source return subgroup.

Equation `(FEMP3)` is `(FEM5)`.  On `p_2`, multiplication by `v` is the
identity, so `r` and `rv` have the same spectral sign.  The first native
Whitehead exchanges `v` and `r`; the standard character-projection product
therefore gives the first equality in `(FEM7)`, and the profile `(FEM6)`
makes it zero.

`experiments/first_selector_endpoint_m1_support_audit.py` reproduces every
literal coefficient image in `(FEM4)`, verifies the actor orders
`2,7,5`, finds the `16` matrices `(FEMP4)`, and faithfully replays a
four-generator set of that subgroup in sparse Leavitt matrices.  The MSI
run completes in about five seconds.  The finite screen is only a replay
of the preceding exact block argument, not an assumption about arbitrary
finite-prefix coefficients.

For clarity, the audit also verifies the faithful identity

```text
B_2rB_2^(-1)=rC_2.
```

It does not attempt to recognize the full signed source using the older
constant-arrow signature helper: the actual source contains coefficient
roots and derived roots.  Full-source normalization of `B_2` is the exact
coefficient calculation already established by
`center-chain-mixed-hecke-overlap-is-common-pauli-source`, and combining
it with the displayed identity is precisely the separate route
`b2-pairs-full-hecke-first-support`.
