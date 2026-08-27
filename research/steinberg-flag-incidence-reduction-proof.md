---
rg: 2
id: steinberg-flag-incidence-reduction-proof
kind: route
title: Identify Steinberg with top building cycles and stack the boundary with the two Fox rows
target: steinberg-fox-kernel-is-flag-incidence
requires:
  - authenticated-mixed-loop-kills-minuscule-affine-modules
---

The spherical building of `G=SL_3(F_p)` is the bipartite incidence graph of
points and planes in `F_p^3`.  Its oriented chambers are flags
`point subset plane`, hence form the basis `G/B`; its two vertex types form
the bases `G/P_1` and `G/P_2`.  With the orientation from the first type to
the second, its cellular boundary is exactly `(SFI1)`.

There are no two-cells, so its top reduced homology is `ker partial`.
The Solomon--Tits realization of the defining-characteristic Steinberg
module therefore gives the `kG`-equivariant identification

```text
St_p=ker(partial:C_1 -> C_0).                           (SFP1)
```

The coefficient actor acts on every building chain space by left
translation.  Consequently the two group-ring elements from `(MMP3)` act
on `C_1`, preserve `ker partial`, and have precisely the expansions `(SFI2)`.
For `f in C_1`,

```text
D_p(f)=0
 iff partial f=0, Xf=0, and Yf=0
 iff f in St_p and Xf=Yf=0.                            (SFP2)
```

This proves `(SFI4)`.

For completeness, write a flag as `([v],[phi])`, where `phi(v)=0`, with
independent projective rescaling of `v` and `phi`.  Left translation is

```text
g.([v],[phi])=([gv],[phi g^(-1)]).                     (SFP3)
```

Thus the coefficient of `Xf` or `Yf` at a fixed flag is obtained by
evaluating `f` at the inverses of the five or six transformations in
`(SFI2)`.  The two components of `partial f=0` are exactly the zero panel-sum
conditions.  Hence `(SFI3)` is a literal finite symbolic incidence system,
not an appeal to semisimplicity or to a character table.

Finally let `s_1` be the Weyl reflection interchanging the first two basis
vectors.  Since

```text
s_1^(-1)x_12(2)s_1=x_21(plusOrMinus 2),                (SFP4)
```

the chamber `x_12(2)s_1B` has a nonzero root parameter in the rank-one
Bruhat cell and is not one of the six chosen chambers `wB`, `w in W`.
Therefore the standard-apartment chain span is not stable under the
coefficient action.  Any argument using only the Weyl sign representation
forgets data required by `(SFP2)`.

There is nevertheless one canonical line that can be disposed of without
any Bruhat expansion.  Both `q=x_21(-1/2)` and `s=x_32(-1/2)` lie in the
lower unipotent `U^-`.  Hence, for a `U^-`-fixed vector `v`,

```text
Xv=A(1-q)v+B(1-s)v-v=-v.                              (SFP5)
```

In particular the one-dimensional `U^-`-fixed line in `St_p|U^-` is not an
affine escape.  Any counterexample must use a genuinely nonconstant
root-group coefficient function in the flag-incidence model.

The highest-weight line can also be evaluated without expanding the whole
module.  Let `v_+` be a highest vector.  Its weight is `(p-1)rho`, so the
finite torus `T(F_p)` acts trivially; hence every element of `B` fixes
`v_+`.  In particular `A,B,c,u,r,h` fix it.  Since

```text
u=q c q^(-1),
u q v_+=q c v_+=qv_+,                                 (SFP6)
```

both factors in the second row of `(MMP3)` vanish on `v_+`, and `Yv_+=0`.

For a simple root, the rank-one identity

```text
x_i(2)x_(-i)(-1/2)x_i(2)=w_i(2)                       (SFP7)
```

and `x_i(2)v_+=v_+` show that `Aqv_+=w_1(2)v_+`.
Likewise `Bsv_+` is a nonzero torus multiple of `w_2(2)v_+`.  In the usual
PBW basis of the Steinberg module these are nonzero multiples of
`f_1^(p-1)v_+` and `f_2^(p-1)v_+`, respectively.  Together with `v_+` they
are three distinct PBW basis vectors.  Therefore

```text
Xv_+=v_+-Aqv_+-Bsv_+ != 0.                            (SFP8)
```

So the `B`-fixed line is contained in `ker Y` but is disjoint from the
common kernel.
