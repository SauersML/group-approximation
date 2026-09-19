---
rg: 2
id: three-parahoric-weyl-triangle-has-affine-gauge-countermodel
kind: claim
title: Three parahoric gauges and the Weyl triangle still admit an exact affine lamp countermodel
distinct_from:
  rank-two-weyl-triangle-is-first-apartment-gauge-detector: that kills one corrector already lying in the full coefficient commutant; this gives three different correctors, each central only on its own parahoric, which obey the same Weyl triangle exactly.
  affine-weyl-apartment-has-independent-lamp-models: that uses arbitrarily large torus quotients and the apartment normalizer; this is one eight-site finite model containing the full coefficient group GL_3(F_2) and the three maximal parahoric stabilizers.
  bounded-p-part-sector-reduces-to-twisted-weyl-homs: that classifies twisted correctors after congruence splitting and retains a level-coupled intertwining condition; this is the elementary finite affine cocycle showing why the Weyl equations plus separate parahoric covariance do not imply that condition.
---

Let

```text
F = GL_3(F_2) = SL_3(F_2),
L = F_2^3,
B = direct_sum_(x in L) C_2,
H = B rtimes (L rtimes F),                              (TPW1)
```

where `L rtimes F` acts affinely on the eight lamp coordinates.  Write `c_x`
for the coordinate lamp and `t_lambda` for translation by `lambda`.  Take

```text
lambda_0=(1,0,1),
lambda_2=(1,1,0),
lambda_1=(0,1,1)=lambda_0+lambda_2,
v_i=t_(lambda_i).                                      (TPW2)
```

The permutation matrices `S_3 < F` permute the three nonzero even-weight
vectors.  Hence the `v_i` are Weyl conjugates and

```text
v_0 v_2^(-1)=v_1.                                     (TPW3)
```

For `P_i=Stab_F(lambda_i)`, every `v_i` commutes with the full finite
parahoric `P_i`.  Thus the complete multiplication tables of `F` and the
three `P_i`, all root relations internal to them, all three local covariance
laws, Weyl conjugacy, and the rank-two triangle hold exactly in one finite
group.

The base lamp `c_0` commutes with all of `F`, while

```text
v_i c_0 v_i^(-1)=c_(lambda_i).
```

In the left regular representation of `H`, put

```text
E=(1-c_0)/2,
E_i=v_i E v_i^(-1).
```

The coordinate lamps are distinct commuting involutions, so

```text
tr(E)=tr(E_i)=1/2,
[E,E_i]=0,
tr(E E_i)=1/4.                                        (TPW4)
```

On the Fourier model of `B`, the eight lamp coordinates are eight qubit
factors and `v_i` is the tensor-factor permutation induced by translation of
`L`; it is a product of four disjoint swaps and moves the distinguished
qubit from `0` to `lambda_i`.  Thus `(TPW1)--(TPW4)` is a literal
three-direction extension of the tensor-swap enemy.

The model identifies the missing relation sharply.  If `u in F` does not
fix `lambda_i`, then

```text
v_i u v_i^(-1)
  = t_(lambda_i+u lambda_i) u,                         (TPW5)
```

and the nonzero translation tail is visible.  Therefore the model fails
exactly when a mixed root word outside the directional parahoric is required
to land back in the coefficient group.  The Weyl triangle does not itself
force a common gauge; it only kills the specialization in which the three
gauges have already been identified in the full coefficient commutant.

Consequently the load-bearing statement remains the common-slot/gluing step
`(RWT8)`: the actual arithmetic presentation must make enough transverse
root words detect the affine translation tail in `(TPW5)`.  Separate exact
parahoric covariance plus every rank-two Weyl relation is insufficient.
