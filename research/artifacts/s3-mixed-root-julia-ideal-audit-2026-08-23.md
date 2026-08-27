# Mixed root--Julia ideal-kernel audit (2026-08-23)

## Target

The first packed-root countermodel killed the entire commutator root line.
The smallest natural repair is non-retractive: retain and authenticate the
unit coordinate `x_13(1)` by identifying it with a genuine Julia
commutator of two involutions.  This audit asks whether that one anchor also
reflects the kernel of the designated packed coefficient.

It does not.  A proper coefficient-ideal quotient retains the authenticated
unit root while killing the designated coordinate exactly.

## Coefficient quotient

Let

```text
A=F_5[eps]/(eps^2),          phi:A->F_5,       phi(eps)=0.
```

The coefficient `eps` is nonzero and square-zero in `A`, while `phi` is
unital.  Entrywise reduction gives a finite group quotient

```text
UT_3(A) -> UT_3(F_5)                                (MJI1)
```

which retains `x_13(1)` and kills `x_13(eps)`.

## Non-retractive Julia anchor

Write elements of `UT_3(F_5)` as `x_12(a)x_23(b)x_13(c)`.  The order-two
automorphism

```text
sigma(x_12(a))=x_23(a),
sigma(x_23(b))=x_12(b),
sigma(x_13(c))=x_13(-c)                              (MJI2)
```

is exact.  Form `K=UT_3(F_5) rtimes_sigma C_2`, let `z` be the actor
involution, put `c=x_13(1)`, and define

```text
j=z c^3.                                             (MJI3)
```

Then

```text
z^2=j^2=1,                 z j z j=c.                (MJI4)
```

Thus the unit root is tied to a literal two-involution Julia commutator and
is nonidentity.  The previous center-killing quotient no longer satisfies
this anchor.  In the left regular representation of the order-250 group
`K`, the anchor word has squared normalized-HS defect `2`, and the
off-diagonal Julia block of `j` relative to `z` has mass `1/4`.

Nevertheless `(MJI1)` gives exactly

```text
x_13(eps)=1.                                         (MJI5)
```

All same-root additions and all positive-root Steinberg triangles remain
exact.  Hence the nontrivial unit/Julia anchor prevents total root collapse
but does not prevent a proper coefficient-ideal kernel.

There is also a zero-carrier absorber for the direct variant.  If one ties
the designated coordinate itself by

```text
z j z j=x_13(eps),                                   (MJI6)
```

then after `(MJI1)` the exact choice `j=z` satisfies `(MJI6)` and has zero
Julia off-diagonal block.  Therefore `(MJI6)` does not identify that block
with the concrete packed endpoint row.

## Endpoint payload

Tensor the scalar endpoint payload from the retractive audit:

```text
Q=V_b=1,       Z_X=-1,       Z_Y=1,
A_00=A_11=(1,1),             A_01=(-1,1).
```

Again all three convention residuals and both source commutators vanish,
while

```text
sum_(b,j)||D_(b,j)||_2^2=8,       ||R||_2^2=4/3.      (MJI7)
```

Thus the exact nontrivial unit-root Julia anchor, the full local root table,
and the designated root relation `(MJI5)` coexist with positive packed row
energy.

## MSI replay

Script:
`experiments/s3_mixed_root_julia_ideal_audit.py`

Remote directory:
`/projects/standard/hsiehph/sauer354/cairn-s3-packed-root-20260823`

Environment: `acn112`, Python `3.11.13`.  The canonical JSON output has
SHA-256

```text
8028bd8a71f6d074d2875686eae01711c7da80d8c6991688f16b81720d588664
```

Exact checks:

```text
75 root-additivity checks:                 0 failures
25 Steinberg multiplication triangles:    0 failures
125 sigma-square checks:                   0 failures
15,625 sigma-homomorphism checks:          0 failures
z and j involutions:                       yes
zjzj=x_13(1) nontrivially:                 yes
x_13(eps)=1 under unital reduction:        yes
direct designated tie admits j=z:          yes
endpoint covariance energy:                8
other endpoint terms:                      0
```

## Consequence

Anchoring a constant root coordinate by a Julia or Hecke word is not
one-coordinate kernel reflection.  It excludes only the total root-killing
quotient.  A successful mixed cell must also exclude every proper
coefficient ideal containing the packed row while retaining the unit, or it
must tie the Julia off-diagonal block directly to the representation-specific
endpoint row on the same reservoir.  The direct tie `(MJI6)` merely replaces
the ideal escape by the zero-carrier absorber.

