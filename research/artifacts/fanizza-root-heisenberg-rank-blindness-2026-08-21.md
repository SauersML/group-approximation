# Local Steinberg--Heisenberg packets do not see coefficient rank

## A family with identical unitary packets and arbitrary coefficient rank

Fix `n>=1` and put

```text
R_n=M_n(F_2).
```

For `1<=r<=n`, let

```text
e_r=diag(I_r,0_(n-r)).                                  (RHB1)
```

Thus `e_r^2=e_r`, but its normalized coefficient rank `r/n` ranges through
all nonzero `n`th fractions.

Inside `E_3(R_n)` define

```text
P_r=x_12(e_r),       Q_r=x_23(e_r),       Z_r=x_13(e_r). (RHB2)
```

The Steinberg relations and characteristic two give

```text
P_r^2=Q_r^2=Z_r^2=1,
[P_r,Q_r]=Z_r,
[P_r,Z_r]=[Q_r,Z_r]=1.                                 (RHB3)
```

Because the scalar line `F_2 e_r` is a copy of `F_2`, the subgroup

```text
H_r=<P_r,Q_r,Z_r>
```

is the same abstract order-eight Heisenberg group `UT_3(F_2)` (isomorphic to
`D_8`) for every nonzero rank `r`.

Let `lambda_n` be the left regular representation of `E_3(R_n)`.  Restricted
to `H_r`, it is exactly `[E_3(R_n):H_r]` copies of the regular representation
of `H_r`.  Consequently the complete finite packet distribution of
`(P_r,Q_r,Z_r)` is independent of `r`.  In particular:

- every nonidentity packet word has trace zero;
- each nontrivial root involution has balanced spectrum;
- the negative central projection `(1-Z_r)/2` has trace `1/2`; and
- restriction multiplicities are the same for all `r`.

Moreover, any fixed abstract selector-automorphism table internal to this
D8 packet can be adjoined in the same semidirect-product model for every
`r`; such an abstract selector extension still contains no rank parameter.

The same is true after adjoining the scalar-line root additivity table

```text
x_ij(ae_r)x_ij(be_r)=x_ij((a+b)e_r),                   (RHB4)
```

and the idempotency multiplication triangle

```text
[x_12(e_r),x_23(e_r)]=x_13(e_r^2)=x_13(e_r).           (RHB5)
```

Thus the smallest mixed Steinberg/finite-Heisenberg packet proposed for the
Fanizza selector cell cannot distinguish a full coefficient carrier
`e_n=1` from a proper carrier `e_r`, even though their coefficient ranks can
differ by fixed density.

## Consequence for source-Gram authentication

The desired source Gram is a statement about complex matrix rank/support.
Local root syntax sees only the abstract additive line and multiplication
`e^2=e`.  Spectral exactification of the D8 packet, conditional expectation
onto it, selector permutations of its characters, and spectator
amplification all return the same data for every `r`.

Therefore no decoder whose hypotheses are only:

1. same-root additivity on `F_2e`;
2. the one Steinberg multiplication triangle `(RHB5)`; and
3. a fixed finite Heisenberg/selector covariance table

can infer that the decoded coefficient occupies the whole selected complex
source or that `X^*X` is close to `E`.  The exact left-regular packets give
zero hypothesis defect with arbitrary hidden coefficient rank.

This does not rule out a substantially larger coefficient chart.  A full
matrix-unit/Morita table can algebraically expose the rank of a fixed
idempotent.  But turning that algebraic rank into normalized complex matrix
trace is exactly a root-to-coefficient trace-reflection theorem, and a fixed
functorial chart again faces the regular firewall.  The surviving route must
either:

- expose an extensive, matrix-dependent family of equivalent coefficient
  atoms on the selected C18 reservoir; or
- prove a characteristic-zero same-reservoir root-to-Gram reflection which
  excludes the finite-characteristic Weyl packets.

Mixed Steinberg triangles are still useful for transferring additivity, as
`mixed-steinberg-triangles-transfer-actor-additivity` proves.  The calculation
here shows that additivity plus one idempotent Heisenberg cell does not
authenticate rank or adjoint Gram.
