# A finite rational Hodge certificate for the six integral transvections

This note isolates the finite calculation used by the direct affine
non-MF argument. Its mathematical input is the explicit integer table below
and elementary multiplication in `SL_3(Z)`. The positivity assertion is proved
by factoring a Gram matrix and bounding an explicitly computed remainder.

## The exact generators and relation words

Write

```text
(a,b,c,d,e,f)=(I+E_12,I+E_13,I+E_21,I+E_23,I+E_31,I+E_32)
```

in `L=SL_3(Z)`, and use `[x,y]=xyx^(-1)y^(-1)`. The thirteen words, in
their operative order, are

```text
[a,d] b^(-1), [b,f] a^(-1), [c,b] d^(-1),
[d,e] c^(-1), [e,a] f^(-1), [f,c] e^(-1),
[a,b], [a,f], [b,d], [c,d], [c,e], [e,f],
(a c^(-1) a)^4.
```

Each is the identity by integral `3 x 3` matrix multiplication. All six
generators are elementary transvections. They generate `SL_3(Z)`: integral
row additions, available as powers of these generators, apply the Euclidean
algorithm to a primitive first column and then to the remaining `2 x 2`
block. The signed row exchanges needed in that reduction are products of
three transvections. The resulting diagonal signs are removed by squares of
those signed exchanges. Thus the reduction ends at the identity using the
six generators and their inverses.

For the calculation in `R[L]`, it is unnecessary to assert that these
thirteen words present `L`. Their being relations is enough.

## Definitions of `D`, `B`, and the Hodge matrix

Let `s=(a,b,c,d,e,f)`. The group-ring column `D` has entries

```text
D_i=s_i-1,                    0<=i<6.
```

For a displayed relation `r=t_1 ... t_m`, define its Fox row `B_r` as
follows. Start with the prefix `p=1` and six zero group-ring entries.
At a positive letter `t_k=s_i`, add `p` to entry `i`, then replace `p`
by `p s_i`. At a negative letter `t_k=s_i^(-1)`, first replace `p` by
`p s_i^(-1)`, then subtract `p` from entry `i`. This completely specifies
the `13 x 6` matrix `B` with integer group-ring entries.

At either sign, the contribution to `B_r D` is the new prefix minus the
old prefix. Consequently

```text
B_r D=r-1=0,                   B D=0.                 (1)
```

For a group-ring element, `*` inverts each group element and conjugates
its coefficient; on matrices it also transposes. Put

```text
Delta=B* B+D D*.                                       (2)
```

For any unitary representation `pi:L->U(H)`, evaluation gives
`D:H->H^6`, `B:H^6->H^13`, and a positive self-adjoint operator
`pi(Delta)` on `H^6`.

## The finite factor and its support

The complete integer table is the array `factor_numerators` in
[sl3-sos-radius0-certificate.npz](../../experiments/sl3-sos-radius0-certificate.npz).
It has `102` rows and `132=6*22` columns. The same table is printed as
`qNumeratorRow0` through `qNumeratorRow101` in
[LiteralP13HodgeData.lean](../../GroupApproximation/Sofic/LiteralP13HodgeData.lean).
The denominator of each entry is exactly `10^8`. No eigenvalues or
floating-point entries are part of the certificate.

For clarity, write `A_(r,i,k)` for the integer entry in row `r` and
column `22 i+k`. The ordered support words `h_0,...,h_21` are

```text
 0: (a c^(-1) a)^2
 1: a c^(-1) a a c^(-1)
 2: a c^(-1) a a c^(-1) a a c^(-1)
 3: (a c^(-1) a)^3
 4: a c^(-1) a
 5: a c^(-1)
 6: a^(-1)
 7: b^(-1)
 8: c^(-1)
 9: d^(-1)
10: e^(-1)
11: f^(-1)
12: 1
13: f
14: e
15: d
16: c
17: d e d^(-1)
18: b
19: a d a^(-1)
20: a
21: b f b^(-1).
```

Their integral matrices, in this order, are also stored in `group_support`.
Equivalently, they are the lexicographically sorted integral matrices of
the Fox prefixes, together with `1` and the six inverse generators. The
verifier reconstructs this set and requires exact equality with the stored
array, including the order.

Define the `102 x 6` group-ring matrix

```text
Q_(r,i)=10^(-8) sum_(k=0)^21 A_(r,i,k) h_k.            (3)
```

For every representation and `z in H^6`,

```text
<pi(Q* Q)z,z>=sum_(r=0)^101 ||sum_i pi(Q_(r,i))z_i||^2>=0.  (4)
```

This proves positivity exactly, irrespective of how the integer entries
were originally found.

## Exact residual computation

Set

```text
R=Delta-(1/250) I_6-Q* Q.                              (5)
```

All coefficients of `R` have common denominator `10^16`. For every
`i,j` and group element `g`, its integer numerator is exactly

```text
N_ij(g)=10^16 [g]Delta_ij
        -40000000000000 [i=j and g=1]
        -sum_(r=0)^101 sum_(k,l: h_k^(-1)h_l=g)
             A_(r,i,k) A_(r,j,l).                      (6)
```

Here `[g]` takes a group-ring coefficient and brackets around a proposition
are its indicator. The support products `h_k^(-1)h_l` have `293` distinct
integral matrices. Formula (6) is therefore a finite calculation with
integers. The exact row totals `sum_(j,g)|N_ij(g)|` are

| Row | Integer numerator |
| --- | ---: |
| 0 | 11670886519714 |
| 1 | 11659124680677 |
| 2 | 11665866556524 |
| 3 | 11658749718021 |
| 4 | 11658998556031 |
| 5 | 11658961981218 |

These are the checked-in values in
[sl3-sos-radius0-certificate.json](../../experiments/sl3-sos-radius0-certificate.json)
and the exact residual block proofs assembled in
[LiteralP13HodgeCertificate.lean](../../GroupApproximation/Sofic/LiteralP13HodgeCertificate.lean).
The independent verifier described below reconstructs them from the factor
and the thirteen words; it does not read either source of residual totals.

The coefficient identity

```text
N_ji(g^(-1))=N_ij(g)                                  (7)
```

is checked as well. Thus the column totals have the same six values as
the row totals. Set

```text
rho=11670886519714/10^16.
```

For completeness, the block Schur bound needs both the row and column
estimates. Put `m_ij=sum_g |N_ij(g)|/10^16`. For `z in H^6`,
write `u_j=||z_j||`. Since every `pi(g)` has norm one,

```text
||sum_j pi(R_ij)z_j|| <= sum_j m_ij u_j,
(sum_j m_ij u_j)^2 <= (sum_j m_ij)(sum_j m_ij u_j^2).
```

Summing over `i` and using both bounds gives
`||pi(R)z||^2<=rho^2||z||^2`. Therefore

```text
||pi(R)||<=rho.                                       (8)
```

Combining (4), (5), and (8) proves, for every unitary representation,

```text
pi(Delta) >= (1/250-rho) I
          = 14164556740143/5000000000000000 I
          > (1/500) I.                                (9)
```

In particular the clean bound `1/500` follows from rational arithmetic.

## Degree-zero consequence, with its proof

Let

```text
T=D*D=sum_(i=0)^5 (2-pi(s_i)-pi(s_i)^*).
```

Applying (9) to `Dx`, and using `BD=0`, gives

```text
(1/500)<Tx,x> <= ||Tx||^2,
T^2 >= (1/500) T.                                     (10)
```

The positive self-adjoint operator `T` has spectrum in `[0,24]`, because
each of its six summands has norm at most four. By the continuous
functional calculus, (10) places its spectrum in
`{0} union [1/500,24]`. Its kernel is precisely the vectors fixed by all
six generators, hence by `L`: this follows from

```text
<Tx,x>=sum_i ||pi(s_i)x-x||^2.
```

If `P_L` is the orthogonal projection onto this kernel, the same spectral
calculus yields the explicit distance estimate

```text
||x-P_L x||^2 <= 500 sum_i ||pi(s_i)x-x||^2.            (11)
```

Thus (11) is derived from the displayed relation words and the integer
factor, through (1)--(10). No qualitative group rigidity theorem is an
input to this derivation.

## Reproducibility and the abstract-presentation distinction

[verify_affine_hodge_certificate.py](../../experiments/verify_affine_hodge_certificate.py)
is an independent standard-library verifier. It accepts precisely the
fixed NPZ member set, with NPY v1.0, little-endian signed `int64`, C-order
arrays and the stated shapes. It then checks, using arbitrary-precision
Python integers:

1. the six generators, thirteen relations, and all thirteen Fox chain rows;
2. the reconstructed `22`-element support and all `293` support products;
3. the Gram product in (6), including every residual coefficient;
4. Hermitian symmetry, all six exact row and column totals, and the strict
   clean-gap inequality.

The verification command is

```text
python3 experiments/verify_affine_hodge_certificate.py \
  --certificate experiments/sl3-sos-radius0-certificate.npz
```

For the pinned factor the expected archive SHA-256 is

```text
5b83dc59e55b89a8f48e115e06ce72deaac2bccd5c3f1ded1ead3837c26b021b
```

The verifier emits the actual digest with the integer results. This note
does not substitute a fresh execution claim for that output; the session's
remote validation artifact records any fresh run.

The preceding direct calculation is in the group ring of the concrete
integral matrix group. For an abstract group on the thirteen words, matrix
coincidence alone would be insufficient. The repository additionally
supplies
[sl3-p13-reductions-complete.json](../../experiments/sl3-p13-reductions-complete.json),
with `4124` explicit conjugated-relator atoms and at most `264` per
reduction, and
[LiteralP13HodgeReplay.lean](../../GroupApproximation/Sofic/LiteralP13HodgeReplay.lean).
Each used prefix or support-product equality has the form

```text
u v^(-1)=product_j w_j r_(i_j)^(epsilon_j) w_j^(-1),
epsilon_j in {-1,1},
```

verified by free reduction. That separate finite replay proves the same
coefficient bound for the abstract presentation too. The direct affine
argument needs only the concrete `SL_3(Z)` version established above.
