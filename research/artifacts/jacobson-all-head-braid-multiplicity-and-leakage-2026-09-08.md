# All-head restrictions for the Jacobson two-braid problem

This note gives necessary conditions on arbitrary finite-dimensional
packets, including mixtures of all six head irreducibles. It does not prove
existence or nonexistence of a marked two-braid completion.

Let `G=GL_3(F_2)`, `F=G_Q x G_P`, and let `K=GL(<e_1,e_3>)_Q` fix
`e_2`. In an exact unitary representation `pi` of `F`, put

```text
B=pi(w_23,w_23),              D=pi(1,w_13).
```

Let `H` be a self-adjoint unitary commuting with `pi(K)`, and write

```text
delta_B=||(HB)^3-I||_op,       delta_D=||(HD)^3-I||_op.
```

The mark is `pi(I+E_13,1)`. The two-braid group and its mark-retaining
infinite-dimensional algebraic model are specified in
[the two-braid reduction](jacobson-two-braid-reduction-2026-09-07.md).

## 1. Second-braid rank balance holds in every overlap type

Decompose the restriction to `K` as

```text
V=(1 tensor M_1) directSum (epsilon tensor M_epsilon)
                       directSum (tau tensor M_tau),
```

where `epsilon` is the sign representation and `tau` is the
two-dimensional standard representation. Since `H,D` both commute with
`K`, they have the forms `I_kappa tensor H_kappa` and
`I_kappa tensor D_kappa` on these summands.

**Proposition 1.** If `delta_D<2`, then

```text
rank_-(H_kappa)=rank_-(D_kappa)       (kappa=1,epsilon,tau).   (1)
```

Thus, for every `k in K`,

```text
Tr(H pi(k))=Tr(D pi(k)).                                  (2)
```

**Proof.** For any involutions `A,C`,

```text
(AC) A (AC)^(-1)-C=((AC)^3-I)C.
```

Apply this in each `K` multiplicity space to `A=H_kappa,C=D_kappa`.
The conjugate of the negative projection of `H_kappa` is at distance
less than one from the negative projection of `D_kappa`. Finite
projections at distance less than one have equal ranks. This proves (1).
The traces in (2) are then obtained by summing the characters of `K`
with these equal signed multiplicities. Notice that this is stronger than
equality of the total negative ranks: no cancellation between inequivalent
`K` types is allowed. The ranks remain exactly equal even with nonzero
braid error. QED.

Here is the full numerical form. Index the head and tail irreducibles by
`1,3,3bar,6,7,8`, and let `m_(alpha,beta)` be the multiplicity of
`alpha tensor beta` in `pi`. Their dimensions, involution-negative ranks,
and head restrictions are

| Type | `d_alpha` | `r_alpha` | `b_(alpha,1)` | `b_(alpha,epsilon)` | `b_(alpha,tau)` |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 0 | 1 | 0 | 0 |
| 3 | 3 | 2 | 0 | 1 | 1 |
| 3bar | 3 | 2 | 0 | 1 | 1 |
| 6 | 6 | 2 | 2 | 0 | 2 |
| 7 | 7 | 4 | 1 | 2 | 2 |
| 8 | 8 | 4 | 1 | 1 | 3 |

These are the established
[overlap branching data](../binary-jacobson-gl3-k-branching-has-regular-counterprofile.md).
Equation (1) says precisely

```text
rank_-(H_kappa)=sum_(alpha,beta) m_(alpha,beta)
                                      b_(alpha,kappa) r_beta.   (3)
```

For example, if the right side for `kappa=1` vanishes, then `H` is
exactly the identity on the entire `K`-trivial isotypic subspace. This
conclusion follows from a braid defect strictly below two, without
assuming an exact braid or that `H` preserves head types.

If also `delta_B<2`, total negative-rank comparison in the first braid,
combined with (3), recovers the necessary equation

```text
sum_(alpha,beta) m_(alpha,beta) r_alpha
                                  (d_beta-2r_beta)=0.          (4)
```

Equation (3), unlike (4), fixes the negative multiplicity in each allowed
overlap gauge before the first braid is considered.

The complete normal form and dimension-independent rounding of the second
braid are proved separately in
[the tail-braid exactification note](jacobson-tail-braid-exactification-2026-09-08.md).
The next result instead controls a different matrix block: transport out
of the two three-dimensional head types.

## 2. The first braid quantitatively forces mixing out of the two 3-types

Let `P` be the sum of the head-isotypic projections for `3` and `3bar`.
It commutes with `pi(F)` and with `K`; put

```text
m=rank(P),                   E=(I-P)HP.
```

Assume `m>0`. Let `||.||_F` denote the unnormalized Hilbert--Schmidt
norm. We first record a strengthening of the existing two-chirality
calculation:

**Lemma 2.** If the head representation has only types `3` and `3bar`,
then every overlap-central involution `J_0` satisfies

```text
||((J_0 B)^3-I)||_F >= sqrt(m/30).                       (6)
```

**Proof.** Use the simultaneous overlap basis from
[the three-dimensional-head proof](del2-three-dimensional-head-braid-gap.md).
The space consists of three copies of a multiplicity space of dimension
`m/3`. In that basis `J_0=diag(A,C,C)` and the chirality involution is
`J`. The proof gives, with `R=J_0 B J_0-B J_0 B`,

```text
D_0=d+2e,          D_0+7J D_0 J=-6R_22-18R_33,
d=MAM,             e=MCM.
```

Since `d,e` are unitaries on the same multiplicity space,
`||D_0||_F>=sqrt(m/3)`. Conjugation by `J` is isometric. Hence

```text
6 sqrt(m/3) <= 6||D_0||_F
              <= ||D_0+7J D_0 J||_F
              <= 6||R_22||_F+18||R_33||_F
              <= 6 sqrt(10) sqrt(||R_22||_F^2+||R_33||_F^2)
              <= 6 sqrt(10)||R||_F.
```

The braid residual and `R` differ by multiplication by a unitary, so
their Hilbert--Schmidt norms agree. This is (6). QED.

**Proposition 3.** For an arbitrary mixture of all head types,

```text
sqrt(m/30) <= delta_B sqrt(m)+3sqrt(2)||E||_F.           (7)
```

In particular, if the first braid is exact, then

```text
||E||_F^2 >= m/540.                                     (8)
```

**Proof.** On `PV`, the compression `A=PHP` is a self-adjoint
contraction commuting with `K`. Define `J_0=sign(A)`, taking sign zero
to be `+1`. This is an exact involution commuting with `K` on `PV`.
Because `H^2=I`,

```text
P-A^2=E*E.
```

For `-1<=t<=1`, `(sign(t)-t)^2<=(1-t^2)`. Functional calculus and
the trace give

```text
||J_0-A||_F^2 <= ||E||_F^2,
||HP-J_0||_F^2 = ||E||_F^2+||A-J_0||_F^2 <=2||E||_F^2.  (9)
```

The last expression treats `J_0` as an isometry from `PV` into `V`.
The operator `B` preserves `PV`. Telescoping the three factors in
`(HB)^3` against the isometry induced by `J_0 B|_(PV)` therefore gives

```text
||((J_0 B|_(PV))^3-I_(PV))||_F
 <= ||((HB)^3-I)P||_F+3||HP-J_0||_F
 <= delta_B sqrt(m)+3sqrt(2)||E||_F.
```

Lemma 2 applies to the left side. This proves (7), and setting
`delta_B=0` gives (8). QED.

This is a restriction on a literal matrix block of `H`, rather than on
branching dimensions alone. A small first-braid defect forces a positive
amount of mixing between the three-dimensional head types and other
nontrivial head types.

## 3. A resulting all-head dimension bound

Set `N_alpha=sum_beta m_(alpha,beta)d_beta`, so the head `alpha`
isotypic subspace has dimension `d_alpha N_alpha`. Since `H` commutes
with `K`, the image of `E` cannot enter trivial overlap types: the
source `PV` has only sign and standard types. From the branching table,
its available target dimension is at most

```text
4N_6+6N_7+7N_8.                                        (10)
```

In particular it cannot enter any trivial-head summand. Also
`||E||_op<=1`, so `||E||_F^2<=rank(E)` is bounded by (10).
For `delta_B<1/sqrt(30)`, equation (7) yields

```text
4N_6+6N_7+7N_8
 >= (N_3+N_3bar)/6 * (1/sqrt(30)-delta_B)^2.             (11)
```

For an exact first braid this becomes

```text
4N_6+6N_7+7N_8 >= (N_3+N_3bar)/180.                    (12)
```

These inequalities permit all head types and arbitrary tail actions,
and they do not assume that `H` preserves any head-isotypic summand.
They recover the impossibility of adding only trivial-head spectators to
the two 3-types and, in addition, require a definite amount of actual
off-diagonal transport into the available 6-, 7-, or 8-type reservoir.

The regular profile has ample capacity in (10), so this argument does
not decide the universal two-braid gap. Its remaining content is the
simultaneous nonlinear compatibility of that transport with (3) and the
exact tail-braid normal form.
No finite computation or new formal verification is claimed here.
