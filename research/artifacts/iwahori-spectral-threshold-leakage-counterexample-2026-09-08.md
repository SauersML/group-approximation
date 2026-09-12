# An Iwahori spectral cut need not have small relative leakage

2026-09-08. This is a direct three-dimensional matrix calculation.
Dilution gives arbitrarily small normalized-HS defect while a specified
spectral cut, at a fixed positive threshold, has leakage proportional
to that defect. Its commutator-to-defect ratio grows as the inverse
square root of the threshold. Thus sufficiently small fixed thresholds
also fail the explicit support-erasure contraction budget, not only an
`o(defect)` leakage estimate. The whole three-dimensional
block is reducing and admits an explicit linear-cost repair. Thus this
does not obstruct a method that enlarges or otherwise replaces the cut,
or combines such surgery with a smooth correction.

## 1. A compatible positive-central endpoint

Use the modular presentation

```text
SL_2(Z)=<s,b | s^4=1, s^2=b^3>.
```

All matrices below have `S_i^2=B_i^3=I`. For these positive-central
representations, the three Iwahori differences are

```text
R_t=S_1 B_1-(S_2 B_2)^2,
R_l=(S_1 B_1^*)^2-S_2 B_2^*,
R_z=S_1^2-S_2^2=0.                                  (1)
```

On an orthonormal basis `e_1,e_2,e_3`, let

```text
S=diag(1,-1,-1),
B e_1=e_2,       B e_2=e_3,       B e_3=e_1,
S_1=S_2=S,       B_1=B,           B_2=B S B.          (2)
```

These are exact modular vertices. Both `SB` and `BSB` are signed
three-cycles whose signs multiply to one, so both have order three.
Consequently

```text
(S_2 B_2)^2=((SB)^2)^2=SB,
S_2 B_2^*=S B^* S B^*=(SB^*)^2.
```

Thus (1) vanishes. The first vertex generates the tetrahedral group
`C_2^2 semidirect C_3 ~= A_4`: its diagonal four-group is generated
by the three `B`-conjugates of `S`. This three-dimensional representation
is irreducible, since the diagonal four-group has three distinct
coordinate characters and `B` permutes them transitively. Irreducibility
is only descriptive here; the counterexample uses the displayed matrices.

## 2. Perturb just one torsion generator

Let `O_t` be the real rotation in the `e_1,e_2` plane which sends
`e_1` to `cos(t)e_1+sin(t)e_2`, and put

```text
S_t=O_t S O_t^*,
q_t=(S_t,B,S,BSB).
```

This is an exact pair of modular vertices for every real `t`, with
positive center and unchanged torsion multiplicities. Write

```text
c=cos(2t),       s=sin(2t),       d=c-1,
a=d^2+s^2=4 sin(t)^2.
```

Then

```text
S_t = [ c   s   0 ]
      [ s  -c   0 ]
      [ 0   0  -1 ],

R_t = (S_t-S)B,
R_l = [ -s   sc    s^2 ]
      [  d   s^2  -cs  ]
      [  0   -d    -s  ].                            (3)
```

Here the subscript on `R_t` names the upper-unipotent row, whereas
the real parameter is the same `t` used in `S_t`. Formula (3) follows
by squaring `S_t B^*` and subtracting `(SB^*)^2`.

Consider the right residual energy used by the commuting-support
construction:

```text
T(t)=R_t^*R_t+R_l^*R_l+R_z^*R_z.
```

Direct multiplication, using `s^2+c^2=1`, gives

```text
T(t) = [ 2a   -s^2     ds    ]
       [ -s^2   a      ds    ]
       [  ds    ds   a+2s^2  ],

Tr T(t)=4a+2s^2.                                    (4)
```

For example, `R_t^*R_t=a diag(1,0,1)`, while the first and
second off-diagonal entries of `R_l^*R_l` are `-s^2` and `ds`.
In particular

```text
T(t)/(4t^2) --> M = [ 2  -1   0 ]
                    [ -1  1   0 ]
                    [ 0   0   3 ]                    (5)
```

as `t` tends to zero through nonzero values. The eigenvalues of `M`
are

```text
(3-sqrt(5))/2,       (3+sqrt(5))/2,       3.
```

They are positive and distinct. The number `11/4` lies strictly
between the last two eigenvalues. Thus for all sufficiently small
nonzero `t`,

```text
P(t)=1_((11t^2,infinity))(T(t))
```

has rank one, and by finite-dimensional spectral continuity

```text
P(t) --> E_33.
```

This projection does not nearly reduce the generators as `t` tends
to zero. Specifically,

```text
||(I-P(t)) B P(t)||_F --> 1,
||[P(t),B]||_F --> sqrt(2).                           (6)
```

The limits follow from `B e_3=e_1`. Here `||.||_F` denotes the
unnormalized Frobenius norm.

## 3. A fixed positive threshold and vanishing HS defect

Choose one sufficiently small `t_0>0` for which the above rank and
leakage conclusions hold, and fix the energy threshold

```text
theta=11t_0^2>0.
```

For every `n>=3`, adjoin `n-3` trivial coordinates to `q_(t_0)`.
Call the resulting exact modular pair `q_n`. Put

```text
e_n^2=sum_j ||R_j(q_n)||_(2,n)^2,
P_n=1_((theta,infinity))(sum_j R_j(q_n)^* R_j(q_n)).
```

If `a_0=4sin(t_0)^2` and `s_0=sin(2t_0)`, equations (4)--(6)
give the exact identities

```text
e_n=sqrt(4a_0+2s_0^2)/sqrt(n) --> 0,
P_n=P(t_0) direct-sum 0_(n-3),
rank(P_n)=1,
||(I-P_n) B_1(q_n) P_n||_(2,n)
  =||(I-P(t_0)) B P(t_0)||_F/sqrt(n).                 (7)
```

Consequently the ratio of this leakage to `e_n` is the fixed positive
number

```text
||(I-P(t_0)) B P(t_0)||_F / sqrt(4a_0+2s_0^2).        (8)
```

The same conclusion holds for commutator leakage, or its maximum over
the four vertex generators. There is no function `omega(x)->0` which
bounds that maximum by `omega(e_n)e_n` for this fixed-threshold family.
Replacing the Hilbert tuple defect by the maximum residual norm changes
only fixed factors.

The commutator ratio has a precise threshold dependence. Write `q_(n,theta)`
and `P_(n,theta)` for this family with `t_0=sqrt(theta/11)`, and retain
`e_(n,theta)` for its Hilbert tuple defect. For each fixed `theta`,
the normalized factors `n^(-1/2)` cancel, so

```text
||[P_(n,theta),B_1(q_(n,theta))]||_(2,n)/e_(n,theta)
  = ||[P(t_0),B]||_F / sqrt(4a_0+2s_0^2)
  ~ sqrt(11/12)/sqrt(theta)             as theta -> 0. (9)
```

Indeed the numerator tends to `sqrt(2)` by (6), while the denominator
is asymptotic to `sqrt(24)t_0` by (4). The ratio and its asymptotic
are independent of `n`. Equivalently, multiplying the left side
by `sqrt(theta)` gives the positive limit `sqrt(11/12)`.

This directly tests the sufficient budget in
[the support-erasure theorem](../iwahori-support-erasure-has-linear-commutator-leakage.md).
Use its maximum-residual convention

```text
e_max=max_j ||R_j(q_(n,theta))||_(2,n) <= e_(n,theta),
kappa_2=max_U ||[U,P_(n,theta)]||_(2,n),
h=max_j ||(I-P_(n,theta)) R_j(q_(n,theta))
                         (I-P_(n,theta))||_(2,n).
```

For the three rows (1), the maximum total length of the two words
is `L=6`. More generally, for any fixed `L>0`, (9) implies that
all sufficiently small fixed positive thresholds satisfy, for every
`n>=3`,

```text
4L kappa_2 > e_(n,theta)/2 >= e_max/2.
```

Since `h>=0`, these cuts fail `h+4L kappa_2<=e_max/2`
regardless of the retained residual. This is failure of that
sufficient budget for this raw cut, not a claim that every possible
erasure output fails to contract.

This is compatible with the usual rank estimate:

```text
rank(P_n)/n <= e_n^2/theta.
```

Small spectral rank does not make the leakage a smaller order than
the residual. The argument supplies such examples for every sufficiently
small positive threshold `theta`: choose `t_0=sqrt(theta/11)` and
then keep it fixed while increasing `n`.

## 4. The threshold and repair boundaries

There are two different limiting procedures. If `t->0` in dimension
three and the threshold is `11t^2`, the selected projection has leakage
bounded away from zero, while the residual tends to zero. In contrast,
at any fixed positive threshold, this shrinking-amplitude family
eventually has empty high spectral cut. That first limiting procedure
alone would say nothing against fixed-threshold surgery. Section 3
instead fixes both the nonzero amplitude and its positive threshold,
and obtains small normalized-HS defect solely by dilution.

Also, the exact support `1_((0,infinity))(T(t))` is the whole
three-dimensional block for small nonzero `t`, since (5) is positive
definite. After dilution that full block reduces every generator.
Thus this example does not refute leakage control for the exact common
support. It refutes an automatic relative-leakage estimate for the
specified nonzero spectral threshold.

Enlarging `P_n` to the whole three-dimensional block gives a reducing
projection of rank three. Replacing both vertices by identities on
that block produces a compatible pair and costs at most `2sqrt(3/n)`
per generator. At fixed `t_0` this is linear in `e_n`, with a constant
depending on `t_0`.

There is an even simpler repair with a constant independent of `t_0`:
replace only `S_1=S_(t_0)` by the already supplied `S_2=S`. This
returns the compatible pair (2), and its sole generator movement is

```text
||S_(t_0)-S||_(2,n)=sqrt(2a_0/n) <= e_n/sqrt(2).      (10)
```

Therefore no failure of strict or flexible repair, or of the combined
low-rank and polynomial method, follows. A sufficient leakage-controlled
support selection must do more than take this raw spectral cut; this
finite example allows enlargement or direct smooth repair to do that
additional work.
