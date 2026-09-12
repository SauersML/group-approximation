# Global coordinates inside one modular multiplicity stratum

2026-09-08. Direct finite-dimensional proof, using the previously
constructed exact modular parameterization. No code, build, numerical
experiment, or git mutation was used. This concerns two supplied
representations in the same multiplicity stratum, rather than the
existence of a compatible endpoint for a small-defect Iwahori pair.

## 1. Statement and notation

Let `rho,rho':SL_2(Z)->U(d)` be exact, and write

```text
S=rho(s), B=rho(b), Z=S^2=B^3,
S'=rho'(s), B'=rho'(b), Z'=(S')^2=(B')^3,
s^4=1, s^2=b^3, Z^2=(Z')^2=I.
```

Suppose the eigenvalue multiplicities of `S` equal those of `S'`,
and those of `B` equal those of `B'`. Let

```text
delta=max(||S-S'||_2,||B-B'||_2),
```

with normalized matrix trace. All parameter-tuple norms are maxima.
The natural map from
`modular-vertex-charts-have-uniform-schatten-control` is

```text
Psi(H)(s)=e^(H_0)e^(H_4)S e^(-H_4)e^(-H_0),
Psi(H)(b)=e^(H_0)e^(H_6)B e^(-H_6)e^(-H_0),            (SC1)
```

where all `H_j` are anti-Hermitian, `Ad(Z)H_0=-H_0`, and
`[H_4,Z]=[H_6,Z]=0`. It is defined for all such parameters and always
gives an exact representation.

## 2. Aligning the central involutions

Put `P=(I+Z)/2` and `P'=(I+Z')/2`. They have equal rank: the
`+1`-multiplicity of `Z` is the sum of the `+1` and `-1`
multiplicities of `S`, and the same formula holds at the other
endpoint.

We use the elementary principal-angle construction for equal-rank
projections. Diagonalizing `P P' P` on `ran P` gives principal
angles `theta_j in [0,pi/2]`. The nontrivial part decomposes into
orthogonal planes with basis `u_j in ran P`, `v_j in ker P`, on
which `ran P'` is spanned by

```text
cos(theta_j)u_j+sin(theta_j)v_j.
```

At angle `pi/2`, equal ranks allow pairing the spaces
`ran P cap ker P'` and `ker P cap ran P'`. Common range and common
kernel are left fixed. Define `H_0` on each plane by

```text
H_0 u_j=theta_j v_j,       H_0 v_j=-theta_j u_j,
```

and zero on the fixed spaces. It is anti-Hermitian and off-diagonal
with respect to `P`, so it anticommutes with `Z`. Its exponential
maps `P` to `P'`, and therefore

```text
e^(H_0) Z e^(-H_0)=Z'.
```

On one such plane the squared Frobenius norms of `H_0` and `Z-Z'`
are `2 theta_j^2` and `8 sin(theta_j)^2`. Since
`theta<=pi sin(theta)/2` on `[0,pi/2]`, summing the plane estimates
and normalizing by `d` gives

```text
||H_0||_2 <= (pi/4)||Z-Z'||_2 <= (pi/2)delta,
||H_0||_op <= pi/2.                                   (SC2)
```

The last HS inequality uses the two-term telescoping estimate
`||S^2-(S')^2||_2<=2||S-S'||_2`.

Conjugate the second endpoint back by this unitary:

```text
S_tilde=e^(-H_0) S' e^(H_0),
B_tilde=e^(-H_0) B' e^(H_0).
```

Then `S_tilde^2=B_tilde^3=Z`. Since
`||e^(H_0)-I||_2<=||H_0||_2`, unitary invariance and a two-term
telescoping estimate give

```text
||S_tilde-S||_2, ||B_tilde-B||_2 <= (1+pi)delta.         (SC3)
```

## 3. A finite-spectrum alignment lemma

Let `U=sum_lambda lambda P_lambda` and
`U'=sum_lambda lambda Q_lambda` be unitaries with the same finite
set of allowed eigenvalues, with zero projections permitted, and
`rank P_lambda=rank Q_lambda` for each label. Suppose every pair of
distinct labels with `P_lambda Q_mu!=0` has
`|lambda-mu|>=gamma>0`. Define

```text
A=sum_lambda Q_lambda P_lambda.
```

It obeys `A U=U' A` and is a contraction: its summands map orthogonal
source spaces into orthogonal target spaces and each is contractive.
Writing `t=sum_lambda tr_d(P_lambda Q_lambda)`, orthogonality gives

```text
tr_d(A)=||A||_2^2=t,
||A-I||_2^2=1-t=sum_(lambda!=mu) tr_d(P_lambda Q_mu).    (SC4)
```

Each overlap trace is nonnegative. Spectral expansion gives exactly

```text
||U-U'||_2^2
 =sum_(lambda,mu) |lambda-mu|^2 tr_d(P_lambda Q_mu)
 >=gamma^2 ||A-I||_2^2.                               (SC5)
```

Take the polar partial isometry of `A`. It maps the support of
`A` in `P_lambda` to the support of `A*` in `Q_lambda`, separately
for each label. Equal projection ranks mean the corresponding
remaining kernel dimensions agree as well. Extend on each label
by any unitary between those kernels. The resulting full unitary
`W` satisfies

```text
W U W*=U',               A=W|A|.
```

The extension need not be chosen continuously. Since the singular
values of the contraction `A` lie in `[0,1]`,
`tr_d|A|>=tr_d|A|^2=t`. Therefore

```text
||W-A||_2^2=tr_d(I-|A|)^2
          =1-2tr_d|A|+t <= 1-t=||A-I||_2^2.
```

Together with `(SC5)` this proves

```text
||W-I||_2<=2||A-I||_2<=2 gamma^-1 ||U-U'||_2.           (SC6)
```

If the source and target label spaces lie in a common fixed
decomposition, all these choices can be made within that
decomposition. In particular the resulting `W` then commutes with
its projections.

Choose the anti-Hermitian principal logarithm `K` of `W`, with
spectral angles in `[-pi,pi]`. The scalar inequality
`|a|<=pi|exp(ia)-1|/2` gives

```text
e^K=W,       ||K||_2<=pi gamma^-1 ||U-U'||_2,
||K||_op<=pi.                                         (SC7)
```

Functional calculus preserves commutation with every fixed
projection that commutes with `W`.

## 4. Constructing the remaining parameters

Apply the lemma first to `S,S_tilde` and then to `B,B_tilde`.
Each corresponding pair has the same spectral multiplicities,
since the original endpoints did and the alignment was a
conjugation.

For `S,S_tilde`, an eigenvalue `lambda` determines the central
eigenspace by `lambda^2`. Thus differently labeled projections
from opposite central eigenspaces have zero overlap, and the
only possible nonzero off-diagonal overlaps have eigenvalue
distance `2`. Use `gamma=2` in the lemma, choosing the unitary
within the central eigenspaces, and call its logarithm `H_4`.

For `B,B_tilde`, the central sign is `lambda^3`; within either
sign the three allowed roots have mutual distance `sqrt(3)`.
Use `gamma=sqrt(3)` and call the resulting logarithm `H_6`.
Both logarithms commute with `Z`. They satisfy

```text
e^(H_4)S e^(-H_4)=S_tilde,
e^(H_6)B e^(-H_6)=B_tilde,
||H_4||_2 <= (pi/2)(1+pi)delta,
||H_6||_2 <= (pi/sqrt(3))(1+pi)delta.                  (SC8)
```

Together with `H_0` from `(SC2)`, formula `(SC1)` now reaches
`rho'` exactly. All three operator norms are at most `pi`, and

```text
||H||_2 <= C delta,       C=pi(1+pi)/sqrt(3).           (SC9)
```

Conversely `(SC1)` conjugates each of the two generators, so it
cannot change its eigenvalue multiplicities. This proves that
its global image is exactly the multiplicity stratum.

The conclusion is an existence statement for coordinates of any
given endpoint. It is not a continuous selection of logarithms,
a globally injective chart, or a uniform inverse-chart theorem.

## 5. An exact intermediate with an operator/rank estimate

Fix `theta>0`, and split each parameter spectrally as

```text
H_j=H_(j,lo)+H_(j,hi),
H_(j,lo)=H_j 1_(|H_j|<=theta).
```

The two pieces commute. The cutoff is an even function of the
anti-Hermitian matrix. Since `Z H_0 Z=-H_0`, it commutes with
`|H_0|` and its spectral projections, so the truncated `H_0`
still anticommutes with `Z`. The other two truncated parameters
still commute with `Z`. Hence `H_lo` lies in the admissible
parameter space and `rho_lo=Psi_rho(H_lo)` is exact.

The forward operator-norm movement estimate gives

```text
max_(g in {s,b}) ||rho_lo(g)-rho(g)||_op<=4theta.        (SC10)
```

Spectral counting gives

```text
rank H_(j,hi) / d <= ||H_j||_2^2/theta^2.              (SC11)
```

Moreover

```text
e^(H_j)-e^(H_(j,lo))
 =e^(H_(j,lo))(e^(H_(j,hi))-I),
```

so its rank is at most `rank H_(j,hi)`. The same holds with
the signs negated. Telescoping the four exponential slots
in `(SC1)` proves

```text
rank(rho'(s)-rho_lo(s))
    <=2 rank H_(0,hi)+2 rank H_(4,hi),
rank(rho'(b)-rho_lo(b))
    <=2 rank H_(0,hi)+2 rank H_(6,hi).
```

Consequently

```text
max_(g in {s,b}) rank(rho'(g)-rho_lo(g))/d
    <=4||H||_2^2/theta^2<=4C^2 delta^2/theta^2.         (SC12)
```

In particular, for `delta>0`, taking `theta=sqrt(delta)` makes
the two respective bounds `4sqrt(delta)` and `4C^2delta`.
For `delta=0` take `H=0` and `rho_lo=rho=rho'`.

The rank estimate is for each generator difference. It does
not assert that all differences are supported in a common
reducing summand. Both endpoints and the intermediate vertex
representation are exact, which is the additional conclusion
unavailable from independently truncating arbitrary generator
logarithms.

## 6. Pair extension and scope

For two modular vertices, apply the construction independently
at the two vertices and take maximum norms. The same constant
works when each vertex's generator multiplicities match those
of its supplied endpoint. The intermediate tuple is again
exact on each vertex, with the same operator and rank bounds.
There is no assertion that it preserves Iwahori compatibility,
even if the endpoints happen to be compatible.

The construction therefore supplies global nonlinear coverage
inside each given multiplicity stratum and an exact way to
separate the small and concentrated parts of a supplied change.
It does not reconcile different strata or find a compatible
endpoint from a local defect bound. Those are separate tasks.
Repository searches covered the existing stratum-reconciliation
claim, finite-spectrum rounding, exact endpoint retraction, and
the newly constructed modular charts; none supplies this
global coordinate bound and representation-preserving spectral
truncation together.
