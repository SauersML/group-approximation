# Low-energy POVMs give flexible direct-sum projection cuts

Date: 2026-09-08. Self-contained written proof. No computation,
build, or new Lean verification is used.

## 1. Supplied data and conclusion

Let `tau=Tr/d` on `M_d(C)`. Let `K` be unital,
trace-preserving, completely positive, and self-adjoint for
normalized `L^2`. Write

```text
E_K(x)=tau(x*(x-K(x))),
||x||_(1,d)=tau(|x|),       ||x||_(2,d)^2=tau(x*x).
```

The energy is nonnegative, because `K` is a self-adjoint
`L^2` contraction. Its Hilbert-space spectrum need not be
nonnegative. Suppose a finite family of effects satisfies

```text
f_i>=0,       sum_i f_i=I,
sum_i tau(f_i-f_i^2)<=gamma<1/3,
sum_i E_K(f_i)<=eta.                                    (1)
```

Every `f_i` is a positive contraction. There exist thresholds
`t_i in (1/3,2/3)` and projections `r_i=1_(f_i>t_i)` such
that

```text
B:=sum_i E_K(r_i)<=3sqrt(3eta),
S:=sum_i r_i<=3I,       ||S-I||_(1,d)<=3gamma.            (2)
```

Put `D=sum_i rank(r_i)` and `s=D/d=tau(S)`. Then

```text
1-3gamma<=s<=1+3gamma.                                 (3)
```

We use the abstract Hilbert space

```text
H_new=direct_sum_i r_i C^d.
```

Zero summands may be omitted. Its summands are orthogonal by
definition, even though the `r_i` in `M_d` may overlap.
Since `gamma<1/3`, this space is nonzero.

Given a finite list of source unitaries `U_a`, define

```text
epsilon=max_a [sum_i ||[U_a,r_i]||_(2,d)^2]^(1/2).        (4)
```

There are unitaries `V_a=direct_sum_i V_(a,i)` on `H_new`
such that every word `w` of length `L` in the generators
and their inverses satisfies

```text
||V_w-I_D||_(2,D)
 <= [sqrt(3)||U_w-I_d||_(2,d)+L epsilon]/sqrt(s),         (5)

|tr_D(V_w)-tr_d(U_w)|
 <= L epsilon/sqrt(s)+6gamma/s.                         (6)
```

Here `tr_D=Tr/D`, and each output word uses the SAME chosen
unitaries `V_a`. The number of effects does not enter these
estimates.

The construction requires the supplied POVM (1). It does
not itself supply expanding corners or a seed partition.

## 2. Simultaneous energy control by separate spectral thresholds

Fix one positive contraction `f`, and write its spectral
decomposition as `f=sum_j lambda_j e_j`, including zero
eigenspaces so that `sum_j e_j=I`. Put

```text
w_jk=tau(e_j K(e_k)).
```

Complete positivity implies positivity, so these weights
are nonnegative. Self-adjointness and unitality give

```text
w_jk=w_kj,       sum_k w_jk=tau(e_j).
```

Consequently

```text
E_K(f)=(1/2)sum_jk w_jk(lambda_j-lambda_k)^2.             (7)
```

Clip `f` spectrally to the interval `[1/3,2/3]`. Coarea
and the fact that a nonconstant clipped pair has an endpoint
with eigenvalue greater than `1/3` yield

```text
integral_(1/3)^(2/3) E_K(1_(f>t))dt
 <= sqrt(3 tau(f) E_K(f)).                              (8)
```

For completeness, the integral is one half of the weighted
sum of the absolute differences of the clipped eigenvalues.
The ordered weight of pairs incident to `1_(f>1/3)` is at
most `2tau(1_(f>1/3))<=6tau(f)`. Cauchy--Schwarz bounds
the integral by

```text
(1/2)sqrt(6tau(f))sqrt(2E_K(f)),
```

which is (8). Thus there is `t in (1/3,2/3)` with

```text
E_K(1_(f>t))<=3sqrt(3 tau(f)E_K(f)).                    (9)
```

The level-set energy is a finite step function, so the
threshold may be taken strictly inside the interval. For
`f=0`, any threshold gives the zero projection.

Choose these thresholds separately for all `f_i`. Summing
(9) and applying Cauchy--Schwarz to the index `i` gives

```text
sum_i E_K(r_i)
 <=3sqrt(3) [sum_i tau(f_i)]^(1/2)
               [sum_i E_K(f_i)]^(1/2)
 <=3sqrt(3eta).                                        (10)
```

This step pays no factor for the number of effects and no
purity deficit. In particular, the total cut energy tends
to zero as `eta` tends to zero even at fixed `gamma`.

## 3. A bounded sum controls dimensions and source multiplicity

For `0<=z<=1` and `1/3<t<2/3`,

```text
1_(z>t)<=3z,
|1_(z>t)-z|<=3z(1-z).                                  (11)
```

The second inequality follows by considering `z<=t` and
`z>t` separately. Functional calculus applies (11) to
each effect and its threshold projection. Hence

```text
r_i<=3f_i,
||r_i-f_i||_(1,d)<=3tau(f_i-f_i^2).
```

Summing the first bound and using the triangle inequality
for the second proves

```text
S<=3I,       ||S-I||_(1,d)<=3gamma,
|tau(S)-1|<=3gamma.                                    (12)
```

This proves (2)--(3). It also gives the optional estimate
`||S-I||_(2,d)^2<=6gamma`, since `||S-I||_op<=2`.
The important bound for inherited source errors is `S<=3I`,
which is an operator inequality even when individual cuts
overlap substantially.

## 4. Polar unitary repair in each selected corner

Let `U` be a unitary and `r` one of the selected projections.
Let `J_r:r C^d->C^d` be the isometric inclusion, and regard

```text
A=J_r* U J_r
```

as a square contraction on `r C^d`. Complete its polar part
to a unitary `V` on that same space. Such a completion
exists because the kernel and cokernel of a square matrix
have equal dimension. In singular values,

```text
Tr((A-V)*(A-V)) <= Tr(I-A*A),                           (13)
```

because `(1-z)^2<=1-z^2` for `0<=z<=1`.

The two summands in

```text
U J_r-J_r V=(I-r)U J_r+J_r(A-V)
```

have orthogonal ranges. Their squared Frobenius norms,
divided by `d`, therefore satisfy

```text
||U J_r-J_r V||_(2,d)^2
 <= 2tau(r U*(I-r)U r)
 = ||[U,r]||_(2,d)^2.                                 (14)
```

For the equality, the two off-diagonal blocks of the
commutator have equal squared Frobenius norm. This follows
from unitarity, or from the equal traces of `A*A` and
`AA*`. Rectangular norms here and below always mean
`Tr(T*T)/d` under the square root, using the ORIGINAL
dimension in this normalization.

Apply this construction to each pair `(U_a,r_i)`. Define
the row inclusion and output unitaries by

```text
J=(J_1 ... J_m):H_new->C^d,
V_a=direct_sum_i V_(a,i),
T_a=U_a J-J V_a.
```

Then

```text
JJ*=S,       ||J||_(2,d)^2=s,
||T_a||_(2,d)^2<=sum_i ||[U_a,r_i]||_(2,d)^2
                <=epsilon^2.                         (15)
```

The unitary list is repaired once. Inverse letters use
`V_a^-1`; their intertwining errors have the same norm,
since

```text
U_a^-1 J-J V_a^-1=-U_a^-1 T_a V_a^-1.
```

## 5. Uniform inheritance of every fixed-word relator

For a word `w` of length `L`, telescoping (15) gives

```text
T_w:=U_w J-J V_w,       ||T_w||_(2,d)<=L epsilon.        (16)
```

There is a point about the rectangular row map that must
not be omitted. The map `J` need not be an isometry on
`H_new`: different summands can have the same physical
image. Nevertheless, for every BLOCK-DIAGONAL operator
`A=direct_sum_i A_i` on `H_new`,

```text
Tr((JA)*(JA))=sum_i Tr(A_i* J_i*J_i A_i)
             =sum_i Tr(A_i*A_i)=Tr(A*A).                (17)
```

The off-diagonal blocks contribute no trace. In particular,
(17) applies to `A=V_w-I_D`. Thus

```text
sqrt(s)||V_w-I_D||_(2,D)
 =||J(V_w-I_D)||_(2,d)
 <=||(U_w-I_d)J||_(2,d)+||T_w||_(2,d).
```

By (12),

```text
||(U_w-I_d)J||_(2,d)^2
 =tau((U_w-I_d)*(U_w-I_d)S)
 <=3||U_w-I_d||_(2,d)^2.                               (18)
```

Equations (16)--(18) prove (5). The same argument applies
to a difference of two fixed words, replacing the original
relation error by `||U_w-U_v||_2` and `L` by the sum of
their lengths.

Every source relator is controlled against its original
error. It is not necessary to carry a previously compressed
source through another round of cuts. The factor three in
(18) does not grow with the number of summands.

## 6. Canonical fixed-word traces

Since each inclusion is isometric on its own summand,

```text
Tr(J V_w J*)=Tr(V_w).
```

Using (16),

```text
tau(U_w S)-s tr_D(V_w)=Tr(T_w J*)/d.
```

Rectangular Cauchy--Schwarz and (15) give

```text
|tr_D(V_w)-tau(U_w S)/s|
 <= L epsilon/sqrt(s).                               (19)
```

The original word is a unitary. Therefore (12) implies

```text
|tau(U_w S)/s-tau(U_w)|
 <= [||S-I||_(1,d)+|s-1|]/s
 <= 6gamma/s.                                         (20)
```

Combining (19)--(20) proves (6).

Consequently, for a sequence of such data with `gamma->0`,
`epsilon->0`, and source word traces converging pointwise
to a specified character, the repaired direct-sum traces
converge to the same character. Vanishing source relator
errors are inherited by (5). Both statements are for every
fixed word; no claim about words of unbounded length is
implicit.

## 7. When the channel controls source generator leakage

Suppose constants `A_a` satisfy

```text
||[U_a,x]||_(2,d)^2 <= A_a E_K(x)
for every self-adjoint x.                             (21)
```

Apply (21) to the projections `r_i` and sum. With
`A=max_a A_a`, (10) gives

```text
epsilon^2<=A B<=3A sqrt(3eta).                         (22)
```

For example, suppose

```text
K(x)=sum_a omega_a U_a x U_a*,
omega_a>0,       sum_a omega_a=1,
```

and the average is self-adjoint. Direct expansion gives,
for self-adjoint `x`,

```text
E_K(x)=(1/2)sum_a omega_a ||[U_a,x]||_(2,d)^2.
```

Thus (21) holds with `A_a=2/omega_a`, and

```text
epsilon^2 <= (6/omega_min)sqrt(3eta).                   (23)
```

There is also a heat version. For such a self-adjoint average
`M`, let `L=I-M` and `K_t=exp(-tL)`, where `t>0`.
The spectrum of `L` lies in `[0,2]`. Scalar functional
calculus, using the increasing function
`lambda/(1-exp(-t lambda))`, yields

```text
E_L(x):=<x,Lx>
 <= [2/(1-exp(-2t))] E_(K_t)(x).
```

At `lambda=0` the inequality follows by continuity. Hence
(21) holds for `K_t` with

```text
A_a=4/[omega_a(1-exp(-2t))].                           (24)
```

This constant is uniformly bounded for `t` bounded away
from zero and fixed positive generator weights. The heat
map itself is bistochastic UCP, by its exponential series
`exp(-t)sum_(k>=0)(t^k/k!)M^k`.

## 8. Original-source localization and a supplied seed partition

The following application records what the localized
idempotence hypothesis actually supplies. Suppose `p` is
a projection, `a=tau(1-p)`, and

```text
||(K^2-K)C_p||_(2->2)<=eta_0,       C_p(x)=pxp.
```

Let `p_1,...,p_m` be a SUPPLIED orthogonal partition of `p`,
and put `p_0=1-p`. Define `f_i=K(p_i)` for all indices.
These effects sum to `I`. For `i>=1`,

```text
E_K(f_i)=<Kp_i,Kp_i-K^2p_i>
 <=||Kp_i||_2 ||(K^2-K)p_i||_2
 <=eta_0 tau(p_i).
```

For the complementary seed, `||I-K||_(2->2)<=2` gives
`E_K(Kp_0)<=2tau(p_0)`. Thus

```text
sum_i E_K(f_i)<=eta_0+2a.                              (25)
```

If `beta=sum_i E_K(p_i)` is the seed partition's total
ambient energy, then

```text
sum_i tau(f_i-f_i^2)
 =sum_i <p_i,(I-K^2)p_i>
 <=2sum_i E_K(p_i)=2beta.                              (26)
```

Here `I-K^2<=2(I-K)` follows spectrally for every
eigenvalue of `K` in `[-1,1]`. Consequently the theorem
applies with `gamma=2beta` and `eta=eta_0+2a` whenever
`2beta<1/3`.

Localization is used only for inputs supported on the
original `p`. No compression is asserted to preserve its
idempotence defect. This application still requires the
low-total-energy seed partition; it does not extract one.

## 9. Exact rank comparison and the minimality boundary

For a projection `p_i`, let `f_i=K(p_i)` and let `r_i`
be any threshold projection with threshold in `(1/3,2/3)`.
Then

```text
||r_i-p_i||_2^2 <=9||f_i-p_i||_2^2
                 <=18E_K(p_i).                       (27)
```

The first inequality does not assume that `f_i` commutes
with `p_i`. To check it, use the spectral decomposition
`f_i=sum_j lambda_j e_j`, and for each nonzero `e_j` put
`alpha_j=tau(e_j p_i)/tau(e_j) in [0,1]`. The contribution
to `||f_i-p_i||_2^2`, divided by `tau(e_j)`, is

```text
(1-alpha_j)lambda_j^2+alpha_j(1-lambda_j)^2.
```

If `lambda_j` is above the threshold, the contribution to
`||r_i-p_i||_2^2` is `1-alpha_j`, and `lambda_j>=1/3`
proves the bound with factor nine. Below the threshold the
contribution is `alpha_j`, and `1-lambda_j>=1/3` proves
the same bound. The second inequality in (27) follows from
`(I-K)^2<=2(I-K)`.

For projections, the absolute trace difference is bounded
by their squared Hilbert--Schmidt distance. In particular,

```text
E_K(p_i)<tau(p_i)/36
 => (1/2)rank(p_i)<rank(r_i)<(3/2)rank(p_i).             (28)
```

If `p_i` has minimum rank among ALL nonzero projections
with `E_K(q)<c tau(q)`, and it satisfies the hypothesis of
(28), then every projection `q<=r_i` of at most half its
rank has rank strictly smaller than `rank(p_i)`. Global
minimality therefore gives `E_K(q)>=c tau(q)`.

The word ALL is necessary. If minimality was tested only
inside a retained corner or a remaining subspace, a small
projection `q<=r_i` may lie outside that tested corner.
Neither the rank estimate nor localization automatically
extends minimality to those projections. In particular,
these estimates do not prove expansion for an arbitrary
family of the selected corners.

## 10. Scope and relation to physical orthogonalization

The total energy bound (10) tends to zero independently of
the fixed purity allowance. The price of allowing physical
overlaps is explicit: the output is a direct sum with
dimension ratio (3), and the inherited traces have the
error in (6). The operator bound `S<=3I` controls source
relator errors at all these cuts simultaneously.

This differs from bounding the final boundary by repeatedly
paying a local relative cut tolerance. It also differs from
orthogonalizing a POVM at a cost controlled by its purity
deficit: no such cost is inserted into (10).

The result does not give a physically orthogonal partition
of the original matrix space, identify compatible matrix
units between different corners, or extract the initial
POVM or seed partition. It does not establish expansion
unless the additional globally quantified minimality
condition in section 9 is actually available. It proves
neither general conditional-expectation rounding nor
nonhyperlinearity.

Existing repository results on outcome-count-free POVM
orthogonalization and the current relative-cut recursion
counterexample were checked before writing this proof.
The argument above uses only finite-dimensional spectral
calculus, positivity, and the displayed estimates.
