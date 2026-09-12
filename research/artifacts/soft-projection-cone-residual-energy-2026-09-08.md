# Energy and dual certificates for soft projection cones

Date: 2026-09-08. Self-contained written finite-dimensional proof.
No computation, build, or new Lean verification is used.

## 1. The operator bound can be removed after taking a square root

Let `tau=Tr/d` on `M_d(C)`, and let `K` be self-adjoint,
bistochastic, and UCP. Define

```text
E_K(x)=tau(x*(x-K(x))).
```

This is a nonnegative quadratic form, and its square root is a
seminorm. The `L^2` spectrum of `K` may contain negative values.

For projections `q_i` and nonnegative real weights `w_i`, put
`S=sum_i w_i q_i`. We prove

```text
E_K(sqrt(S))<=2sum_i w_i E_K(q_i),
E_K((I-S)_+)<=8sum_i w_i E_K(q_i).                     (1)
```

There is no hypothesis on `||S||_op`, the number of terms,
or their weights.

First recall an elementary Hilbert--Schmidt functional-calculus
estimate. If `A,B` are self-adjoint and `f` is scalar Lipschitz
with constant `L` on their spectra, then

```text
||f(A)-f(B)||_F^2<=L^2||A-B||_F^2.                     (2)
```

Indeed, writing their spectral projections as `P_j,Q_k`,
the two sides before the inequality have respective expressions

```text
sum_jk |f(lambda_j)-f(mu_k)|^2 Tr(P_j Q_k),
sum_jk |lambda_j-mu_k|^2 Tr(P_j Q_k).
```

All weights `Tr(P_j Q_k)` are nonnegative. This proves (2)
without assuming the two matrices commute.

For two rectangular matrices `A,B` of the same shape, apply (2)
with `f(z)=|z|` to their Hermitian dilations

```text
H_A=[0 A; A* 0],       H_B=[0 B; B* 0].
```

The absolute value of `H_A` is block diagonal, with entries
`sqrt(AA*)` and `sqrt(A*A)`. Since
`||H_A-H_B||_F^2=2||A-B||_F^2`, dropping the nonnegative
lower-right contribution gives

```text
||sqrt(AA*)-sqrt(BB*)||_F^2<=2||A-B||_F^2.              (3)
```

Now take `A` to be the row `(sqrt(w_i)q_i)_i`, so `AA*=S`.
For a unitary `U` on `C^d`, let

```text
B=U A (direct_sum_i U*).
```

Then `BB*=U S U*`. Dividing (3) by the ORIGINAL dimension
`d`, not by the column dimension, proves

```text
||[U,sqrt(S)]||_2^2<=2sum_i w_i||[U,q_i]||_2^2.         (4)
```

For each self-adjoint `H`, substitute `U=exp(itH)`, divide
by `t^2`, and take `t->0`. Finite-dimensional differentiation
gives the same estimate with `U` replaced by `H` inside
the commutators.

Every self-adjoint bistochastic UCP map has a self-adjoint
Kraus representation

```text
K(x)=sum_a H_a x H_a,       H_a=H_a*,       sum_a H_a^2=I.
```

To verify this, start with any Kraus representation
`sum_a v_a* x v_a`. Self-adjointness says the adjoint
representation `sum_a v_a x v_a*` gives the same map.
Average the two and replace each `v_a` by its real and
imaginary self-adjoint parts. Bistochasticity gives the
displayed sum of squares. Direct expansion then gives

```text
E_K(x)=(1/2)sum_a ||[H_a,x]||_2^2.                    (5)
```

Summing the differentiated (4) over these Kraus operators
proves the first inequality of (1).

Finally, `f(z)=(1-z^2)_+` is 2-Lipschitz on `[0,infinity)`.
Applying the spectral version of (2) to commutators, or
differentiating it under unitary conjugation, shows

```text
E_K(f(sqrt(S)))<=4E_K(sqrt(S)).
```

Since `f(sqrt(S))=(I-S)_+`, this proves the second inequality
of (1).

## 2. Closed-cone least-squares minimization

Let `F` be an arbitrary selected family of nonzero projections
such that

```text
E_K(q)<=h tau(q)       for every q in F,       h>=0.     (6)
```

The family may impose further conditions, such as a specified
projection-expansion test. Those conditions are not discarded.
Let `C` be the CLOSED conic hull of `F`: the closure, in the
finite-dimensional matrix space, of all finite nonnegative
linear combinations of its elements. In particular `C` is
closed, convex, nonempty, and contained in the positive cone.

There is a unique minimizer

```text
S=argmin_(T in C) ||I-T||_2^2.                         (7)
```

Existence follows by restricting to a bounded sublevel set
of the coercive objective and using finite-dimensional
compactness. Uniqueness follows from strict convexity.
Define

```text
Delta=||I-S||_2^2,       X=I-S,       R=X_+.
```

Scaling `S` by any nonnegative scalar remains feasible.
Differentiation of the objective at scale one gives
`tau((S-I)S)=0`, including the case `S=0`. Hence

```text
tau(S^2)=tau(S),
Delta=1-tau(S),       0<=Delta<=1.                     (8)
```

For any `q in F`, `S+tq` is feasible for `t>=0`.
The right derivative at `t=0` is nonnegative, yielding

```text
tau(Xq)<=0       for every allowed q.                  (9)
```

Thus a positive value of this linear functional certifies
that a candidate projection is not already an allowed
direction of the cone.

For a finite conic sum `T=sum_i w_i q_i`, (1) and (6)
give `E_K(sqrt(T))<=2h tau(T)`. Approximate `S` by finite
conic sums. Trace, square root, and energy are continuous
in finite dimension, so

```text
E_K(sqrt(S))<=2h tau(S),
E_K(R)<=8h tau(S)<=8h.                                (10)
```

This limit argument justifies the estimates for an infinite
pool without assuming an exact finite decomposition of the
minimizer or a uniform bound on the number of summands.

## 3. The positive residual carries uncovered mass and dual gain

Because `S>=0`, one has `0<=R<=I`. Also

```text
tau(R)>=tau(X)=Delta,
tau(XR)=tau(R^2)>=tau(R)^2>=Delta^2.                   (11)
```

The last inequality is trace Cauchy--Schwarz with `tau(I)=1`.
The spectral bound `0<=I-K<=2I` on Hilbert space gives

```text
E_K(X)<=2||X||_2^2=2Delta.
```

Energy Cauchy--Schwarz and (10)--(11) therefore prove

```text
tau(X K(R))
 =tau(XR)-<X,(I-K)R>
 >=tau(R^2)-sqrt(E_K(X)E_K(R))
 >=Delta^2-4sqrt(h Delta)
 =:g.                                                 (12)
```

No estimate of `||X||_op` has been used. This is important:
the least-squares sum can have large eigenvalues even though
`tau(S^2)=tau(S)<=1`.

## 4. The actual mixed-norm defect sharpens this residual

Put

```text
delta=||K^2-K||_(infinity->2),       Y=K(R).
```

Since `R` is a positive contraction, so is `Y`, and
`tau(Y)=tau(R)`. Its energy satisfies

```text
E_K(Y)=<K(R),K(R)-K^2(R)>
 <=||K(R)||_2 ||(K^2-K)(R)||_2
 <=delta sqrt(tau(R))
 <=delta.                                             (13)
```

Here `||K(R)||_2<=||R||_2<=sqrt(tau(R))`. Thus (13)
uses only the stated mixed norm. It does not require a
global `2->2` bound on `K^2-K`.

If a localized bound is available on a physical corner,
it cannot automatically be applied to this `R`: there is
no general reason for `R` to be supported in that corner.
Equation (13) avoids that issue completely.

For `0<t<1`, let `q_t=1_(Y>t)` and

```text
G(t)=tau(Xq_t),       b(t)=E_K(q_t).
```

The spectral projections of `Y` give nonnegative symmetric
weights `w_jk=tau(e_j K(e_k))`, with total ordered weight
one. Spectral coarea and Cauchy--Schwarz yield

```text
integral_0^1 b(t)dt
 =(1/2)sum_jk w_jk |lambda_j-lambda_k|
 <=sqrt(E_K(Y)/2)
 <=sqrt(delta/2)=:B.                                  (14)
```

Meanwhile layer cake and (12) give

```text
integral_0^1 G(t)dt=tau(XY)>=g,
|G(t)|<=||X||_2||q_t||_2<=sqrt(Delta).                 (15)
```

The function `G` may be negative at some thresholds. The
selection below explicitly allows this.

Assume `g>0` and first `delta>0`. Set

```text
A=2sqrt(Delta) B/g.
```

By (14), the set of thresholds with `b(t)>A` has Lebesgue
measure at most `B/A`. Its integral of `G` is therefore
at most `sqrt(Delta)B/A=g/2`. Subtracting that integral
from (15) shows

```text
integral_({t:b(t)<=A}) G(t)dt>=g/2.
```

The domain of integration has measure at most one.
All functions involved are finite step functions. Hence
there is a threshold strictly between zero and one with

```text
tau(Xq_t)>=g/2,       E_K(q_t)<=A.                     (16)
```

By Cauchy--Schwarz and `||X||_2^2=Delta`, this also gives

```text
tau(q_t)>=g^2/(4Delta),
E_K(q_t)/tau(q_t)
 <=8Delta^(3/2)sqrt(delta/2)/g^3.                      (17)
```

If `delta=0`, (14) says `b(t)=0` almost everywhere.
Equations (15) and the same finite-step-function argument
give a threshold of zero energy and gain at least `g/2`.
Thus (16)--(17), with their zero right-hand energy bound,
remain valid at zero defect.

For example, `h<Delta^3/16` makes `g` positive. If the
uncovered mass stays bounded away from zero and this
strict inequality is maintained with a fixed margin,
the selected projection has positive trace bounded away
from zero and energy tending to zero with `delta`.

## 5. What this changes in projection selection

The estimate for `sqrt(S)` permits a soft least-squares
cone rather than an operator-order packing constraint
`S<=I`. The bounded residual `R=(I-S)_+` carries the
uncovered mass and can be sharpened using the ACTUAL
mixed-norm idempotence defect. None of these estimates
repeatedly pays the boundary of a remaining physical corner.

The cone must retain the desired seed requirements. If
the pool contains all low-energy projections, it contains
`I`, so the minimizer is already `I` and the residual
vanishes. In an expanding-seed application, `I` is included
only if it satisfies the specified expansion condition.

There is a second, related limitation. Even when `Delta>0`,
positive dual gain and low energy alone do not certify
expansion: `I` always has `E_K(I)=0` and
`tau(XI)=Delta>0`. The threshold obtained above may fail
the pool's additional requirements, and its positive
gain only proves, by (9), that it is outside the pool.
The argument does not assert it can be added as an
admissible expanding direction.

Thus the remaining task is to turn the controlled residual
into projections that satisfy the chosen expansion test,
or to obtain an admissible decomposition preserving enough
of its dual gain. That step is not supplied by (1)--(17).
No expanding component decomposition, conditional-expectation
rounding theorem, or nonhyperlinearity conclusion is claimed.

The proof is elementary and uses no external approximation
theorem. It is recorded for the unbounded soft-sum estimate,
the closed-cone variational identities, and their precise
connection to the native mixed-norm hypothesis.

## 6. Rational weights give an actual amplified corner model

The soft sum can also be used directly to construct finite
matrix models. This avoids a purity requirement on the effects
`w_i q_i`. Begin with a finite family of projections and rational
nonnegative weights

```text
w_i=k_i/M,       k_i nonnegative integers,       M>=1,
S=sum_i w_i q_i,       beta=||S-I||_2,       s=tau(S)>0.
```

Zero-weight terms can be omitted. Take the abstract direct sum

```text
H_new=direct_sum_i (q_i C^d)^(direct_sum k_i),
D=dim(H_new)=sum_i k_i rank(q_i)=Md s.                 (18)
```

Thus `s` is the dimension ratio to `M` copies of the original
space. The amplification factor `M` need not be bounded.
For each summand, let `J_(i,j)` be `1/sqrt(M)` times its
natural inclusion into `C^d`, and let `J` be the row of these
maps. Then

```text
JJ*=S,       ||J||_(2,d)^2=s.                         (19)
```

Here and below a rectangular matrix's norm `||.||_(2,d)`
means its unnormalized Frobenius norm divided by `sqrt(d)`.
In particular, for EVERY block-diagonal operator `A` on
`H_new`, with the specified copy decomposition,

```text
||JA||_(2,d)^2=Tr_D(A*A)/(Md)=s||A||_(2,D)^2.          (20)
```

To see this, sum the Frobenius squares of the column blocks
`J_(i,j) A_(i,j)`. Each inclusion is an isometry up to
the factor `1/sqrt(M)`. Physical overlaps between different
`q_i C^d` do not create cross terms in this sum of column
block norms. Equation (20) does not assert that `J` is an
isometry on arbitrary vectors.

Let `U_a` be any finite family of source unitaries and put

```text
epsilon^2=max_a sum_i w_i||[U_a,q_i]||_(2,d)^2.        (21)
```

For each corner compress `U_a` to `q_i C^d` and complete its
polar decomposition to a unitary `V_(a,i)` there. If the
singular values of `q_i U_a q_i` on this space are `sigma_j`,
then they lie in `[0,1]`, and direct expansion gives

```text
||U_a inclusion_i-inclusion_i V_(a,i)||_F^2
 =2sum_j(1-sigma_j)
 <=2sum_j(1-sigma_j^2)
 =||[U_a,q_i]||_F^2.                                 (22)
```

The equality in the first line uses a polar unitary completion;
the kernels of the square compression have equal dimension,
so such a completion exists. Let `V_a` repeat `V_(a,i)` on
each of its `k_i` copies. Equations (21)--(22) imply

```text
||U_a J-J V_a||_(2,d)<=epsilon.                       (23)
```

The same bound holds for the inverse generators, since
`U_a^-1 J-J V_a^-1=-U_a^-1(U_a J-J V_a)V_a^-1`.
Consequently a length-`L` word `w` satisfies

```text
||U_w J-J V_w||_(2,d)<=L epsilon.                    (24)
```

Put `a_w=||U_w-I||_(2,d)`. For `A=U_w-I`, one has
`||A||_op<=2` and `||A*A||_2<=2||A||_2=2a_w`. Thus

```text
||(U_w-I)J||_(2,d)^2
 =tau(A*A S)
 <=a_w^2+2a_w beta.                                  (25)
```

Using (20), (24), and (25) gives the claimed word estimate

```text
||V_w-I||_(2,D)
 <=[sqrt(a_w^2+2a_w beta)+L epsilon]/sqrt(s).          (26)
```

For traces, the block-diagonal structure gives
`tau_d(J V_w J*)=Tr_D(V_w)/(Md)=s tr_D(V_w)`.
Multiply the intertwining error in (24) by `J*` and use
Hilbert--Schmidt Cauchy--Schwarz and (19) to obtain

```text
|s tr_D(V_w)-tau_d(U_w S)|<=L epsilon sqrt(s).
```

Moreover,

```text
|tau_d(U_w S)/s-tau_d(U_w)|
 <=[|tau_d(U_w(S-I))|+|1-s| |tau_d(U_w)|]/s
 <=(beta+|1-s|)/s.
```

Together these prove

```text
|tr_D(V_w)-tr_d(U_w)|
 <=L epsilon/sqrt(s)+(beta+|s-1|)/s.                  (27)
```

If the source generators satisfy a supplied energy domination
`||[U_a,x]||_2^2<=A_0 E_K(x)` for self-adjoint `x`, and all
chosen projections satisfy (6), then

```text
epsilon^2<=A_0 sum_i w_i E_K(q_i)<=A_0 h s.           (28)
```

In a sequence of such constructions with `beta->0`, `h->0`,
and uniformly bounded `A_0`, both fixed-word errors and
canonical fixed-word traces are inherited by (26)--(28).
More generally only `beta->0` and `epsilon->0` are needed.
The new dimensions may be large multiples of the old ones.
Exact source relations other than unitarity are not asserted
to remain exact after polar repair.

For a cone minimizer in Sections 2--4, the parameters are
`beta=sqrt(Delta)` and `s=1-Delta`. If it is a finite
rational sum and `Delta<1`, (26)--(27) specialize to

```text
||V_w-I||_(2,D)
 <=[sqrt(a_w^2+2a_w sqrt(Delta))+L epsilon]/sqrt(1-Delta),

|tr_D(V_w)-tr_d(U_w)|
 <=L epsilon/sqrt(1-Delta)+(sqrt(Delta)+Delta)/(1-Delta).
                                                               (29)
```

No rationality or finite-generation assumption on the cone
is necessary for the limiting consequence. At each fixed
matrix dimension, first approximate its minimizer by a finite
conic sum, as in Section 2. Then approximate its finitely many
nonnegative weights by nonnegative rationals with a common
denominator. The sum, its normalized trace, its distance to
`I`, and every weighted commutator energy are continuous
under these finite weight changes. The estimates (26)--(28)
apply to the rational sums without requiring that they remain
exact minimizers. In a sequence of dimensions, the two
approximations can be chosen at each coordinate with errors
tending to zero. No uniform bound on the denominators or
numbers of summands is needed.

This is a concrete use of weighted cone coverage and removes
the POVM-purity prerequisite for this amplified construction.
It still requires a projection pool whose cone approaches
`I` and whose weighted boundary is small. If expanding corners
are needed, they must be supplied by further properties of
that pool and a separate check after polar repair. Neither
coverage by expanding projections nor expansion of the
threshold in Section 4 has been proved here.
