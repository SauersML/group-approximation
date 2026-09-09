# Eight native test words and an explicit repair of their S3 core

2026-09-08. Written group identities and finite-dimensional Hilbert-space
arguments, independently audited by hand. No code, numerical search, or
Lean verification was run for these results.
Hyperlinearity of `H=L_(F_2)(1,2)^x` remains unresolved.

The word definitions are those of
[the explicit Thompson compiler](leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md).
That compiler authenticates the substitution of the
[Bleak--Quick presentation, Theorem 2.1](https://arxiv.org/html/1511.02123#S2).
The new calculations below do not require another presentation theorem.

## 1. One Thompson relator is a commutator with the marked relation

Work in any group with `c^3=1`. Let `A` be arbitrary, and put

```text
D=c^(-1) A c,       K=A c,       r=K^2,
L=K^(-1)c^(-1)K^(-1)c^(-1).
```

Use `X^Y=Y^(-1)XY` and `[X,Y]=XYX^(-1)Y^(-1)`. Then

```text
D^(A D) A^(-1) = [L,r].                              (1)
```

No involution hypothesis on `A` is needed. Write `A=K c^(-1)`. Then

```text
D=c^(-1)K,       A D=K c K,
D^(A D) A^(-1)
  =K^(-1)c^(-1)K^(-1)c^(-1) K^2 c K c K^(-1)
  =L r (c K c K^(-1)).
```

But `L(c K c K^(-1))=K^(-2)=r^(-1)`, so the last factor is
`L^(-1)r^(-1)`, proving (1). In the native compiler `A=j`,
`D=gamma^2(j)`, and `r=r_*`. Consequently

```text
rho_4=[L,r_*],       ||rho_4-I|| <= 2 ||r_*-I||.       (2)
```

The estimate holds for every unitary evaluation in normalized HS or
operator norm: write the difference from identity as
`L(r_*-I)L^* r_*^*+(r_*^*-I)` and use unitary invariance.

## 2. The shorter packet has equivalent quantitative defects

The shared compiler also gives the exact identities

```text
A=a c d c^(-1) a^(-1),
A^2=a c d^2 c^(-1) a^(-1).                           (3)
```

Thus `rho_1=A^2` can be replaced by the length-at-most-16 word `d^2`,
with exactly the same defect in every unitarily invariant norm. Define

```text
T_8={r_*,d^2,rho_2,rho_3,rho_5,rho_6,rho_7,rho_8}.   (4)
```

These are eight explicitly specified native kernel words, each of length
at most `9880`. Let `E_8` be their maximum defect and `E_9` the maximum
defect of the original nine-word packet. On every unitary tuple
representing `C_3*C_2^3`,

```text
E_8 <= E_9 <= 2 E_8.                                 (5)
```

The first inequality uses (3); the second additionally uses (2). Taking
infima, either at a fixed dimension or over all frozen dimensions `24k`,
preserves both inequalities. Thus the two packets have a uniform positive
gap simultaneously, and admit vanishing-defect sequences simultaneously.
This comparison applies to arbitrary unitaries, not only native matrices.

An exact representation killing (4) kills the original nine words.
The existing Thompson argument therefore forces `c=1` in every exact
finite-dimensional unitary target. Since the frozen `C` is nontrivial,
compactness makes the minimum of `E_8` strictly positive at each fixed
`24k`. This does not prove that the infimum stays positive as `k` grows.
Nor is vanishing of this one packet sufficient for hyperlinearity of `H`:
that requires vanishing for every finite stage of the whole kernel.

## 3. An explicit repair theorem with the order-three matrix unchanged

Let `C,A` be unitaries in `M_n(C)`, with `C^3=I`. Suppose the eigenspaces
of `C` for `omega` and `omega^2`, where `omega=exp(2 pi i/3)`, have equal
dimension. The frozen `C_3` factor satisfies this hypothesis. Put

```text
epsilon=||(A C)^2-I||_2,       eta=||A^2-I||_2,
f(epsilon,eta)=sqrt((2/3)(epsilon^2+epsilon eta+eta^2)).
```

There exists a self-adjoint unitary `J` in the same dimension such that

```text
J C J=C^*,       ||J-A||_2 <= f(epsilon,eta).          (6)
```

HS norms and traces are normalized by `n`. This bound is sharp for
abstract unitary pairs with frozen `C`, including arbitrarily small
defects, as shown in Section 4. No subgroup stability theorem,
enlargement of the dimension, or deletion of a corner is assumed.

### Orthogonal projection onto the required linear space

Give matrices the real Hilbert inner product `Re tr(X^*Y)`. Define real
linear orthogonal involutions

```text
F(X)=X^*,       G(X)=C^* X^* C^*,       T(X)=C X C.
```

Then `FG=T`, `GF=T^(-1)`, and `T^3=I`. The common fixed space of `F,G`
is

```text
K={X:X=X^*, C X C=X}.                                (7)
```

Let `P` be its orthogonal projection and `S=P(A)`. Explicitly, with
`A_0=(A+A^*)/2`,

```text
S=(A_0+T(A_0)+T^2(A_0))/3.
```

Indeed `(I+T+T^2)/3` is the orthogonal projection onto `Fix(T)`, and
`FTF=T^(-1)` makes this average commute with `(I+F)/2`.
The two given defects are exactly the reflection displacements:

```text
||(I-F)A||_2=eta,       ||(I-G)A||_2=epsilon.
```

For the first equality, multiply `A-A^*` by `A`. For the second, apply
`T` to `A-G(A)` and use
`C A C-A^*=A^*((AC)^2-I)`.

For every real `t>0`, put

```text
alpha=(1+t/2)/3,       beta=(1+1/(2t))/3.
```

The following inequality holds between self-adjoint operators on the
real Hilbert space:

```text
I-P <= alpha(I-F)^2+beta(I-G)^2.                      (8)
```

To verify it, decompose into `Fix(T)` and its orthogonal complement;
both are invariant under `F,G`. On `Fix(T)`, `F=G`. Their common
positive eigenspace is `K`, where both sides vanish; on their common
negative eigenspace, the right side is `4(alpha+beta)I>=I`.

On the orthogonal complement of `Fix(T)`, `T+T^(-1)=-I`, so
`FG+GF=-I`. Here set

```text
Q=2 alpha F+2 beta G,       lambda=2 alpha+2 beta-1.
```

The chosen coefficients give

```text
Q^2=4(alpha^2+beta^2-alpha beta)I=lambda^2 I,
12 alpha beta-4 alpha-4 beta+1=0,       lambda>0.
```

Since `Q` is self-adjoint, `lambda I-Q` is positive semidefinite.
This is precisely (8) on that summand.

Applying (8) to `A` and minimizing at `t=epsilon/eta` proves

```text
||A-S||_2^2
 <= inf_(t>0)(alpha eta^2+beta epsilon^2)
  = (eta^2+eta epsilon+epsilon^2)/3.                 (9)
```

The last line uses the minimizing choice of `t`. If `eta=0`, take
`t` to infinity; if `epsilon=0`, take `t` to zero. If both vanish,
`A` itself is an admissible `J`.

### Polar completion stays in the required space

Decompose according to the three eigenspaces of `C`. Equation (7) says

```text
S = S_1 direct_sum [ 0  X  ],       S_1=S_1^*.
                   [ X* 0  ]
```

The second block acts on the `omega,omega^2` eigenspaces. They have equal
dimension, so the polar partial isometry of `X` extends to a unitary `V`
between them. Choose a sign for each zero eigenvalue of `S_1`, and set

```text
J = sign(S_1) direct_sum [ 0  V  ].
                        [ V* 0  ]
```

Then `J` belongs to `K` and `J^2=I`. It is a polar completion of `S`, so
it minimizes distance from `S` to all unitaries. Explicitly, for singular
values `s_i` every unitary `W` satisfies

```text
||S-W||_2^2 >= (1/n) sum_i (s_i-1)^2,
```

by `Re Tr(W^*S)<=sum_i s_i`. The chosen `J` attains equality, including
on the kernels. In particular `||J-S||_2<=||A-S||_2`.
Since `J-S` lies in `K` and `A-S` is perpendicular to `K`,

```text
||J-A||_2^2=||J-S||_2^2+||S-A||_2^2
           <=2||S-A||_2^2.
```

Together with (9) this proves (6). Finally `C J C=J` and `J^2=I`
imply `J C J=C^*`.

## 4. Sharpness for abstract unitary pairs with frozen C

Take the three-dimensional block

```text
C_0=diag(1,omega,omega^2),
A_theta=diag(1,exp(i theta),exp(-i theta)),
0<=theta<=pi/3.
```

Every admissible `J` exchanges the second and third eigenspaces of
`C_0`; its diagonal entries there vanish. Choosing `+1` on the first
coordinate therefore gives

```text
min_J ||A_theta-J||_2^2=4/3.
```

Meanwhile

```text
eta^2=(8/3)sin^2(theta),
epsilon^2=(8/3)sin^2(theta+2 pi/3).
```

Both displayed sines are nonnegative, and

```text
sin^2(theta)+sin^2(theta+2 pi/3)
  +sin(theta)sin(theta+2 pi/3)=3/4.
```

Thus (6) is an equality throughout this family. The defect ratio ranges
from infinity to zero, including endpoints where one defect vanishes. At
`theta=pi/6`, both defects are `sqrt(2/3)`, so the bound
`||A-J||_2<=sqrt(2) max(epsilon,eta)` has optimal constant.

For arbitrarily small defects, take a direct sum of one such block with
many exact blocks `(C_0,J_0)`, where `J_0` fixes the first coordinate
and exchanges the other two. The defects and minimum repair distance
all scale by the square root of the fraction of exceptional blocks.
Equality persists even if `J` may mix blocks: the projected matrix `S`
has singular values one on the exact blocks and the first exceptional
coordinate, and zero on the other two exceptional coordinates, so the
polar minimum proved above is unchanged. A total of `8k` triples gives
the frozen multiplicities in dimension `24k`; a unitary change of basis
identifies this `C` with the prescribed frozen matrix.

These examples establish sharpness for the abstract pair problem.
They have not been authenticated as evaluations of the native word
`A=j` in three simultaneously conjugated involutions.

## 5. A quadratic separated-root bound for the actual packet

For frozen `C`, all three eigenspaces have dimension `n/3`. Every `J`
above has zero trace on their `omega,omega^2` sum, and trace at most `1/3`
on the remaining summand. Therefore

```text
||J-I||_2^2=2-2 tr(J)>=4/3.
```

For every unitary `A` and self-adjoint unitary `J`, one also has

```text
||A-I||_2^2 >= ||J-I||_2^2-||A-J||_2^2.
```

Indeed, putting `P_+=(I+J)/2`, the left side minus the right side is
`4 tr(P_+(I-Re(A)))>=0`, because `I-Re(A)` is positive semidefinite.

Apply this inequality and (6) to `A=j`, and use (3). Every frozen-factor
tuple satisfies

```text
epsilon=||r_*-I||_2,       eta=||d^2-I||_2,

||d-I||_2^2=||j-I||_2^2
 >= 4/3-(2/3)(epsilon^2+epsilon eta+eta^2).          (10)
```

In particular

```text
E_8<=delta  ==>  ||d-I||_2^2>=4/3-2 delta^2,
                 Re tr(d)<=1/3+delta^2.
```

Thus an asymptotic solution must keep the derived constant root at
distance at least `2/sqrt(3)-o(1)` from identity, with a quadratic
defect correction to its squared distance. The coefficient `2/3` of
`epsilon^2` in (10) is sharp for abstract pairs with `eta=0`: dilute
the `theta=0` example of Section 4 among exact blocks. If the exceptional
fraction is `p`, then `epsilon^2=2p` and
`||A-I||_2^2=4/3-(4/3)p`, giving equality. No pointwise sharpness claim
is made for (10) when both defects are nonzero, and this example is
again not a native-word model.

## 6. The precise remaining mathematical problem

The finite `S_3` relations can be repaired with `C` unchanged, by (6).
But `A` is a prescribed word in three simultaneously conjugated
involutions `B_i`; it is not an independent variable. Replacing `A` by
`J` supplies no new relative unitary realizing that replacement. It also
does not prove the other six rows of (4), or control their defects after
an alteration of the original `B_i`.

The comparison (5) and bound (10) can be used without that missing lifting
step. Nonhyperlinearity still requires an all-dimensions gap for a native
kernel packet. Hyperlinearity still requires models of every finite
kernel stage. Neither is supplied here.
