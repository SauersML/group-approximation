# A uniform first-braid gap for both three-dimensional head types

2026-09-07; dependency and scope audit 2026-09-08. This is a proved
restriction on the Jacobson joint-cell problem. It rules out all mixtures
of the two three-dimensional head types, including every dimension-twelve
packet with one such head and tail `1 directSum rho_+`. It does
not establish the all-types gap or a non-MF existence theorem.

## Statement

Let `G=GL_3(F_2)`, let `K=GL(<e_1,e_3>)` act identically on `e_2`,
and put `b=w_23`. Let `rho_+,rho_-` be the conjugate
three-dimensional irreducible representations. For arbitrary
finite-dimensional unitary representations `sigma_+,sigma_-` on
spaces `W_+,W_-`, put

```text
pi(g_Q,g_P)=(rho_+(g_Q) tensor sigma_+(g_P))
             directSum (rho_-(g_Q) tensor sigma_-(g_P)),
B=pi(b,b).
```

Either multiplicity space may vanish, but the total space is nonzero.
If `H` is any self-adjoint unitary commuting with `pi(K_Q)`,
then

```text
||(HB)^3-I||_op >= 1/4.                                  (1)
```

The two multiplicity spaces and their tail actions are unrestricted.
The involution `H` may mix the two head-isotypic summands. If only one
head type occurs, the stronger bound `1/3` holds.

## The angle between the head positive line and the overlap sign line

For the next computation, let `rho` be either one of `rho_+,rho_-`.
The existence of the two three-dimensional types and the restriction
`rho|_K=sign directSum standard` are supplied by the established
[overlap branching table](../binary-jacobson-gl3-k-branching-has-regular-counterprofile.md).
No explicit cyclotomic representation or separate mixed-packet certificate
is needed. Here is an elementary way to obtain the specific angle needed
below from this restriction and the orders of products in `G`.

The three-dimensional representation is faithful, since `G` is simple
and the representation is nontrivial. Its determinant is one, since a
simple nonabelian group has no nontrivial one-dimensional characters.
Every involution therefore has eigenvalues `1,-1,-1`.

We also need character zero at order three and character one at order
four. These follow directly from the eigenvalues. In `GL_3(F_2)`, every
element of order three is conjugate to its inverse: its rational
canonical form consists of a one-dimensional fixed block and the
irreducible block for `t^2+t+1`. Thus its character is real. Faithfulness,
dimension three and determinant one then force eigenvalues
`1,omega,omega^2` and character zero. Similarly an order-four element is
unipotent with a single size-three Jordan block, and is conjugate to its
inverse. Its square is an involution. The eigenvalues of its image,
their squares, determinant one and the reality of its character force
`1,i,-i`, giving character one.

Let `P` be the projection onto the `K`-sign line. For each of the three
involutions `k` of `K`, let `R_k=(I+rho(k))/2` be its rank-one positive
projection. These projections lie in the standard summand, and Schur's
lemma applied to their conjugacy-invariant sum gives

```text
sum_(k involution in K) R_k = (3/2)(I-P).                 (2)
```

Write `rho(b)=2vv*-I`, where `v` is a unit vector. If `R_k=uu*`, then

```text
Tr(rho(k)rho(b)) = 4 |<u,v>|^2 - 1.                     (3)
```

The three involutions of `K` are `d=w_13`, `t=I+E_13`, and
`t'=I+E_31`. Direct multiplication of their binary matrices shows that
`db` has order three, whereas `tb` and `t'b` have order four. Equations
(2)--(3) therefore yield

```text
(3/2)(1-||Pv||^2) = 1/4+1/2+1/2 = 5/4,
||Pv||^2 = 1/6.                                         (4)
```

Choose a unit vector `p` on the sign line and a unit vector `q` in the
standard summand so that
`v=sqrt(1/6)p+sqrt(5/6)q`. Complete `q` by a unit vector `r` in that
two-dimensional summand. In the basis `p,q,r`, the head involution is

```text
X=rho(b)=[[-2/3,sqrt(5)/3,0],
          [sqrt(5)/3,2/3,0],
          [0,0,-1]].                                    (5)
```

Only the conjugacy classes of products of involutions entered (2)--(4),
so the conjugate three-dimensional representation gives exactly the same
real matrix (5) in its own adapted basis.

## Both chiralities in a single overlap basis

Choose a real orthonormal basis `q,r` of the standard representation of
`K` in which the positive line of `rho(d)` is `q`. The positive lines
of `rho(t)` and `rho(t')` can then be represented by
`(q+sqrt(3)r)/2` and `(q-sqrt(3)r)/2`: these are the three reflection
axes of the standard representation of `S_3`. Choose the phase on the
sign vector `p`, the common phase on the standard summand, and the
phase of the unit vector `v` so that its `p` and `q` coordinates are
positive real numbers. Equations (3)--(4) give

```text
|v_p|^2=1/6,       |v_q|^2=1/4,       |v_r|^2=7/12.
```

The equal squared overlaps `1/2` with the other two axes imply
`Re(v_q conjugate(v_r))=0`. Thus one chirality has positive line

```text
v_+=(1/sqrt(6),1/2,i sqrt(7/12)),
```

and its conjugate has `v_-=conjugate(v_+)`. The restrictions of the
two representations to `K` are now identical real matrices. If the
original labeling has the opposite sign, interchange `+` and `-`.

Reorder the full space as three copies of
`W=W_+ directSum W_-` and put

```text
J=I_(W_+) directSum -I_(W_-),
M=sigma_+(b) directSum sigma_-(b).
```

The involutions `J,M` commute. Schur's lemma for the common
`sign directSum standard` restriction gives
`H=diag(A,C,C)`, with `A,C` arbitrary self-adjoint unitaries on `W`.
In particular, neither `A` nor `C` is assumed to commute with `J`.
The operator `B=pi(b,b)` has block matrix

```text
B=[[-(2/3)M,              M/sqrt(6),       -i sqrt(7/18) J M],
   [ M/sqrt(6),          -(1/2)M,         -i sqrt(7/12) J M],
   [ i sqrt(7/18) J M,     i sqrt(7/12) J M,   (1/6)M]].
```

For any two involutions `H,B`, multiplication by `BHB` gives
`(HBH-BHB)(BHB)=(HB)^3-I`. Write their common defect norm as
`delta`, and denote the second and third diagonal blocks of
`HBH-BHB` by `R_22,R_33`. With `d=MAM` and `e=MCM`, multiplication
gives

```text
R_22=-(1/2)CMC-(1/6)d-(1/4)e-(7/12)JeJ,
R_33= (1/6)CMC-(7/18)JdJ-(7/12)JeJ-(1/36)e.
```

Each block has norm at most `delta`. Set `D=d+2e`. The combination
that cancels `CMC` is

```text
D+7JDJ=-6R_22-18R_33.
```

Since conjugation by `J` is isometric, the reverse triangle inequality
gives

```text
6||D|| <= ||D+7JDJ|| <= 24 delta,
||D||=||A+2C|| >= 2||C||-||A||=1.
```

Therefore `delta>=1/4`, proving (1) without any restriction on mixing
the two head chiralities.

## The stronger bound for a single head type

Return to the adapted real matrix (5), which is available when only
one of the two head types occurs. In this section write `sigma` for
its full tail multiplicity representation on `W`.

Since the sign and standard representations of `K` are irreducible and
inequivalent, the commutant condition on `H` gives

```text
H=diag(A,C,C),                                          (6)
```

where `A,C` are arbitrary self-adjoint unitaries on `W`. Set
`M=sigma(b)`, so `M=M*=M^(-1)`, and `B=X tensor M`.

For any two involutions `H,B`, multiplication by the unitary `BHB`
shows

```text
(HBH-BHB)(BHB)=(HB)^3-I.
```

Consequently the two defects have the same operator norm. Write this
norm as `delta`. Every diagonal compression of `HBH-BHB` has norm at
most `delta`. The third and second head-coordinate compressions of
(5)--(6) respectively give

```text
||CMC+MCM|| <= delta,                                   (7)
||(2/3)CMC-(5/9)MAM-(4/9)MCM|| <= delta.                 (8)
```

Subtract `2/3` times the expression in (7) from the expression in (8).
The triangle inequality gives

```text
||(5/9)MAM+(10/9)MCM|| <= (5/3)delta.
```

Unitary invariance of the norm and its reverse triangle inequality now
give

```text
(5/9)||A+2C|| <= (5/3)delta,
||A+2C|| >= 2||C||-||A|| = 1.
```

This proves the stronger bound `delta>=1/3`. If the braid were exact,
the same elimination would give `A=-2C`, contradicting unitarity
immediately.

## Consequences and scope

The dimension-twelve choice `rho_+` on the head and
`sigma=1 directSum rho_+` on the tail is included. The stronger bound
proves that the first defect of every possible overlap-central involution
on this packet is at least one third. This proof makes no assertion about
an achieved upper bound on either cell's defect. Increasing only the tail multiplicities or changing only the
tail representation cannot produce vanishing braid defects with this
fixed head type. Adjoining arbitrary copies of the conjugate
three-dimensional head type, and allowing the overlap involution to mix
them, still leaves the uniform lower bound `1/4`.

One can additionally adjoin an arbitrary trivial-head summand with any
tail action. That summand consists of trivial `K`-types, whereas the
three-dimensional head part has only sign and standard `K`-types.
Consequently every allowed `H` preserves their direct-sum decomposition.
The packet operator `B` preserves it as well. Restricting to the nonzero
three-dimensional head part therefore retains the lower bound `1/4`.
Adding trivial-head summands cannot remove this obstruction.

The [exact two-braid reduction](../jacobson-joint-cells-are-two-braids.md)
identifies the second cell defect with `||(H pi(1,w_13))^3-I||`.
It proves that the maximum of the two defects is exactly two for every
nontrivial head representation when the tail acts trivially. In contrast,
the present first-braid bound permits arbitrary tail action but restricts
the head types.

The [joint shortest-cell problem](../binary-jacobson-joint-shortest-cells-have-a-finite-marked-model.md)
also allows the other nontrivial head irreducibles, and allows their
overlap types to mix with those considered here. This argument does not
control those cases. In particular, the other restrictions are
`rho_6|_K=2*1+2*standard`,
`rho_7|_K=1+2*sign+2*standard`, and
`rho_8|_K=1+sign+3*standard`. Their shared overlap types allow `H` to mix
them with the three-dimensional heads. The block formula
`H=diag(A,C,C)` and the scalar head coefficients used above consequently
do not hold on that larger space. The existing regular counterprofile
already rules out obtaining the missing conclusion from branching counts
alone.

Nor can a first-braid gap hold over all head types, even after requiring a
nontrivial head mark. In the existing
[affine-braid finite model](../binary-jacobson-shortest-affine-braid-is-finite-marked.md),
let `G_Q` act on the first three coordinates of `F_2^4`, let `G_P` act
trivially, and let `h` exchange `e_2` and `e_4`. The overlap fixes these two
vectors, so `h` commutes with `K`, and `h b=(24)(23)` has order three.
The resulting permutation representation on the fifteen nonzero vectors
is unitary and retains the head transvection. Its head restriction is
`3*1+2*rho_6`: the two orbits with a nonzero first-three-coordinate vector
each afford the seven-point permutation representation `1+rho_6`, and
the remaining vector `e_4` is fixed. Thus additional head types really can
remove the first-braid obstruction. The controlled-swap cell fails in
this model by the nonidentity residual swap `(14)`, as the cited model
computes. A possible all-types obstruction must use that second cell as
well.

This result introduces no
claim of literature priority; its purpose is an exact, dimension-free
exclusion of a live family in the existing matrix problem. The proof
uses finite-dimensional linear algebra and exact representation data;
it requires no search or numerical job.
