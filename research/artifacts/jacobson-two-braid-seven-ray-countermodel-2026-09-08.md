# An amenable seven-ray quotient of the Jacobson two-braid group

2026-09-08. The explicit amenable quotient below retains the entire finite
packet and proves that both proposed two-braid infima are zero. It even
satisfies an additional literal nonpermutation-tail commutation relation.
This proves no non-MF existence theorem and asserts no new formal
verification or exact finite marked image.

## 1. The presentation

Let `G=GL_3(F_2)`, `F=G_Q x G_P`, and let `K` be the head copy of
`GL(<e_1,e_3>)` acting identically on `e_2`. Write

```text
b=(w_23,w_23),             d_P=(1,w_13),
w=(I+E_13,1),
Gamma=<F,h | h^2=1, [h,K]=1, (hb)^3=1, (hd_P)^3=1>.     (1)
```

Here `w_ij` is the coordinate swap. This is exactly the presentation in
[the two-braid reduction](jacobson-two-braid-reduction-2026-09-07.md).
The finite multiplication table of `F` gives a finite presentation for
the packet in (1).

## 2. Seven rays and a faithful finite packet

Let `X=F_2^3\{0}`. Label its seven elements by

```text
A_i=e_i,       B_i=sum_(j!=i) e_j       (i=1,2,3),
C=e_1+e_2+e_3.
```

The coordinate permutation subgroup `S_3<=G` preserves the two triples
`{A_1,A_2,A_3}` and `{B_1,B_2,B_3}`, permutes their subscripts in the
same way, and fixes `C`. The second assertion uses the displayed
missing-coordinate indexing of the `B_i`.

Let `V_7` be the vector space over `F_2` with basis `e_(x,n)` for
`x in X` and `n>=0`, consisting of finite-support vectors. Define an
action of the entire finite packet `F=G_Q x G_P` as follows.

The head factor `G_Q` acts naturally on the three vectors

```text
(e_(A_1,0),e_(A_2,0),e_(A_3,0))
```

and fixes every other basis vector. The tail factor `G_P` fixes level
zero. At each positive level it acts by the permutation representation
on the seven nonzero vectors:

```text
g_P e_(x,n)=e_(g x,n)       (n>=1).                     (2)
```

Both factor actions are faithful. The natural head representation is
faithful, and a matrix fixing every nonzero vector in `F_2^3` is the
identity. Their supports are disjoint, so their actions commute and
embed the direct product `F` in `GL(V_7)`.

## 3. The involution and both braid relations

Define a basis-permutation involution `H` on the `A` rays by

```text
H e_(A_2,n)=e_(A_1,n+1),
H e_(A_1,n+1)=e_(A_2,n)       (n>=0),
H e_(A_1,0)=e_(A_1,0),
H e_(A_3,n)=e_(A_3,n)         (n>=0).                  (3)
```

On each positive level of the `B` rays let it be the unshifted swap

```text
H e_(B_1,n)=e_(B_2,n),
H e_(B_2,n)=e_(B_1,n),
H e_(B_3,n)=e_(B_3,n)         (n>=1).                  (4)
```

It fixes all three `B` vectors at level zero and fixes the entire `C`
ray. These are disjoint transpositions and fixed points, so `H^2=1`.

The head subgroup `K` acts only on the plane spanned by
`e_(A_1,0),e_(A_3,0)` and fixes its coordinate complement. The
involution `H` fixes this plane pointwise and preserves the complement.
Therefore `[H,K]=1`.

On the `A` rays the action of `b=(w_23,w_23)` is the same coordinate
swap at every level. Thus `Hb` has the three-cycles

```text
(e_(A_1,n+1), e_(A_2,n), e_(A_3,n))       (n>=0),        (5)
```

and fixes `e_(A_1,0)`. On each positive `B` level its factors are
the coordinate permutations `(12)` and `(23)`, so their product is
a three-cycle. Both factors fix the `B` level zero and the `C` ray.
This proves `(Hb)^3=1` everywhere.

On the `A` rays `Hd_P` has the three-cycles

```text
(e_(A_1,n), e_(A_3,n), e_(A_2,n-1))       (n>=1),        (6)
```

and fixes `e_(A_1,0),e_(A_3,0)`. On each positive `B` level its
factors are `(12)` and `(13)`, again giving a three-cycle. Both
factors fix the `B` level zero and the `C` ray. Therefore
`(Hd_P)^3=1` everywhere as well.

Set

```text
A_7=<F,H> <= GL(V_7).                                  (7)
```

All relations of (1) hold, so mapping `h` to `H` and using (2) gives
a surjection `Gamma -> A_7` whose restriction to `F` is injective.
In particular

```text
w e_(A_3,0)=e_(A_3,0)+e_(A_1,0),                       (8)
```

so the head mark survives.

## 4. The entire quotient is amenable

Call an operator eventually a translated ray permutation if its action,
for all sufficiently large `n`, is

```text
e_(x,n) |-> e_(sigma(x),n+k_x),
sigma in Sym(X),          (k_x)_(x in X) in Z^X.         (9)
```

The head has trivial eventual action. Every tail matrix permutes the
seven rays with shifts zero. The involution `H` swaps `A_1,A_2`
with input shifts `-1,+1`, swaps `B_1,B_2` with shifts zero, and
fixes the other rays. Products retain (9), after increasing the finite
exceptional level. Inverses do too: the formula in (9) bijects the
sufficiently high portions of the input and output rays, so it determines
the inverse there. The eventual data are unique and compose as
translated permutations. They give a homomorphism

```text
nu_7:A_7 -> Z^7 semidirect S_7.                        (10)
```

An element in its kernel fixes every basis vector beyond some level.
The images of the finitely many remaining vectors involve only finitely
many coordinates. Choose a level `M` containing these supports and the
exceptional vectors. The element preserves the finite-dimensional
coordinate space of levels `0,...,M` and fixes its complement.
Its restriction is invertible because it is injective on a
finite-dimensional space.

Any finite collection of kernel elements admits a common such `M` and
therefore generates a subgroup of the finite group
`GL_(7(M+1))(F_2)`. Hence `ker(nu_7)` is locally finite. The image of
(10) is a subgroup of a virtually abelian group. Amenability of locally
finite groups, and its preservation under subgroups and extensions,
prove that `A_7` is countable amenable.

Every countable amenable group is operator MF. The literature input is
Tikuisis--White--Winter's quasidiagonality theorem, explicitly restated
as Theorem 2.3 in Schafhauser,
[Finite dimensional approximations of certain amalgamated free products
of groups](https://arxiv.org/html/2306.02498#S2), and recorded by
[amenable-implies-operator-mf](../amenable-implies-operator-mf.md).
Thus `Gamma -> A_7` followed by an MF embedding is a norm-corona
homomorphism preserving the entire finite packet.

This linear action on a vector space over `F_2` defines the abstract
amenable group used for the theorem. It is not being identified with a
finite-dimensional complex unitary representation, and the argument
does not assert that `A_7` is LEF.

## 5. Consequences for both matrix infima

The exact-packet characterization in
[the two-braid reduction](jacobson-two-braid-reduction-2026-09-07.md)
says that the infimum `gamma` is positive exactly when every
norm-corona homomorphism of `Gamma` kills `w`. Section 4 constructs a
counterexample. Hence

```text
gamma=0.                                               (11)
```

Equivalently there are exact finite-packet representations `pi_n` and
self-adjoint unitaries `H_n` commuting exactly with `pi_n(K)`, for
which the head mark is nonidentity and both braid defects tend to zero.
This uses the proved finite-packet correction, not an assumed exact
finite marked quotient of `Gamma`.

The [relative tail-braid rounding theorem](jacobson-tail-braid-exactification-2026-09-08.md)
changes only `H_n`, retains every packet matrix, and makes the tail
braid exact at a cost at most three halves of its previous defect in the
first braid. Consequently

```text
gamma_tail=0                                           (12)
```

as well. The all-head leakage and standard-carrier restrictions are
therefore compatible with marked asymptotic models and cannot force a
positive two-braid gap.

## 6. A further nonpermutation-tail commutation still admits this quotient

Put

```text
r=(I+E_13)_P,           s=(I+E_23)_P.
```

The additional relation

```text
[h r h,s]=1                                            (13)
```

holds in the literal Jacobson group. Indeed, writing
`J=F_2<S,T | TS=1>`, `P=ST`, `Q=1-P`, the literal matrices are

```text
h=[[Q,S,0],[T,0,0],[0,0,1]],
r=x_13(P),             s=x_23(P).
```

The identities `QP=0` and `TP=T` give
`h x_13(P) h=x_23(T)`, which commutes with `x_23(P)` because they
belong to the same root subgroup.

Nevertheless, (13) does not remove the amenable countermodel. On every
positive level, the tail transvections in (2) act on ray labels by

```text
r=(A_3 B_2)(B_1 C),
s=(A_3 B_1)(B_2 C).                                    (14)
```

The permutation `H` fixes `A_3,C` and swaps `B_1,B_2` at the same
positive level. Consequently conjugating the moved points of `r` by
`H` gives exactly the moved points of `s`. Both permutations fix all
other positive-level vectors. The only shifted point involving the
head boundary is `H e_(A_2,0)=e_(A_1,1)`, and `r` fixes
`e_(A_1,1)`. Thus the equality also holds at the boundary:

```text
H r H=s       in A_7.                                  (15)
```

In particular (13) holds. The enlarged finite presentation

```text
Gamma_1=<F,h | h^2=1, [h,K]=1,
                    (hb)^3=1, (hd_P)^3=1, [h r h,s]=1>
```

also surjects onto the same amenable group `A_7`, retaining the full
packet and the head mark. No universal head-collapse estimate or square
coefficient return follows from this extra same-root commutation alone.

The quotient does not preserve every literal Jacobson coefficient
interaction: (15) folds the conjugated `T` root onto the tail `P`
root. Its conclusion concerns these stated finite presentations. It
does not decide MF of `Gamma` or `Gamma_1`, the full Jacobson
head-collapse claim, or the independent non-MF existence objective.
