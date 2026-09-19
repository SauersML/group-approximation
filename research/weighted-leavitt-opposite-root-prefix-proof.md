---
rg: 2
id: weighted-leavitt-opposite-root-prefix-proof
kind: route
title: Expand differently weighted rows into prefix coordinates over the finite Leavitt core
target: weighted-leavitt-opposite-root-packets-have-finite-models
requires: []
---

The degree-zero algebra `L_0` is the increasing union of finite matrix
rings. At level `N`, its matrix units are `s_u t_v` for `|u|=|v|=N`;
the relation `s_u t_v=sum_i s_(ui)t_(vi)` embeds one level into the next.
Every homogeneous degree-zero element belongs to some level, by the
Leavitt relations and the normal form consisting of sums of `s_u t_v`.

Choose an integer `ell` such that `n_i=ell+a_i>=0`, and put
`D=sum_i 2^(n_i)`. Form rectangular matrices

```text
T_((i,u),j)=delta_(i,j)t_u,       |u|=n_i,
S_(i,(j,v))=delta_(i,j)s_v,       |v|=n_j.
```

The prefix inverse and range-sum identities give `TS=I_D`, `ST=I_m`.
Thus `Phi(X)=TXS` is a ring isomorphism onto its image, with inverse
`Y -> SYT`. For `X in B(a)`, each image entry has degree

```text
deg(t_u X_ij s_v)=-n_i+(a_i-a_j)+n_j=0.
```

Conversely, `SYT` has its `(i,j)` entry in degree `n_i-n_j=a_i-a_j`
when `Y` has degree-zero entries. Hence

```text
B(a) ~= M_D(L_0).                                      (WOP3)
```

Every finite inventory on the right belongs to one finite matrix ring.
For a finite group-generator inventory include its inverses too; their
images are units of that same finite ring. This proves local finiteness of
the unit group without any analytic or representation-theoretic input.

For weights `(0,r,0)`, take `ell=0`, so `D=k+2`. Label the new coordinates
by `1`, the `k` prefixes `u`, and `3`. The three families become

```text
Phi(X_u)=I+E_(1,u),
Phi(Y_u)=I+E_(u,3),
Phi(Z)=I+E_(3,1).
```

The directed graph `1 -> u -> 3 -> 1` is strongly connected. Repeated
elementary commutators along simple paths produce every elementary matrix
over `F_p`; powers supply its scalar coefficients. Thus these generators
give exactly `SL_(k+2)(F_p)`. The reverse native arms are already present:
`[Y_u,Z]=x_21(s_u)` and `[Z,X_u]=x_32(t_u)`.

For an actor, the same map gives

```text
Phi(D_g)=diag(1,g^(-1),c_g).
```

Its entries belong to the level-`r` finite core `M_k(F_p)`. So all actors,
native arms, and opposite roots together lie in
`GL_(k(k+2))(F_p)` after that core expansion. No multiplication law for
the indexed actor family is used.

The image of `w=x_13(1)` is a nontrivial elementary matrix. A regular
representation of the resulting finite group therefore has trace zero on
`w` and squared normalized HS distance two from the identity.

For an active corner, the assignment `1 -> A`, with all branch operators
in `ARA`, gives a homomorphism from the abstract Leavitt algebra to that
corner. Extend its matrix-unit action by the identity on `1-A`. An image of
the locally finite unit group is locally finite, and `I+AE_13!=I` since
`A!=0`. This proves the marked conclusion without asserting faithfulness
or local finiteness for the full ambient Steinberg group.

For `(WOP4)`, write the depth-one generators as `X_i,Y_i`, the depth-two
generators as `X_(ij),Y_(ij)`, and `Z=x_31(1)`. The prefix convention gives

```text
[X_i,Y_i]=x_13(1),
[X_i,Y_(ij)]=x_13(s_j),
[X_(ij),Y_i]=x_13(t_j).                                 (WOP5)
```

The constant opposite pair `x_13(1),Z` supplies the `(1,3)` Weyl word,
so `x_31(t_i)` is available up to a sign corrected by inversion.
Also `[Z,X_i]=x_32(t_i)`. Therefore

```text
[x_13(s_i),x_32(t_i)]=x_12(s_i t_i),
[Y_i,x_31(t_i)]=x_21(s_i t_i).
```

Root additivity and `s_0t_0+s_1t_1=1` give both `x_12(1)` and
`x_21(1)`. Together with the constant `(1,3)` pair these generate the
constant `SL_3(F_p)`, including its Weyl permutations. Conjugating the raw
`s_i,t_i` roots in `(WOP5)` now supplies them in every root position.
Finally, root additivity and

```text
[x_ab(u),x_bc(v)]=x_ac(uv)             for distinct a,b,c
```

inductively supply every polynomial coefficient in every root position.
These are all elementary generators of `EL_3(L_2(F_p))`, proving `(WOP4)`.

For `(WOP6)`, every element of `F_r` lies in the weighted ring with row
weights `(0,r,0)`. An element of both `F_1` and `F_2` has zero entries
between row `2` and the outer rows: their required degrees are respectively
`1` and `2`, or `-1` and `-2`, and the grading is a direct sum. Its outer
block `C` is scalar, and its middle entry has the form `c_A` in the
level-one core. Prefix refinement identifies that entry at level two with
`A tensor I_2`. The two finite matrix identifications consequently give

```text
diag(C,A) in SL_4(F_p),
diag(C,A tensor I_2) in SL_6(F_p).
```

Their determinant conditions are
`det(C)det(A)=1=det(C)det(A)^2`, so both determinants equal one.
Conversely each such block matrix belongs to both packets. The two block
factors commute and embed injectively, proving the claimed direct-product
intersection. In particular, the mark and its opposite root lie in the
outer `SL_2` factor.

For the finite gluing model, take `N/|F_i|` copies of the regular `F_i`
action. Each restriction to `K` is `N/|K|` copies of the regular `K`
action. A `K`-equivariant bijection identifies the two actions on one
`N`-point set; their permutation matrices agree on all of `K`. The
nonidentity element `w` has no fixed points, giving trace zero and squared
normalized HS distance two. To record the full branching data, for complex
irreducibles `sigma` of `F_i` and `tau` of `K` the multiplicities are

```text
m_i(sigma)=N dim(sigma)/|F_i|,
m_K(tau)=N dim(tau)/|K|,
sum_sigma m_i(sigma)[Res_K(sigma):tau]=m_K(tau).
```

The last identity is the restriction identity for regular representations.
All these multiplicities are integral and realized on the common matrix
space, so this is an exact countermodel to a marked kill conclusion based
only on the finite chart and overlap branching constraints.

Finally `(WOP5)` gives `(WOP7)` in the Leavitt group. To check that this
relation is absent from the amalgam, abbreviate

```text
a=X_0, c=X_1 in F_1,
b=Y_(0j), d=Y_(1j) in F_2.
```

Its amalgam normal form is

```text
a | b | a^(-1) | b^(-1)d | c | d^(-1) | c^(-1).
```

These seven factors alternate between the two finite groups and all lie
outside `K`. In particular,
`b^(-1)d=x_23((s_1-s_0)s_j)` is a nonzero middle-to-outer root, since
left multiplication of its coefficient by `t_1` gives `s_j!=0`.
Every element of `K` has that entry zero. The other six factors are
nonzero native arms and likewise outside `K`. The reduced-word theorem
for amalgams therefore makes `R_j` nonidentity there. This proves the
precise distinction between the overlap constraints and the additional
mixed Leavitt identity without asserting a matrix stability estimate.

For `(WOP8)`, use the rectangular matrices `T_r,S_r` already constructed
for weights `(0,r,0)` and `ell=0`. Their identities `T_r S_r=I_N` and
`S_r T_r=I_3` do not require homogeneous input. Consequently
`Phi_r(X)=T_r X S_r` is an isomorphism `M_3(L) -> M_N(L)` on the entire
matrix rings, with inverse `Y -> S_r Y T_r`.

It also identifies the elementary groups. Each original elementary root
maps to a product of commuting elementary roots: for example,

```text
Phi_r(x_12(a))=product_(|u|=r) x_(1,u)(a s_u),
Phi_r(x_21(a))=product_(|u|=r) x_(u,1)(t_u a).
```

The roots involving rows `2,3` have the same respective formulas with
outer coordinate `3`, and the outer roots `x_13(a),x_31(a)` are unchanged.
This proves inclusion into `EL_N(L)`. Conversely, the elementary roots
between an outer and a middle coordinate have lifts

```text
x_(1,u)(a) <- x_12(a t_u),
x_(u,1)(a) <- x_21(s_u a),
x_(u,3)(a) <- x_23(s_u a),
x_(3,u)(a) <- x_32(a t_u).
```

For distinct middle coordinates `u,v`, the identity
`x_(u,v)(a)=[x_(u,1)(a),x_(1,v)(1)]` supplies a lift too. Together with
the unchanged outer roots these exhaust the elementary generators of
`EL_N(L)`, proving the claimed elementary-group isomorphism.

Split a length-`s` word as `uv`, where `|u|=r` and `|v|=d`. Prefix
cancellation gives

```text
Phi_r(F_r)=SL_N(F_p),
Phi_r(x_12(t_(uv)))=x_(1,u)(t_v),
Phi_r(x_23(s_(uv)))=x_(u,3)(s_v).
```

Thus the two-depth image lies in the elementary group over the coefficient
subring generated by the length-`d` branch pairs. The constant `SL_N`
Weyl words move each of these coefficients to every root position, with
signs corrected by inversion. Root additivity, scalar powers, and
spare-index commutators then generate every elementary root over that
coefficient subring. This proves equality of the elementary groups once
the subring is identified.

Let `q=2^d`. The length-`d` prefix generators satisfy
`t_v s_w=delta_(v,w)` and `sum_(|v|=d) s_v t_v=1`, so they define a
homomorphism from `L_(1,q)(F_p)` into `L`. This homomorphism is injective
without requiring a simplicity theorem. It scales the standard degree by
`d`. On degree zero it embeds every finite prefix matrix ring: multiplication
on the left by `t_u` and on the right by `s_v` extracts each scalar matrix
coefficient, and all degree-zero elements lie in such a finite level.

The kernel is graded because distinct source degrees map to distinct
target degrees. If a nonzero homogeneous kernel element `a` had positive
degree `k`, some `t_w a`, with source prefix length `|w|=k`, would be
nonzero of degree zero: otherwise
`a=sum_(|w|=k) s_w t_w a=0`. This contradicts injectivity on degree zero.
For negative degree `-k`, some `a s_w` of degree zero is similarly nonzero,
using `a=sum_(|w|=k) a s_w t_w`. Thus the kernel is zero.

Its image is exactly `R_d`. One inclusion follows from the degrees of the
generators. Conversely, every homogeneous element of degree divisible by
`d` is a sum of monomials `s_a t_b` with `|a|-|b|` divisible by `d`.
Choose `ell>=0` so that `|a|+ell` and `|b|+ell` are both divisible by `d`.
The common-suffix refinement

```text
s_a t_b=sum_(|c|=ell) s_(ac) t_(bc)
```

expresses the monomial using prefixes of lengths divisible by `d`, hence
using products of length-`d` branch generators. This proves the stated
Veronese identification and completes `(WOP8)`. For `d=1`, it gives all of
`L`. For `d>1`, the unchanged outer root `x_13(s_0)` is outside the image
subgroup because its nonzero coefficient has degree one, proving properness.

For `(WOP9)`, let `q=2^(s-r)` and work first in `B=L_(1,q)(F_p)`.
The construction in `GroupApproximation/Leavitt/AryCorner.lean`
(`CompleteMatrixFamily.cornerBinaryFamily` and
`cornerIdem_ne_zero`) has the following explicit algebraic verification.
Put `p_i=s_i t_i`, `e=sum_(i<q-1) p_i`, and `f=e-p_0`. Orthogonality
makes `e` and `f` idempotent, gives `e+p_(q-1)=1`, and gives

```text
e s_0=s_0,       t_0 e=t_0,
e s_(q-1)=0,     t_(q-1)e=0,
f s_0=0,         t_0 f=0.
```

In particular `t_0 e s_0=1`, so `e!=0`. The four elements displayed in
the claim lie in `eBe`. Direct multiplication gives

```text
T_0 S_0=e,       T_0 S_1=0,
T_1 S_0=0,       T_1 S_1=p_0+f=e,
S_0 T_0+S_1 T_1
 =s_0(e+p_(q-1))t_0+f=e.
```

These are exactly the binary Leavitt relations with corner unit `e`, so
universality gives a unital homomorphism
`rho:L_2(F_p) -> eBe`. The theorem
`BinaryLeavitt.exists_mul_mul_eq_one` in
`GroupApproximation/Leavitt/LeavittSimplicity.lean` states that every
nonzero `x` in the binary algebra admits `a,b` with `a*x*b=1`.
If such an `x` were in the kernel of `rho`, applying `rho` to this
identity would give `e=0`. Thus `rho` is injective.

Apply `rho` entrywise to three-by-three matrices and then set

```text
J(g)=rho_entrywise(g)+(1-e)I_3.
```

The corner entries annihilate `1-e` on both sides, so `J(gh)=J(g)J(h)`
on invertible matrices, `J(I_3)=I_3`, and inverses are preserved.
Entrywise injectivity and subtraction of the fixed complementary matrix
make `J` injective. On elementary generators,

```text
J(x_ij(a))=I_3+rho(a)E_ij=x_ij(rho(a)),
```

so `J` restricts to an embedding `EL_3(L_2(F_p)) -> EL_3(B)`.
Block inclusion `g -> diag(g,I_(N-3))`, followed by the coefficient
identification and inverse prefix expansion in `(WOP8)`, embeds this
group into `H`. The inclusion `H<=G` supplies the other direction.
Hyperlinearity passes to subgroups by restricting finite-set matrix
approximations; applying that fact to the two embeddings proves `(WOP9)`.
This argument uses no elementary-rank comparison theorem beyond the
explicit block inclusion. Its reverse embedding sends `x_13(1)` to
`x_13(e)` in the intermediate `q`-ary matrix group, which explains the
stated limitation concerning marked pairs.
