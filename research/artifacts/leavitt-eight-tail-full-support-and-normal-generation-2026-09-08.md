# Every tail survives in a nontrivial image of the eight-word kernel

2026-09-08. Written group identities and the established presentation and
simplicity of Thompson's `V`. No code, enumeration, or approximation is
used. The result concerns the exact eight-word quotient, and does not
prove simplicity or hyperlinearity of its kernel.

## 1. The coordinate presentation works over every group

Use the complete system (3)--(5) in the
[eight-tail normal form](leavitt-eight-tail-wreath-normal-form-2026-09-08.md).
Let `E=F_2^3`,

```text
Q=(C_3*E)/<<T_8>>,       p:Q->E,
N=ker p,                c_x=b_x c b_x^(-1).
```

Setting `c=1` kills the packet and retains the marked `E`, so `p`
has its marked section. Thus `Q=N semidirect E`. Moving the `b_i`
to the right in a word shows that the eight `c_x` generate `N`.
These facts do not require a perfect-kernel theorem.

For every group `G`, there is a bijection

```text
Hom(N,G) <-> {solutions (z_x) of the full coordinate system in G},
psi       |-> (psi(c_x)).                             (1)
```

The system here includes all eight cube equations and all 64 packet
coordinate equations; it does not impose `z_0!=1`.

To prove the forward direction, the cursor rewriting from the normal
form expresses `b_x t b_x^(-1)` in the `c_y` for every packet word `t`.
All those conjugated relations hold in `N`, so their images hold in `G`.

For the converse, given a coordinate solution, form the ordinary group
`G^E semidirect E`, with `(y.f)_x=f_(x+y)`. Assign

```text
c -> ((z_x),0),       b_i -> (1,e_i).                 (2)
```

The explicit coordinate calculations prove that (2) kills every packet
word and defines a homomorphism from `Q`. Its projection to `E` is `p`,
so the image of `N` lies in the base group. Projecting that image onto
coordinate `0` defines `psi:N->G` and sends `c_x` to `z_x`.
Uniqueness follows because the `c_x` generate `N`, proving (1).

In particular the displayed system is a finite presentation of `N`
on eight generators with 72 relators. One can see this directly by
taking `G` to be the group presented by those generators and relators:
the map in (2) supplies the inverse to the evident surjection onto `N`.
No prefix action, finiteness, or approximation property of `G` enters.

## 2. Local vanishing is equivalent to vanishing of the square root

Fix a coordinate `x`, and abbreviate its words by `z,d,a,A,B,D`.
Their definitions and the two anchor relations give

```text
z^3=1,       d^2=1,       A=a z d z^(-1)a^(-1),
A^2=1,      (Az)^2=1,    D=z^(-1)Az,
DA=z.                                                 (3)
```

For the last equality, `(Az)^2=1` gives `AzA=z^(-1)`, so
`DA=z^(-1)AzA=z^(-2)=z`. The omitted overlap relation
`D^(AD)A^(-1)=1` also follows, as in the exact eight-row reduction.
Together with the six retained Thompson relations, these equations
define a homomorphism

```text
phi_x:V->G,       (A_V,B_V,D_V) -> (A_x,B_x,D_x).      (4)
```

Here the source presentation and its named prefix generators are the
ones authenticated in the
[native certificate](leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md).
The word `D_V A_V` is a nonidentity order-three prefix permutation.
Thompson's `V` is simple, so killing that word makes (4) trivial.
Therefore

```text
z_x=1 => A_x=B_x=D_x=1 => d_x=1.                     (5)
```

The last implication uses the conjugacy in (3). Conversely `d_x=1`
gives `A_x=1`, and the square and cube relations force `z_x=1`.
Consequently

```text
z_x=1 <=> d_x=1,        z_x=1 => B_x=1.              (6)
```

Simplicity is used only for the local presentation argument, not as
an assertion about `N`. If `z_x!=1`, the same argument shows that
`phi_x` is injective.

## 3. Vanishing propagates across each four-vertex face

On any face parallel to `e_1,e_2`, write

```text
p=z_(x+e_2) z_(x+e_1+e_2)^(-1),
q=z_(x+e_1) z_x^(-1).
```

The four displayed words for `d` are exactly

```text
d_x                 =p q,
d_(x+e_2)           =q^(-1)p^(-1)=(pq)^(-1),
d_(x+e_1+e_2)       =q p,
d_(x+e_1)           =p^(-1)q^(-1)=(qp)^(-1).         (7)
```

Also `qp=q(pq)q^(-1)`. Thus either all four `d` values are identity
or none is. This calculation holds before any relator is imposed.
By (6), a solution of the full system has either four identity tails
or four nonidentity tails on each face. The only possible numbers of
nonidentity tails at this stage are `0,4,8`.

## 4. An inactive face forces the opposite face to vanish

Suppose a face `F=x+<e_1,e_2>` has `z_y=1` for all `y in F`.
At every `y in F`, the shared-coordinate formulas give

```text
d_y=h_y=a_y=e_y=A_y=D_y=w_y=1,
k_y=m_y=1,       P_(1,y)=[e_y,u_y]=1,
X_(0,y)=1,
Q_(1,y)=z_(y+e_3) z_(y+e_1+e_3)^(-1),
B_y=X_(1,y)=Q_(1,y).                                (8)
```

The possible nontrivial value of `u_y` is harmless because `e_y=1`.
Equation (6) says `B_y=1`, so (8) forces

```text
z_v=z_(v+e_1)       for every v in F+e_3.             (9)
```

Substitution in the four-term formula for `d_v` makes it identity
on that opposite face too. Equation (6) then makes every `z_v`
there identity. Together with Section 3, this proves the exact
dichotomy over every target group:

```text
either all eight z_x are identity,
or all eight z_x are nonidentity.                    (10)
```

This excludes supports of sizes one through seven, including a single
active plane. It supplies no nontrivial solution in `V` with support eight.

## 5. Internal normal generation and preservation of all eight copies

Apply (1) and (10) to a homomorphism `psi:N->G`. If it kills any
one `c_x`, it kills all eight generators and is trivial. Taking
the particular quotient `G=N/<<c_x>>_N` gives

```text
N=<<c_x>>_N       for every x in E.                   (11)
```

This is internal normal generation in `N`, stronger than normal
generation by `c` in the larger split extension `Q`.

The native Leavitt map kills the packet and sends `c` to a nontrivial
coordinate three-cycle; hence every `c_x` is nontrivial in `N`.
For `G=N` and `psi=id`, (4) therefore gives eight embedded indexed
copies `V_x<=N`. For any nontrivial `psi:N->G`, every `psi(c_x)`
survives by (10). Simplicity in (4) then proves

```text
psi|_(V_x) is injective for every x in E.             (12)
```

The same statements apply in particular to the eight-tail realization
problem in `V`. Any nontrivial homomorphism `N->V` automatically
retains every marked tail and every one of the eight local Thompson
copies. Thus the separate requirement that it retain `c` can be
replaced by nontriviality.

## Scope

Neither (11) nor (12) proves that `N` is simple. A proper kernel can
avoid each `V_x` while containing mixed words among the copies.
No equality or pairwise distinctness of the eight indexed subgroups
is asserted. No new embedding of `N` into `V`, positive normalized-HS
gap, or nonhyperlinearity result is obtained.

The result does not rely on a finite common-depth permutation search:
it is an identity-propagation argument for arbitrary exact targets.
