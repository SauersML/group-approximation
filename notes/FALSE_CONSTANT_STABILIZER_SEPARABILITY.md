# The constant Kazhdan stabilizer is separable in the Laurent quotient

Date: 2026-08-11

## 1. Outcome

For the stable Laurent double, the small constant stabilizer

`J=SL_3(Z)`                                             `(CSS1)`

embedded on matrix coordinates `3,4,5` is a separable subgroup of

`F=G *_E G ~= E semidirect_(varphi) (Q*Q)`,            `(CSS2)`

where

`E=EL_r(Z[x_1^(+-1),...,x_d^(+-1)])`,
`Q=SL_d(Z)`,                                           `(CSS3)`

and `varphi:Q*Q->Q` is the fold map governing the action on Laurent
exponents.

The proof uses explicit finite `Q`-stable ring quotients

`A_(p,M)=F_p[(Z/MZ)^d]`.                               `(CSS4)`

They retain any prescribed nonconstant Laurent-matrix entry while the
constant subgroup `(CSS1)` remains a constant `3 x 3` block.  Elements
with nontrivial `Q*Q` component are separated by finite quotients of the
free product.

Consequently there is a nested normal residual chain `L_n normal F` with

`intersection_n L_n=1`,
`intersection_n J L_n=J`.                              `(CSS5)`

This proves the relative-separability hypothesis left open in
`FALSE_INTERMEDIATE_SPLIT_HOMOLOGY.md`.  The associated intermediate
finite-index subgroups converge exactly to `R_0 semidirect J`, where the
radical word has infinite-order homology.  Hence their integral filling
norms diverge.

This still does not prove FALSE: the remaining quantitative problem is to
turn that divergence into an unbounded marked paired-discriminant ratio.
The important gain is that the transfer degree is the size of the image of
one fixed `SL_3(Z)`, rather than the image of a polynomial elementary
group of growing ring complexity.

## 2. Finite equivariant Laurent quotients

Put

`R=Z[x_1^(+-1),...,x_d^(+-1)]`.                       `(CSS6)`

For a prime `p` and an integer `M>=2`, let

`A_(p,M)=F_p[U_M]`, `U_M=(Z/MZ)^d`.                   `(CSS7)`

Write `u_1,...,u_d` for the standard generators of `U_M`.  There is a
surjective ring homomorphism

`ev_(p,M):R->A_(p,M)`, `x_i |-> u_i`.                 `(CSS8)`

The action of `Q=SL_d(Z)` on Laurent exponents descends modulo `M` to an
action on `U_M`, hence to ring automorphisms of `A_(p,M)`.  Formula
`(CSS8)` is `Q`-equivariant.  Thus it induces finite homomorphisms

`E->EL_r(A_(p,M))`,                                   `(CSS9)`

and

`F->EL_r(A_(p,M)) semidirect Aut(A_(p,M))`,           `(CSS10)`

where the `Q*Q` action in `(CSS10)` is obtained by composing the fold map
with the finite action on `A_(p,M)`.  Only the finite image of the displayed
semidirect product is used.

**Lemma 1 (finite Laurent detection).**  If `0!=f in R`, then there are
`p,M` for which `ev_(p,M)(f)!=0`.  If `f` is not an integer constant, they
may be chosen so that `ev_(p,M)(f)` is not in the constant subring `F_p`.

**Proof.**  Write

`f=sum_(alpha in S)c_alpha x^alpha`                   `(CSS11)`

with finite exponent set `S subset Z^d`.  Choose `M` so large that the
images modulo `M` of the elements of `S` are distinct.  Then the group
elements `u^alpha` occurring in `(CSS11)` are distinct basis vectors of
the `F_p`-vector space `F_p[U_M]`.  Choose `p` not dividing at least one
nonzero coefficient.  This proves nonvanishing.

If `f` is nonconstant, first subtract its constant coefficient.  Choose
`M` large enough that every nonzero exponent in its support remains
nonzero modulo `M`, and then choose `p` retaining a nonconstant
coefficient.  Its image has a nonzero component on a nonidentity basis
element of `U_M`, so it is not constant.  End proof.

The use of the group algebra rather than evaluation at one point is
load-bearing: `(CSS8)` remains equivariant under the whole arithmetic
action `Q`, so it defines a quotient of the semidirect product, not merely
of `E`.

## 3. Separating the constant block

Embed `J=SL_3(Z)=EL_3(Z)` in `E` as

`diag(I_2,J,I_(r-5))`.                                `(CSS12)`

The stable range `r>=d+4>=7` makes this block available, and it commutes
with `h=e_12(x_1^(-1))`.

**Lemma 2 (matrix separation inside `E`).**  For every `e in E minus J`
there are `p,M` such that the image of `e` under `(CSS9)` does not belong
to the image of `J`.

**Proof.**  Regard `e` as its matrix in `SL_r(R)`.  Membership in `J` is
equivalent to the following finite list of entry conditions:

1. every entry outside the `3 x 3` block on coordinates `3,4,5` equals the
   corresponding entry of the identity;
2. every entry inside that block is an integer constant.

If all these conditions hold, the `3 x 3` block has determinant one because
the full matrix does, so it lies in `SL_3(Z)=J`.

Since `e notin J`, at least one condition fails.  If an outside-block entry
differs from the required Kronecker delta, apply the nonvanishing part of
Lemma 1 to that difference.  If an inside-block entry is nonconstant, apply
the second part.  In the resulting finite ring quotient, the matrix of `e`
still violates the defining entry conditions of the constant block
`J`.  Hence its image is not in the image of `J`.  End proof.

## 4. Subgroup separability

Every element of `(CSS2)` has a unique form

`f=e ell`, `e in E`, `ell in Q*Q`.                     `(CSS13)`

**Theorem 3 (constant-stabilizer separability).**  For every `f in F-J`
there is a finite quotient `theta:F->K` such that

`theta(f) notin theta(J)`.                            `(CSS14)`

**Proof.**  If the `Q*Q` component `ell` in `(CSS13)` is nontrivial, use
residual finiteness of `Q*Q` to find a finite quotient retaining `ell`, and
compose with the projection `F->Q*Q`.  The subgroup `J<=E` maps to the
identity while `f` does not.

If `ell=1`, then `f=e in E-J`.  Apply Lemma 2 and use the finite
semidirect-product quotient `(CSS10)`.  Its restriction to `E` is the
matrix quotient `(CSS9)`, so `(CSS14)` holds.  End proof.

Thus `J` is closed in the profinite topology of `F`.  Notice that this is
stronger than merely separating each nonidentity element of `J`; it
separates every outside coset from the entire subgroup.

## 5. A simultaneous residual and relative chain

The group `F` is finitely generated and residually finite.  Enumerate

`F-J={a_1,a_2,...}`, `F-{1}={b_1,b_2,...}`.           `(CSS15)`

For each `a_i`, choose a finite quotient as in Theorem 3 and let `N_i` be
its normal kernel.  Thus

`a_i notin J N_i`.                                    `(CSS16)`

For each `b_i`, choose a finite quotient retaining it and let `M_i` be its
normal kernel.  Define

`L_n=intersection_(i<=n)(N_i intersect M_i)`.          `(CSS17)`

**Corollary 4 (relative residual chain).**  The `L_n` are nested normal
finite-index subgroups of `F` and satisfy `(CSS5)`.

**Proof.**  If `1!=b_i`, then `b_i notin M_i`, so `(CSS17)` gives
`intersection_nL_n=1`.  Clearly `J subset intersection_n J L_n`.  If
`a_i notin J`, then `L_n<=N_i` for every `n>=i`; equation `(CSS16)` gives
`a_i notin J L_n`.  Hence no element outside `J` belongs to
`intersection_n J L_n`, proving equality.  End proof.

## 6. Consequence for the explicit radical word

Let

`pi:D=G *_Gamma G->F=G *_E G`,
`R_0=ker(pi)`,                                         `(CSS18)`

and pull `(CSS17)` back:

`K_n=pi^(-1)(L_n)`, `H_n=pi^(-1)(J L_n)`.             `(CSS19)`

Then

`intersection_nK_n=R_0`,
`intersection_nH_n=pi^(-1)(J)=R_0 semidirect J`.      `(CSS20)`

The marked radical word `w=i_2(h)i_1(h)^(-1)` is an integral boundary in
every finite-index cover `Y_(H_n)`, but
`FALSE_INTERMEDIATE_SPLIT_HOMOLOGY.md` proves that it has infinite order in
the abelianization of the limiting subgroup in `(CSS20)`.  Therefore

`Fill_Z,2(w;H_n)->infinity`.                           `(CSS21)`

Moreover `Y_(K_n)->Y_(H_n)` is regular of degree

`m_n=|J/(J intersect L_n)|`,                          `(CSS22)`

and the exact orthogonal transfer formulas give

`Fill_R(w;K_n)^2`
` =m_n^(-1)Fill_R(w;H_n)^2+epsilon_n^2`,
`epsilon_n<=C`,                                       `(CSS23)`

`rho_(K_n)(c_(K_n))^2`
` >=m_n^(-1)rho_(H_n)(c_(H_n))^2-C^2`.               `(CSS24)`

Because `J` is now the constant `SL_3(Z)`, the degree `(CSS22)` measures
only the finite image of a fixed arithmetic group.  Ring quotients may
grow in directions invisible to that constant block.  This removes the
previous artificial use of the much larger polynomial stabilizer.

## 7. Remaining quantitative gate

The construction proves existence of the exact relatively separating
mixed tower and forces integral escape in its intermediate covers.  It
does not yet prove either

`Fill_R(w;H_n)/sqrt(m_n)->infinity`                   `(CSS25)`

or a marked paired-discriminant divergence in the complementary case.

The next useful refinement is **relative residual growth with controlled
constant-block image**: choose the separating quotients in Theorem 3 so
that the Laurent-matrix complexity grows much faster than
`|theta_n(J)|`.  The explicit quotients `(CSS4)` make this plausible, but
integral filling growth must be quantitatively related to their exponent
or injectivity radius before `(CSS25)` can be claimed.

The unconditional conclusion is already structural: the last invariant
mode has an explicit, relatively separating finite tower, and its Kazhdan
averaging cost depends only on a constant `SL_3(Z)` block.
