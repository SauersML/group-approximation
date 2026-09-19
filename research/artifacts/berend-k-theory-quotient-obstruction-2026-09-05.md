---
title: Integral K-theory and a finite-orbit lifting obstruction for Eckhardt's Berend groups
date: 2026-09-05
---

This is a direct calculation for the specific cubic family used in
Eckhardt's Theorem 2.4. It proves an obstruction to a proposed class of
return maps from finite-orbit quotients. It does **not** prove infinite
decomposition rank or resolve Eckhardt--Wu Conjecture II / STW LXXXVI.
The calculation is derived here from standard K-theory; no claim that it
is previously unpublished is made.

## Setup and conclusions

Let `a` be a root of `p(t)=t^3+t^2-2t-1`, let `L` be the ring of
integers of `Q(a)`, and choose a unit `b` multiplicatively independent of
`a`. Write `alpha,beta` for the commuting automorphisms of
`D=C*(L)=C(T^3)` induced by multiplication by these units, and put

`B=D ⋊_alpha Z`,  `A=B ⋊_beta Z=C*(L ⋊ <a,b>)`.

Here `beta` on `B` is the extension fixing the implementing unitary
`u_alpha`. Set `epsilon=Norm(b)=det(beta|L)`, which is either `+1` or
`-1`. Eckhardt's construction does not require `epsilon=+1`; this sign
must not be silently discarded.

Let `omega=[z_1][z_2][z_3]` be the top exterior generator of `K_1(D)`,
where `z_i` are the coordinate unitaries, and let `nu` be its image in
`K_1(A)`. Then:

1. For each `i=0,1`, `K_i(A)` is isomorphic to `Z^4` if
   `epsilon=+1`, and to `Z^2 direct_sum Z/2` if `epsilon=-1`.
2. The class `nu` has infinite order in the first case and exact order
   two in the second. In particular it is always nonzero.
3. Every proper quotient map `q:A -> A/I`, with `I!=0`, kills `nu`.
   Thus `nu` lies in the image of `K_1(I) -> K_1(A)` for every nonzero
   ideal `I`.
4. Fix any matrix unitary `v in U_k(D)` representing `omega`. For every
   nonempty finite invariant `F subset T^3`, put
   `Q_F=C(F) ⋊ Z^2` and let `q_F:A -> Q_F` be restriction. Every unital
   homomorphism `theta:Q_F -> A` satisfies

   `||theta^(k)(q_F^(k)(v))-v||=2`.                         `(BK1)`

5. More generally, suppose `sigma:Q_F -> A` is unital completely
   positive and

   `||sigma^(k)(q_F^(k)(v))-v||<1`.                        `(BK2)`

   There is a unitary `w in M_k(C(F)) subset M_k(Q_F)` for which

   `max{||1-sigma^(k)(w)^*sigma^(k)(w)||,
         ||1-sigma^(k)(w)sigma^(k)(w)^*||}=1`.              `(BK3)`

The value in `(BK3)` is the maximal possible defect for a contraction.
It prohibits uniformly multiplicative return maps, even when the
finite-orbit quotients are asymptotically isometric.

## Explicit actions for both norm signs

No search for independent units is needed to instantiate either case.
Take `b_-=a+1` and `b_+=-(a+1)`. Relative to the rational basis
`1,a,a^2` the exact multiplication matrices are

```text
             [ 0  0   1 ]                 [ 1  0  1 ]
M_alpha =    [ 1  0   2 ],     M_beta- =   [ 1  1  2 ],
             [ 0  1  -1 ]                 [ 0  1  0 ]

M_beta+ = -M_beta-.
```

These matrices preserve the lattice `Z[a]`; their characteristic
polynomials and determinants are unchanged when the multiplication
operators are written in any integral basis of the full ring `L`.
They can also be used directly as an explicit action on `Z^3`, since
the argument applies equally to this invariant lattice. This does not
assume without proof that `1,a,a^2` is an integral basis of `L`.

The relations

`a(a^2+a-2)=1`,  `(a+1)(2-a^2)=1`

show that the matrices are integral automorphisms. They commute since
`M_beta-=1+M_alpha`. Their determinants are respectively `1,-1,+1`.

For completeness, the polynomial has one real root `r` in `(1,2)`,
one `s` in `(-1/2,0)`, and one in `(-2,-1)`, as is seen by its signs
at the interval endpoints; it is irreducible by the rational-root
test. If `a^n=(plus_or_minus(a+1))^m`, logarithms of the absolute values
at the first two embeddings give, when `m!=0`,

`n/m=log(r+1)/log(r)>1`,

`n/m=log(s+1)/log(abs(s))<1`.

The second inequality uses `0<abs(s)<s+1<1`. These are incompatible.
If `m=0`, the first embedding forces `n=0`. Thus either choice gives
two independent units.

The roots' absolute values are distinct: the positive root is below
`3/2`, the root below `-1` is below `-3/2`, and `abs(s)<1/2`, again by
evaluating `p` at `3/2` and `-3/2`. Every positive power of `a` therefore
has three distinct conjugates. Since the field has prime degree three,
each such power has degree three, verifying the irreducibility-of-powers
condition in Berend's criterion. Every common eigenvector is an
eigenvector of `M_alpha`, and one of `M_alpha` and its inverse expands
it. Together with independence, this verifies the three Berend
conditions for both explicit matrix actions.

## The first Pimsner--Voiculescu sequence

The Kunneth formula for the three circles identifies the integral graded
ring `K_*(D)` with the exterior algebra on `L` in degree one:

`K_0(D)=Lambda^0 L direct_sum Lambda^2 L`,

`K_1(D)=Lambda^1 L direct_sum Lambda^3 L`.

This identification is natural for lattice automorphisms: their action
on `K_1` sends each coordinate-unitary class to the corresponding integer
linear combination, and the action on products is its exterior power.

The characteristic polynomial of multiplication by `a` is `p`. Hence

`det(alpha|L)=1`,  `det(1-alpha|L)=p(1)=-1`.

Because `Lambda^2 alpha` is integrally conjugate to `alpha^(-T)` in
dimension three with determinant one,

`det(1-Lambda^2 alpha)=det(1-alpha^(-1))=1`.

Consequently `1-alpha_*` is an isomorphism on both `Lambda^1 L` and
`Lambda^2 L`; on `Lambda^0 L` and `Lambda^3 L` it is zero. No
rationalization, rank-only argument, or unexamined torsion is used.

The Pimsner--Voiculescu exact sequence therefore gives

`0 -> Z omega_B -> K_1(B) --boundary--> Z[1_D] -> 0`,        `(BK4)`

`0 -> Z[1_B] -> K_0(B) --boundary--> Z omega -> 0`.          `(BK5)`

The class of `u_alpha` maps to a generator of `Z[1_D]`, up to the
irrelevant choice of boundary sign. Thus

`K_1(B)=Z omega_B direct_sum Z[u_alpha]`.

Naturality gives

`beta_*(omega_B)=epsilon omega_B`,
`beta_*([u_alpha])=[u_alpha]`.                              `(BK6)`

This also explicitly rules out an extension shear on `K_1(B)`.

For `K_0(B)`, evaluation at the fixed point `0 in T^3` gives a
homomorphism `r:B -> C*(Z)=C(T)` which maps `u_alpha` to the coordinate
unitary. Since `r_*([1_B])=1`, choose a lift `eta` of `omega` in `(BK5)`
and subtract `r_*(eta)[1_B]` so that `r_*(eta)=0`. The boundary map
identifies `ker r_*` with `Z omega`, hence

`K_0(B)=Z[1_B] direct_sum Z eta`.

The map `r` is beta-invariant. Naturality of the boundary yields
`boundary(beta_*(eta))=epsilon omega`. The difference
`beta_*(eta)-epsilon eta` lies in `Z[1_B]` and is killed by `r_*`, so it
is zero. Therefore

`beta_*|K_0(B)=diag(1,epsilon)`,
`beta_*|K_1(B)=diag(epsilon,1)`.                            `(BK7)`

## The second sequence and the surviving class

Apply Pimsner--Voiculescu to `A=B ⋊_beta Z`. For either parity it gives
an exact sequence with left term `coker(1-beta_*|K_i(B))` and right term
`ker(1-beta_*|K_(1-i)(B))`. The kernel groups are free, so the sequences
split as sequences of abelian groups. Equation `(BK7)` proves the two
K-group formulas above.

More precisely, exactness gives an injection

`coker(1-beta_*|K_1(B)) -> K_1(A)`.

The coordinate of this cokernel generated by `omega_B` is
`Z/(1-epsilon)Z`. Its generator maps to `nu`. This proves the exact
order assertion, including the orientation-reversing case.

## Every proper quotient loses the class

For a finite invariant `F`, the restriction of `q_F` to `D` factors as

`C(T^3) -> C(F) -> Q_F`.

Since `K_1(C(F))=0`, it follows immediately that `(q_F)_*(nu)=0`.
The established finite-orbit reduction for this Berend action says that
every proper quotient of `A` factors through some such `Q_F`. Therefore
every proper quotient kills `nu`. Exactness of the K-theory sequence for
`0 -> I -> A -> A/I -> 0` proves that `nu` is in the image of `K_1(I)`
for each nonzero `I`.

There is a stronger statement about the norming product model. For any
sequence `F_n`, the diagonal homomorphism

`A -> product_n Q_(F_n)`

kills `nu` on `K_1`, and so does its composition with the quotient by
`direct_sum_n Q_(F_n)`. Indeed choose, independently at each point of
each finite `F_n`, a selfadjoint logarithm `h_n` of `q_(F_n)^(k)(v)`
with `||h_n||<=pi`. The bounded sequence `(h_n)` belongs to the matrix
algebra over the product, and
`t -> (exp(i t h_n))_n` is a norm-continuous unitary path from `1` to
the image of `v`. This argument avoids the invalid general inference
that coordinatewise vanishing in K-theory implies product vanishing.

## Return maps: exact and quantitative obstructions

If `theta` is a unital homomorphism as in `(BK1)`, then
`theta^(k)(q_F^(k)(v))` is a unitary of trivial K-class, whereas `v` has
class `nu!=0`. Unitaries at distance strictly less than two have the
same K-class. Their distance is at most two, proving equality in `(BK1)`.

For the completely positive assertion choose
`h_F=h_F^* in M_k(C(F))` with `||h_F||<=pi` and
`exp(i h_F)=q_F^(k)(v)`. Put

`x(t)=sigma^(k)(exp(i t h_F))`,  `0<=t<=1`.

This is a norm-continuous path of contractions beginning at `1`. By
`(BK2)`, its endpoint is invertible and is connected to `v` through
invertibles: the straight segment stays within distance less than one
of `v`. Its endpoint therefore has K-class `nu!=0`. The path `x(t)`
cannot consist entirely of invertibles, because that would join this
class to `1`. Choose `t_0` where `x(t_0)` is noninvertible.

For a contraction `x`, if both `||1-x^*x||<1` and `||1-xx^*||<1`,
then `x` has both a left and a right inverse and is invertible. Hence at
`t_0` one of these norms is at least one, and contractivity makes both
at most one. Taking `w=exp(i t_0 h_F)` proves `(BK3)`.

In particular there cannot be return maps satisfying `(BK2)` eventually
whose multiplicativity defects tend uniformly to zero on the unit ball
of `M_k(Q_F)`. Defects only on images of fixed elements of `A` are a
different condition: the witnesses `h_F` and `w` depend on `F`.

## Consequence for the open problem and its limitation

This proves that norm separation by the rank-two finite-orbit quotients
misses a nonzero integral K-class that is present in every nonzero ideal.
The obstruction persists for their faithful product-modulo-sum model.
It identifies a necessary failure of multiplicativity for any completely
positive attempt to return those quotient models to `A`.

It does not rule out the return maps permitted by decomposition rank.
That definition requires a contractive sum of finitely many order-zero
maps; the total map need not be multiplicative on all quotient inputs.
The basic analogy already occurs for `C(T^3)`: evaluation on dense finite
sets loses its top K-class, yet partitions of unity give decomposition
rank three. No implication from `(BK3)` to infinite decomposition rank
is asserted. An additional result tying this unavoidable defect to an
unbounded number of colours is still missing.

## Sources and audit boundary

* C. Eckhardt, [A note on strongly quasidiagonal groups](https://arxiv.org/html/1309.2205),
  Theorem 2.4: the exact cubic, independence of the second unit, and the
  group family. The second unit's norm is not specified there.
* M. Pimsner and D. Voiculescu,
  [Exact sequences for K-groups and Ext-groups of certain cross-product C*-algebras](https://jot.theta.ro/jot/archive/1980-004-001/1980-004-001-005.html),
  J. Operator Theory 4 (1980), 93--118: the crossed-product exact sequence.
* B. Blackadar,
  [K-Theory for Operator Algebras, Chapter V](https://www.cambridge.org/core/books/abs/ktheory-for-operator-algebras/ktheory-of-crossed-products/FD70C8C693B58D29A95B79C0ED628FB3),
  for the standard crossed-product K-theory framework.
* The current named-problem source is Schafhauser--Tikuisis--White,
  [Nuclear C*-algebras: 99 problems](https://arxiv.org/abs/2506.10902),
  Problem LXXXVI; see also Eckhardt--Wu,
  [Nuclear dimension and virtually polycyclic groups](https://arxiv.org/abs/2408.07223),
  Conjecture II.

Primary literature and repository searches were made on 2026-09-04/05.
No later resolution or existing statement of this exact quotient-lifting
calculation was located. That search is not proof of novelty. All new
assertions here are established by the displayed integral calculation
and elementary norm arguments, not by a numerical experiment or a
claim of having resolved the named problem.
