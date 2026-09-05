# Twisted section parity: finite survival and an inductive-limit candidate

Date: 2026-09-05. **Candidate proof under independent review.**
This file is not a Cairn route and does not change the status of STW LIX.
The proposed finite-stage calculation and its extension are written out
so the exact topological claims can be attacked before any promotion.

## A. The bundle and two sections

Let

    Y = product_(i=1)^l CP^{d_i},   m = sum_i d_i,
    H = direct-sum_i L_i^{direct-sum d_i},
    M = S^5 x Y,
    V = C^3 direct-sum H,
    r = rank(V) = m+3.

Here L_i is the pullback of the tautological line from the i-th factor.
In particular dim_R(M)=2r-1. Put h_i=c_1(L_i), choosing orientations
consistently; signs of the resulting top integer are immaterial below.

There are two unit sections of V:

    e(x,y) = (e_3,0),        s(x,y) = (x,0),

where S^5 is the unit sphere in C^3. Their orthogonal complements are

    e^perp = C^2 direct-sum H,
    s^perp = F direct-sum H,

where F over S^5 has fiber F_x=x^perp in C^3. The rank-two bundle F is
the bundle clutched by a generator u:S^4 -> U(2) of pi_4(U(2))=Z/2.
Indeed U(3)->S^5 is its unit-frame fibration, and the boundary
pi_5(S^5)->pi_4(U(2)) maps a generator onto that generator.

## B. Difference of unit sections and its Euler interpretation

For an oriented real rank-n bundle over an (n-1)-dimensional finite CW
complex, homotopy classes of unit sections, if nonempty, form a torsor
for H^{n-1} of the base with the orientation local system. This follows
directly by obstruction theory: the fiber S^{n-1} is (n-2)-connected,
and the only difference obstruction in this dimension has coefficients
pi_(n-1)(S^{n-1})=Z. Here n=2r and the orientation system is trivial.

Write d(e,s) in H^{2r-1}(M;Z) for that difference. It is equivalently
the relative Euler class of pr_M^*V on M x [0,1], supplied with e
and s on the two boundary components. We normalize the sign once.

The relative Euler number is

    <d(e,s),[M]> = +/- <c_m(H),[Y]> = +/-1.             (A)

A direct zero-count establishes the normalization, without assuming an
unstable Chern formula. On S^5 x [0,1], interpolate the two C^3-valued
sections by (1-t)e_3+t x. It has exactly one zero, at t=1/2 and x=-e_3.
Its derivative is an isomorphism of oriented real six-dimensional
spaces, so its local zero index is +/-1. Add a section of H, multiplied
by a scalar bump supported in the interior in the t-variable. Choose
that section transverse to zero. The zeros of the direct-sum section
are the product of the one interpolation zero with the zeros of this
section of H. Their signed number is the displayed top Chern number.
Since c_m(H)=product_i h_i^{d_i}, that number is +/-1.

## C. Why an isomorphism of complements requires a gauge orbit

If e^perp and s^perp were isomorphic, polar decomposition would give
a unitary bundle isomorphism between them. Extend it by sending e to s.
This gives a unitary automorphism g of V with ge=s. Conversely any
such g restricts to an isomorphism of the complements.

Unitary automorphisms preserve the section difference because they
preserve the orientation on each sphere fiber:

    d(ge,gs)=d(e,s).

In particular the action on the integer torsor is by translations.
It remains to show that all these translations are even. This is the
step that must include every gauge automorphism, not just a convenient
subgroup of them.

## D. Every gauge translation is even

Let g be any unitary automorphism of V. Form its mapping-torus bundle
W_g over S^1 x M with the explicit identification
`(v,1) ~ (g^(-1)v,0)`. Thus a section interpolating from e at t=0
to ge at t=1 descends to W_g. Its top
Chern number equals, up to the fixed sign convention,

    <c_r(W_g),[S^1 x M]> = <d(e,ge),[M]>.              (B)

To see this, use e as the boundary section at one end and its g-image
at the other. A transverse interpolating section descends to W_g,
and the same interior zeros compute both the relative Euler number
and the Euler number of the closed mapping-torus bundle. The top
complex Chern class is the Euler class of the underlying oriented
real bundle.

Write T=S^1 x S^5 and let z be its integral degree-six generator.
Because K^1(Y)=0 and K^0(Y) is free, the kernel of restriction

    K^0(S^1 x M) -> K^0(M)

is canonically K^1(M)=K^1(S^5) tensor K^0(Y). Thus

    [W_g] = [pr_M^* V] + delta,
    ch(delta) = z ch(beta)                           (C)

for some beta in K^0(Y), up to the harmless choice of sign of z.
The odd Bott generator on S^5 has odd Chern character the integral
degree-five generator. This gives the coefficient 1 in (C).

The K-ring of Y is generated additively by line monomials
product_i L_i^{a_i}. Consequently it suffices to calculate on a
monomial, for which

    ch(beta) = exp(sum_i a_i h_i).

Products of positive-degree components of ch(delta) vanish because
z^2=0. The exact Chern-character/Newton identity therefore reads

    c_j(delta) = (-1)^(j-1) (j-1)! ch_j(delta).

All components with j<3 vanish. For a multi-index b with |b|=j-3,
the coefficient of z product_i h_i^{b_i} in c_j(delta) is

    +/- (|b|+2)! product_i a_i^{b_i} / product_i b_i!
     = +/- (|b|+2)(|b|+1)
          multinomial(|b|;b_1,...,b_l) product_i a_i^{b_i}.

This is an even integer. Integer linear combinations of line monomials
have the same property. Thus every positive Chern class of delta is
divisible by two in integral cohomology. There is no torsion in the
cohomology groups concerned, so the rational computation is an integral
divisibility computation.

Finally

    c(W_g)=c(V)c(delta).

The bundle V is pulled back from Y, whose dimension is 2m=2r-6,
so c_r(V)=0. Every term contributing to c_r(W_g) contains a
positive Chern class of delta and is therefore even. Equation (B)
proves that every gauge translation is even.

Combining with (A), no g can carry e to s. Hence

    F direct-sum H is NOT isomorphic to C^2 direct-sum H.  (D)

The proof only needs the even-translation conclusion; it does not
assume that the stable gauge map is onto K^1(M).

## E. Exact value for the CP^2 test

For Y=CP^2, H=L direct-sum L, V=C^3 direct-sum (L direct-sum L), r=5.
Write ch(beta)=a+b h+c h^2. Formula (C) gives

    c_3(delta)=2a z,
    c_4(delta)=-6b zh,
    c_5(delta)=24c zh^2.

Since c(V)=1+2h+h^2,

    c_5(W_g)=(2a-12b+24c) z h^2.                     (E)

For beta=1,L,L^2 the coefficients are respectively 2,2,26.
They generate 2Z. More concretely, a generator S^5->U(3), acting
on C^3 and as the identity on H, realizes a translation of size 2:
its last-column map S^5->S^5 has degree 2 by Bott's computation of
the fibration U(2)->U(3)->S^5, and the zero-count multiplies this
degree by c_2(H)[CP^2]=1.

Thus the gauge translation subgroup is exactly 2Z, and the two
complements in (D) differ by the nonzero class in Z/2.

On X=S^4 x CP^2, the unitary

    v_2=u direct-sum 1_(L direct-sum L)

clutches the bundle F direct-sum (L direct-sum L) over S^5 x CP^2.
A null-homotopy of v_2 would identify that bundle with
C^2 direct-sum (L direct-sum L). Equation
(D) excludes this. Its stable K1 class is nevertheless zero.

This decides the earlier q+D test if all steps A--D withstand review:
the coset is nonzero and has order two. The section-orbit Z/2 calculation
does not, without an additional identification, specify the subgroup D
inside the separate relative gauge presentation Z/24; no such
identification is needed for the null-homotopy decision.

## F. A proposed simple twisted tower preserving the obstruction

Set r_0=2, Y_0=point, X_0=S^4, E_0=C^2. Recursively put

    Y_(i+1)=Y_i x CP^{r_i},
    X_(i+1)=S^4 x Y_(i+1),
    E_(i+1)=pr_i^*E_i direct-sum L_(i+1)^{direct-sum r_i},
    r_(i+1)=2r_i,
    A_i=Gamma(End(E_i)).

Thus E_i=C^2 direct-sum H_i with
H_i=direct-sum_(j=0)^(i-1) L_(j+1)^{direct-sum r_j},
rank H_i=sum_(j<i)r_j=r_i-2, and dim_R X_i=2r_i.

Choose x_i in X_i such that for every fixed k the projections of
the tail x_i, i>=k, into X_k are dense. Such a choice exists: take
a sequence with dense tails in the compact metrizable infinite product
S^4 x product_(j>=0) CP^{r_j}, and project its i-th point to X_i.

After choosing an orthonormal identification E_i(x_i)=C^{r_i}, set

    phi_i(f)(x,z) = f(x) direct-sum (f(x_i) tensor 1_(L_(i+1),z)).

This is a unital injective *-homomorphism A_i->A_(i+1). The first
summand proves injectivity. Put A=lim_i(A_i,phi_i).

### Proposed simplicity proof

For nonzero a in (A_k)_+, choose a nonempty open set O in X_k on
which a is nonzero. Dense tail projections yield i>=k with the
X_k-coordinate of x_i in O. Since every preceding connecting map
retains the coordinate copy, phi_(k,i)(a)(x_i) is nonzero. At the
next stage its point-evaluation summand is a fixed nonzero matrix
tensored with a line bundle. It is therefore nonzero at EVERY fiber
of X_(i+1), hence is full in the homogeneous algebra A_(i+1).
The standard inductive-limit simplicity criterion now gives simplicity
of A. Its hypotheses can also be checked directly by approximating a
nonzero positive element of a putative proper ideal by a positive
stage element and taking a nonzero cutdown.

A is separable, nuclear, unital, and infinite-dimensional. Each X_i
has only even-dimensional cells, so K1(A_i)=0 by Bott periodicity
and the cellular exact sequence; hence K1(A)=0 by continuity.
Compatible tracial states exist by compactness of the inverse system
of the nonempty compact trace spaces of the A_i. The resulting trace
on the simple unital limit is faithful, giving stable finiteness.

### Proposed unitary persistence proof

Let u_0=u on X_0=S^4. The image of u_0 at stage i is homotopic to

    w_i=u direct-sum 1_(H_i).

Inductively the point-evaluation summand of w_i is a constant finite
matrix unitary tensored with L_(i+1); contract the constant matrix
unitary in U(r_i). This leaves w_(i+1), while the coordinate part is
unchanged. Applying Section D to Y_i and H_i proves that every w_i
is non-null-homotopic: otherwise its S^4-clutching over S^5 x Y_i
would give the forbidden isomorphism in (D).

For a unital inductive limit, a null-homotopy of a stage unitary in
the limit is witnessed at a later stage. Explicitly approximate
finitely many sufficiently close vertices of the path by elements
of a common stage, use polar decomposition to obtain unitaries,
and join adjacent unitaries by their logarithms; sufficiently close
endpoints can be joined to the original stage endpoints too.
Thus the limit of u_0 is non-null-homotopic in U(A), while its
K1 class is zero.

If verified, this would refute STW Problem LIX. It is NOT being
promoted here pending independent scrutiny, especially of the
section-difference mapping-torus formula and its full gauge ambiguity.

## Sources and proof boundary

- [Bott, The stable homotopy of the classical groups](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/bott4.pdf),
  p. 315 and the unitary stabilization fibration: pi_4(U(2))=Z/2,
  pi_4(U(3))=0, and degree 2 for U(3)->S^5 on pi_5.
- [James--Thomas, An approach to the enumeration problem for non-stable
  vector bundles](https://doi.org/10.1512/iumj.1965.14.14033), classical
  orbit-enumeration context. No theorem from an inaccessible full text
  is used as a replacement for the explicit arguments above.
- [STW, Nuclear C*-algebras: 99 problems](https://mysite.science.uottawa.ca/atikuisis/STW.pdf),
  Problem LIX, records the general injectivity problem as open.

The new claims in this candidate depend on the written proofs, not on
search snippets or a declaration that Euler nonvanishing detects every
unitary. In particular the entire gauge action, which was missing from
the earlier finite test, is explicitly included in Sections C--D.
