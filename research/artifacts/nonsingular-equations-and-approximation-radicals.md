# Nonsingular equations, coefficient certificates, and approximation radicals

## Status

The Kervaire--Laudenbach conjecture is not resolved here. This artifact
proves three precise results: nonsingular one-variable equations preserve
every matrix certificate about the old coefficients; their relative
presentations preserve the pullbacks of both approximation radicals; and
they have solutions in MF overgroups when the coefficient group is MF.

The finite-dimensional root theorem is classical
Gerstenhaber--Rothaus. Section 1 supplies its one-variable proof, including
the degree calculation, rather than asserting a new discovery. The radical
and certificate statements are consequences developed for this repository.
No literature priority or Lean verification is asserted.

Primary references checked for this attempt:

- [Thom, *Convergent sequences in discrete groups*, Remark 3.5](https://arxiv.org/html/1003.4093v3):
  the unitary word map with coefficients is onto when its exponent sum is
  nonzero, attributed there to Gerstenhaber--Rothaus.
- [Nitsche--Thom, *Universal solvability of group equations*, Lemma 2.1](https://arxiv.org/pdf/1811.07737):
  coordinatewise roots and quotient passage give the hyperlinear result.
  Their more general covering construction is different: Remark 2.5 does
  not assert that its solution overgroup is hyperlinear.
- [Marimon--Pinsker, *All mixed identities are singular in groups with no algebraicity*, v2](https://arxiv.org/html/2606.24741v2):
  the introduction still identifies the universal equation problem as open.

## 1. The complete one-variable matrix argument

Let `d>=1`, fix unitary coefficients `A_0,...,A_l in U(d)`, and let
`e_1,...,e_l` be integers with `m=sum_j e_j !=0`. The smooth map

\[
 F(T)=A_0T^{e_1}A_1\cdots T^{e_l}A_l:U(d)\longrightarrow U(d)
                                                               \tag{1}
\]

is surjective and has degree `m^d`.

We use the ordinary degree of a map between compact connected oriented
manifolds of equal dimension. In particular, degree is invariant under
homotopy and is the sum of the signs of the derivatives over a regular
value. A map of nonzero degree is surjective: an omitted point is a regular
value with empty inverse image and hence would give degree zero.

### Reduction to the power map

The compact Lie group `U(d)` is connected, orientable, and has real
dimension `d^2`. Choose a path from each coefficient `A_j` to the identity.
Using those paths in (1) gives a homotopy to `P_m(T)=T^m`. This homotopy
does not need to preserve relations between the coefficient matrices: it
is a homotopy of maps on `U(d)`, not a deformation of a group embedding.

### Degree of `P_m` for positive `m`

Choose a diagonal unitary `V=diag(lambda_1,...,lambda_d)` with distinct
eigenvalues. If `X^m=V`, then `X` commutes with `V`, so `X` is diagonal in
this fixed basis. There are exactly `m^d` inverse images, obtained by
choosing one of the `m` roots of each `lambda_i` independently.

It remains to check regularity and orientation at every inverse image;
counting roots alone is insufficient. Write `X=diag(z_1,...,z_d)` and
parametrize a tangent vector by `X exp(tK)`, with `K^*=-K`. Left-translating
the output tangent vector by `X^(-m)`, differentiation gives

\[
 L_X(K)=\sum_{j=0}^{m-1}X^{-j}KX^j.                    \tag{2}
\]

On the `d` real diagonal directions, this is multiplication by `m`.
For each `i<j`, the off-diagonal entries `K_ij` and `K_ji=-conj(K_ij)`
form a real two-plane, identified with the complex coordinate `K_ij`.
On it, (2) is multiplication by the complex number

\[
 c_{ij}=\sum_{h=0}^{m-1}(z_j/z_i)^h.
\]

This number is nonzero. Indeed, `z_j^m/z_i^m=lambda_j/lambda_i !=1`,
so the geometric sum cannot vanish. Complex multiplication by `c_ij`
has real determinant `|c_ij|^2>0`. The total derivative determinant is
therefore positive and nonzero. Left translations preserve orientation,
so all `m^d` inverse images contribute `+1`. Thus `deg(P_m)=m^d`.

### Negative `m`

Inversion `J(T)=T^(-1)` is a diffeomorphism. At the identity its real
derivative on the `d^2`-dimensional Lie algebra is `-I`. Its orientation
sign is consequently `(-1)^(d^2)=(-1)^d`. For `m<0`, write
`P_m=P_|m| o J`. Multiplicativity of degree gives

\[
 \deg(P_m)=|m|^d(-1)^d=m^d.                            \tag{3}
\]

Equations (1)--(3) prove surjectivity in every positive dimension. In
particular, `F(T)=I_d` has an exact solution without changing any
coefficient or enlarging the matrix size. The assertion makes no claim
that a root can be chosen continuously in the coefficients.

## 2. Exact conservation of coefficient certificates

Fix a finite alphabet `S`, a finite relator list `R` in the free group
`F(S)`, an old word `a in F(S)`, and a new word
`w in F(S union {t})` whose exponent sum in `t` is nonzero. For an arbitrary
unitary tuple `U in U(d)^S`, the coefficients in `w` evaluate to unitaries,
whether or not `U` satisfies `R`. Section 1 therefore proves that the
projection

\[
 \{(U,T):w(U,T)=I_d\}\longrightarrow U(d)^S            \tag{4}
\]

is onto for each fixed `d`.

Write, in operator norm,

\[
 a_{\rm op}(U)=\|a(U)-I\|,\qquad
 \delta_R(U)=\max_{r\in R}\|r(U)-I\|,
\]

with the empty maximum equal to zero. For every fixed `C>=0`, the two
statements

\[
 \forall U:\quad a_{\rm op}(U)\le C\delta_R(U),        \tag{5}
\]

\[
 \forall U,T:\quad a_{\rm op}(U)
 \le C\max\bigl(\delta_R(U),\|w(U,T)-I\|\bigr)        \tag{6}
\]

are equivalent. Here the quantifiers can refer either to one fixed
dimension or to all positive dimensions. Statement (5) implies (6) by
nonnegativity; for the converse choose an exact root in (4) for each `U`.

The same argument applies to normalized Hilbert--Schmidt energies
`e_v(U)=||v(U)-I||_(2,d)^2`. It gives the exact equivalence

\[
 \forall U:\quad e_a(U)\le C\sum_{r\in R}e_r(U)
 \quad\Longleftrightarrow\quad
 \forall U,T:\quad e_a(U)\le C\left(\sum_{r\in R}e_r(U)+e_w(U,T)\right).
                                                               \tag{7}
\]

Thus the sets of admissible constants, and hence their infima in
`[0,infinity]`, are identical. An empty admissible set has infimum infinity.
This is stronger than preservation of the existence of some certificate:
there is no gain in its optimal constant, even in one matrix size.

More generally, if `B(U)>=0`, `E(U,T)>=B(U)`, and
`E(U,T)=B(U)` at every exact root, then a coefficient-only inequality
`A(U)<=C B(U)` is equivalent to `A(U)<=C E(U,T)`. No tracial or
operator-order positivity certificate is being silently substituted for
the specified matrix norm inequality.

## 3. Extension into any algebraic quotient of a unitary product

Let

\[
 P=\prod_n U(d_n),\qquad Q=P/N,
\]

where `N` is any normal subgroup. Every nonsingular one-variable equation
with coefficients in `Q` has a solution in `Q` itself. To prove this,
choose unitary sequence lifts of its finitely many coefficients. In
coordinate `n`, solve the lifted equation exactly in `U(d_n)` by Section 1.
The sequence of roots belongs to `P`, and its image solves the equation in
`Q`. Multiplicative relations between coefficient lifts need only hold in
the quotient; exact coordinate representations of their coefficient group
are not assumed.

Consequently, if

\[
 H=(G*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle,
 \qquad q:G\longrightarrow H,                        \tag{8}
\]

with `deg_t(w)!=0`, **every** homomorphism `phi:G->Q` extends to a
homomorphism `psi:H->Q` satisfying `psi o q=phi`. Choose a root for the
equation after applying `phi` to its coefficients, and use the universal
property of the free product and then of the quotient (8).

Two important instances are:

1. `N_op={ (U_n): ||U_n-I||_op ->0 }`;
2. `N_(2,omega)={ (U_n): lim_omega ||U_n-I||_(2,d_n)=0 }`, for a
   nonprincipal ultrafilter `omega`.

They are normal subgroups by the triangle inequality and unitary invariance
of their respective metrics. The second quotient is the standard metric
ultraproduct used for hyperlinearity.

The first is precisely the unitary group of the norm matrix corona

\[
 \mathcal Q=\prod_n M_{d_n}(\mathbb C)/\bigoplus_n M_{d_n}(\mathbb C).
\]

For completeness, every corona unitary has a unitary sequence lift: choose
a bounded lift `a_n`; unitarity gives `a_n^*a_n-I ->0` and
`a_na_n^*-I ->0` in norm. The matrices are invertible eventually and their
polar unitaries differ from them by a norm-null sequence. Replace the
finitely many exceptional coordinates by arbitrary unitaries. The kernel
of the resulting map from `P` is exactly `N_op`.

There is no passage here from an operator-norm approximation to a
normalized-HS approximation. Both quotients are treated separately by the
same algebraic argument.

## 4. Both approximation radicals are conserved on the coefficients

For a class `C` of target groups, set

\[
 \operatorname{Rad}_{C}(G)=\bigcap_{\phi:G\to Q,\ Q\in C}\ker\phi.
\]

Let `C_op` be all norm matrix-corona unitary groups, and `C_hyp` all
tracial metric ultraproducts above. They define `Rad_MF` and `Rad_hyp`
in the repository's conventions. For (8), Section 3 proves

\[
 q^{-1}(\operatorname{Rad}_{\rm MF}(H))=\operatorname{Rad}_{\rm MF}(G),
 \qquad
 q^{-1}(\operatorname{Rad}_{\rm hyp}(H))=\operatorname{Rad}_{\rm hyp}(G).
                                                               \tag{9}
\]

Here is the full kernel argument, without assuming `q` injective. If
`a in Rad_C(G)`, every map `psi:H->Q` kills `q(a)`, since its restriction
`psi o q` is a map from `G`. Conversely, if `a notin Rad_C(G)`, choose
`phi:G->Q` with `phi(a)!=1`. Section 3 extends it to `psi:H->Q`, which
detects `q(a)`. This proves both equalities in (9).

In particular,

\[
 \ker q\subseteq\operatorname{Rad}_{\rm MF}(G)
                  \cap\operatorname{Rad}_{\rm hyp}(G),           \tag{10}
\]

and `q` induces injective maps between the corresponding radical
quotients. Formula (9) does **not** assert that either radical of `H` is
generated by the image of the radical of `G`; new-variable words have not
been classified.

The result also holds for a countable triangular sequence of adjunctions:
at stage `j`, add `t_j` with an equation nonsingular in `t_j` and
coefficients in the previous group. Extend each homomorphism successively
into the same target `Q`, and pass to the direct limit by its universal
property. This works even if intermediate coefficient maps are not known
to be injective. The reverse inclusion of radicals still follows by
restriction, as above.

## 5. The positive MF case, including the solution overgroup

Let `G` be countable and MF in the norm-corona sense, and choose a faithful
map \(\phi:G\to U(\mathcal Q)\). Section 3 supplies an extension
\(\psi:H\to U(\mathcal Q)\). Since `psi o q=phi`, the coefficient map `q`
is injective.

Moreover `K=psi(H)` is a countable subgroup of the same norm-corona unitary
group, hence is MF by that definition, and `phi(G)<=K`. Thus the equation
has a solution in an MF group containing the original coefficient group.
This proves the one-variable Kervaire--Laudenbach assertion for MF groups
directly; it does not assume that MF implies hyperlinear.

It is the image `K`, not necessarily the universal relative group `H`,
which is proved MF. Choosing a root need not make `psi` faithful on the
new variable. Already with `G=1` and `w=t^2`, the valid root `T=I` kills
the nontrivial generator of `H=C_2`. This example is a limitation of a
chosen solution map, not a claim that `C_2` is non-MF.

One can also place `G` in a countable MF group that solves every nonsingular
one-variable equation over itself. Inside the same corona, start with
`K_0=phi(G)`. Having constructed countable `K_j`, choose roots for all such
equations with coefficients in `K_j`, and let `K_(j+1)` be generated by
`K_j` and those countably many roots. The union `K_infinity` is countable
and remains a subgroup of the corona. Any finite list of coefficients in
the union lies in some `K_j`, so its equation has a root in `K_(j+1)`.

## 6. A quantitative restriction on an algebraic counterexample certificate

Suppose `G=<S|R>` and an old word `a` dies in (8). Then in `F(S union {t})`
there is a finite normal-closure identity

\[
 a=\prod_{j=1}^{A+B}v_j f_j^{\epsilon_j}v_j^{-1},
 \quad \epsilon_j\in\{1,-1\},\quad f_j\in R\cup\{w\},             \tag{11}
\]

where `A` factors use old relators and `B` use the added equation. Only
finitely many relators from `R` occur, even if the presentation is infinite.
For an arbitrary coefficient tuple `U`, select `T` with `w(U,T)=I`.
The `B` new-equation factors become identities. Telescoping the remaining
unitary factors gives, in operator norm or normalized HS norm,

\[
 \|a(U)-I\|\le\sum_{r\in R} n_r\|r(U)-I\|
                  \le A\max_{r:n_r>0}\|r(U)-I\|,                \tag{12}
\]

where `n_r` counts old-relator occurrences and `sum_r n_r=A`. If `A=0`,
the first sum is zero. In normalized HS energy, Cauchy--Schwarz further
gives for `A>0`

\[
 e_a(U)\le A\sum_r n_r e_r(U).                          \tag{13}
\]

Thus arbitrarily many uses of the added nonsingular equation cannot
reduce the required old-relator matrix-certificate cost. Every proposed
identity (11) must meet (12)--(13) in all dimensions. This is a necessary
condition on an algebraic counterexample, not a method producing (11).

The nonsingularity hypothesis is essential. Take `G=C_2=<a|a^2=1>` and
the singular equation `w=t a t^(-1)`. Then
`a=t^(-1) w t` has `A=0`, and the coefficient group collapses in the
relative presentation. With `a=-I`, the equation has no unitary solution;
Section 1 does not apply because `deg_t(w)=0`.

## 7. The attempted global step and why it is still missing

The intended proof of the universal conjecture was: extend all matrix
representations across the equation, then separate every nontrivial old
coefficient. The extension step is proved above, with the same matrix
dimension and exact roots. The separation step is not available for an
arbitrary coefficient group. Formula (10) puts a possible kernel inside
the common approximation radical; it does not show that kernel is zero.

For a nontrivial element already in both radicals, every such matrix
representation kills it before the equation is adjoined. Neither the degree
calculation, the conserved certificate constant, nor a finite matrix search
can make those representations detect it. No argument here proves that
the common radical is always trivial, and none produces a nonsingular
normal-closure identity killing a nontrivial element of it.

There are consequently two distinct missing outcomes: a general reason
that this possible coefficient kernel vanishes, or an explicit nonsingular
identity (11) together with proof that its old word is nontrivial. Neither
has been obtained. The universal Kervaire--Laudenbach root remains OPEN.
