# Direct Kazhdan attack on the hyperbolic operator-MF problem

Date: 2026-09-12. This continues the attempted proof, rather than treating
the failed weak-quasidiagonality citation as a resolution. The target is a
non-MF word-hyperbolic group. The calculations below give exact quantitative
lemmas for two proposed analytic constructions. They do not yet establish
the target or the implication from non-residual-finiteness to non-MF.

## 1. What the established Kazhdan corner theorem consumes

The theorem `normal-kazhdan` in `non_mf_groups_exist.tex` proves the following.
For a countable group `G` and normal Kazhdan subgroup `K`, if **every**
operator-norm asymptotic representation `V_n` has

```text
||V_n(k)-I||_(2,tr) -> 0       for every k in K,
```

then every norm-corona homomorphism kills `K`. The quantifier includes
representations obtained by cutting to nonzero invariant corona corners and
renormalizing the trace by their own ranks. This is why the theorem can
promote Hilbert--Schmidt collapse to operator-norm collapse.

For a finitely generated group without finite quotients, exact
finite-dimensional unitary representations are trivial: their images are
finitely generated linear groups, hence residually finite; any nontrivial
image would yield a finite quotient of the source. That argument does not
give the displayed assertion for asymptotic representations. The direct
attack must produce it, or a different norm obstruction.

## 2. Exact estimate for a spectral low cluster

Let `V_s in U(d)` be an inverse-paired tuple indexed by a finite symmetric
generating list `S`. On `M_d`, define the lazy adjoint channel

```text
T = (1/2) id + (1/(2|S|)) sum_(s in S) Ad(V_s).
```

It is unital, trace preserving and completely positive. On the Hilbert
space with normalized Hilbert--Schmidt norm it is selfadjoint with spectrum
in `[0,1]`. Fix `0<gamma<1` and put

```text
P = 1_[1-gamma,1](T),
alpha = ||(I-T)P||_(2->2).
```

Assume the complementary spectrum is contained in `[0,1-gamma]`. For every
integer `m>=1`, the spectral theorem gives the exact bound

```text
||T^m-P||_(2->2) <= max{(1-gamma)^m, m alpha}.             (2.1)
```

Indeed, on `ker(P)` use the complementary spectral bound. On `ran(P)`,
every eigenvalue `lambda` satisfies `1-alpha<=lambda<=1`, and
`1-lambda^m <= m(1-lambda) <= m alpha`.

For any linear map `A:M_d->M_d`, normalized Hilbert--Schmidt norm satisfies

```text
||A||_(infinity->infinity) <= sqrt(d) ||A||_(2->2).
```

Apply `||z|| <= sqrt(d)||z||_2` to the output and `||x||_2<=||x||` to the
input. Hence

```text
||T^m-P||_(infinity->infinity)
 <= sqrt(d) max{(1-gamma)^m, m alpha}.                    (2.2)
```

For a sequence with one fixed `gamma>0`, if

```text
alpha_n sqrt(d_n) log(d_n+1) -> 0,                       (2.3)
```

there are integers `m_n` for which the right side of (2.2) tends to zero.
For an explicit selection, set `b_n=alpha_n sqrt(d_n)` and

```text
m_n = ceil(C log(d_n+1) + min{n,b_n^(-1/2)}),
```

where `b_n^(-1/2)=+infinity` when `b_n=0` and
`C>1/(2[-log(1-gamma)])`. The first summand controls the high spectrum;
the diverging second summand makes that error tend to zero also on
bounded-dimension subsequences. The low-spectrum term tends to zero since
`b_n log(d_n+1)->0` and
`b_n min{n,b_n^(-1/2)}<=sqrt(b_n)`.

Thus (2.3) gives **ucp maps `T_n^(m_n)` close to the spectral projections**
in the operator norm on linear maps `M_(d_n)->M_(d_n)`. It does not say that
the projections themselves are completely positive, that their ranges
are matrix subalgebras, or that the group approximations can be corrected
to exact representations.

## 3. Why property (T) gives a low cluster, not an exact fixed space

For a norm asymptotic representation of a Kazhdan group, the maps
`Ad(V_n(g))` determine an exact representation in the norm corona of the
Hilbert-space operators on `M_(d_n)`. The image of the Kazhdan projection
is the spectral projection of the image of the lazy average at `1`.
Functional calculus therefore supplies a fixed gap and coordinate
projections of the form in Section 2 with `alpha_n->0`.

Positive coordinate eigenvalues tending to zero for `I-T_n` are allowed.
Replacing this low cluster by `ker(I-T_n)` would discard precisely the
part of the argument that needs control. In particular, the corona
argument alone does not supply (2.3).

A finite sum-of-squares certificate can make this statement quantitative.
Use a scaled Laplacian `L=I-T` and a certificate

```text
L^2-kappa L = sum_j a_j* a_j
```

in the group algebra. The existence of such certificates is
[Ozawa's theorem](https://arxiv.org/abs/1312.5431). If evaluating a fixed
certificate on an approximate adjoint tuple has residual operator norm at
most `epsilon`, then

```text
L_n^2-kappa L_n >= -epsilon I.
```

For `epsilon<kappa^2/4`, every eigenvalue lies outside the open interval

```text
(r_-,r_+),       r_±=(kappa ± sqrt(kappa^2-4epsilon))/2.
```

The low cluster is at most
`r_- = 2epsilon/(kappa+sqrt(kappa^2-4epsilon)) <= 2epsilon/kappa`;
the high cluster begins at `r_+>=kappa/2`. Consequently one may take
`alpha<=2epsilon/kappa` and `gamma=kappa/2` in (2.1)--(2.3), after making
the harmless scaling that puts `L_n` in `[0,1]`. This yields a sufficient
rate `epsilon_n sqrt(d_n) log(d_n+1)->0` for the stated ucp approximation
of the low-cluster projections. It supplies no rank bound on MF models.

## 4. The rank-one low cluster does not reduce the matrix dimension

The identity matrix is fixed by every adjoint channel. Therefore, if
`rank(P)=1` as a projection on `L^2(M_d)`, then

```text
P(x)=tr_d(x) I.
```

This is already an exact unital trace-preserving completely positive
projection, for arbitrary `d`. Its range has dimension one while the
matrix representation may have arbitrarily large dimension. Cutting to
this range is a cut in the Hilbert space of **matrices**, not a nonzero
invariant subspace of the original `C^d` carrying the group model.

Thus minimizing the rank of the adjoint low cluster does not itself
minimize the matrix dimension. An additional argument would have to show
that quotientlessness forbids such approximately irreducible, large
matrix models. No such argument follows from property (T) alone.

The repository contains a related warning in
`leavitt-kazhdan-heat-rounding-boundary-and-factorial-center-countermodel-2026-09-08.md`,
Section 6: certain normalized-HS microstates have scalar heat rounding
while remaining far from all same-dimension exact representations. Those
are not norm-MF counterexamples, so they do not decide the present problem.
They do prevent replacing the missing representation-repair argument by
the assertion that a scalar heat projection has been found.

## 5. What fixed-rank compactness actually proves

Let `G=<S|R>` be finitely presented with no nontrivial finite-dimensional
unitary representations. Fix a nonidentity word `w`, a separation `c>0`,
and a dimension bound `D`. There is `delta(D,w,c)>0` such that no tuple
in `U(d)^S`, `1<=d<=D`, simultaneously satisfies

```text
max_(r in R) ||V(r)-I|| < delta(D,w,c),
||V(w)-I|| >= c.                                          (5.1)
```

For each `d`, restrict the continuous maximum-relator-defect function to
the compact set `||V(w)-I||>=c`. If this set is nonempty, its minimum is
positive: a zero would be an exact representation separating `w`.
Taking the minimum over `1<=d<=D` proves (5.1); empty sets impose no
restriction. Accordingly, separated MF models for such a group must
escape every bounded dimension along a subsequence on which the word is
separated.

This establishes only `d_n->infinity`, not an upper bound on `d_n` in
terms of the defect. In particular it does not justify selecting models
with `epsilon_n log(d_n)->0` or (2.3). Identity padding cannot disprove
the existence of an efficiently chosen sequence either: the issue is the
growth of **minimal** feasible dimensions, not arbitrary padded ones.

## 6. A stronger cohomological route and its precise normalization

[De Chiffre--Glebsky--Lubotzky--Thom](https://arxiv.org/abs/1711.10238)
establish Frobenius stability for finitely presented 2-Kazhdan groups.
Here the Frobenius norm is unnormalized. Thus if such a group has a
sequence of separating operator-norm models with relator defects
`epsilon_n` and dimensions `d_n` satisfying

```text
sqrt(d_n) epsilon_n -> 0,                                (6.1)
```

the models are Frobenius asymptotic representations, since
`||A||_F<=sqrt(d_n)||A||`. Frobenius stability corrects them to exact
representations; `||A||<=||A||_F` preserves operator-norm closeness and
separation of each fixed word. This contradicts the absence of nontrivial
finite-dimensional representations.

Two independent inputs are absent from the hyperbolic quotientless
construction: 2-Kazhdan cohomology vanishing and the rate (6.1). Neither
is a consequence of its stated property-(T) hypothesis. In particular,
using normalized Hilbert--Schmidt norm in the cited stability theorem
would change that theorem.

## 7. Why the existing algebraic compression cannot finish this lane

For a non-elementary subgroup `L` of a hyperbolic group `G`, `C_G(L)` is
finite. If `uLu^(-1)<=L`, then

```text
C_G(L) <= u C_G(L) u^(-1).
```

Both finite groups have the same order, so equality holds. Hence
`[ucu^(-1),l]=1` for every `c in C_G(L)` and `l in L`. These are exactly
the generators of the compression defect used by the established
non-MF criterion, so that defect is trivial in this setting. If `L` is
a finite Kazhdan subgroup, its conjugate inclusion is equality directly
and the same conclusion follows. An infinite virtually cyclic subgroup
does not have property (T). Thus none of the possible Kazhdan subgroups
escapes this restriction.

This restates the existing
`hyperbolic-compression-centralizer-rigidity` calculation at the precise
input of the operator-norm theorem. A successful direct construction
needs a different source of universal Hilbert--Schmidt collapse, a
dimension-uniform representation-repair argument, or a new norm
obstruction.

## 8. A projective repair would suffice

For a finitely generated group without finite quotients, every homomorphism
to `PU(d)` is trivial. Indeed, the adjoint action embeds `PU(d)` faithfully
in `GL(M_d(C))`. A nontrivial projective image would therefore be a
nontrivial finitely generated linear image, and residual finiteness of
that image would provide a finite quotient of the source.

Such a group is also perfect: its finitely generated abelianization is
residually finite, and so must be trivial. Let `V_n` be a norm asymptotic
representation of any perfect group. If

```text
dist(V_n(g), U(1) I) -> 0       for every fixed g,
```

then `||V_n(g)-I||->0` for every `g`. To see this, choose scalar unitaries
close to each of `V_n(a)` and `V_n(b)`. Scalars commute, so
`||[V_n(a),V_n(b)]-I||->0`; asymptotic multiplicativity gives
`||V_n([a,b])-I||->0`. Every element is a fixed finite product of
commutators, and another finite telescoping estimate proves the claim.

Consequently, to prove non-MF for a nontrivial finitely generated
quotientless group, it would suffice to prove **projective** repair: for
each norm asymptotic representation, exact homomorphisms
`rho_n:G->PU(d_n)` can be found with

```text
dist_PU([V_n(s)],rho_n(s)) -> 0       for each generator s,
dist_PU([U],[W]) = inf_(z in U(1)) ||U-zW||.
```

The exact homomorphisms are trivial by the first paragraph. Word
telescoping propagates scalar closeness from generators to all fixed
elements, and perfectness then gives norm collapse by the second
paragraph. Thus even a separating sequence cannot exist.

This reduces the requested repair conclusion but does not establish its
hypothesis. Passing to `Ad(V_n)` alone produces another approximate
representation; it does not make its relator defects vanish. Property
(T) controls first cohomology for Hilbert-space coefficients, whereas a
dimension-uniform correction of noncentral relator curvature requires
additional information about second cohomology with operator-norm
coefficients or a different nonlinear correction theorem.

The newer conditional stability theorem of
[Willett, author version dated 21 May 2026](https://math.hawaii.edu/~rufus/rep%20kk%204.pdf)
does not supply this hypothesis: Remark 5.7 states that its required good
class of finite-dimensional representations already implies the full
group C*-algebra is residually finite dimensional, and hence the group is
residually finite when finitely generated. Applying that condition to the
quotientless candidate would assume the contradiction to be proved.

## 9. Explicit logarithmic almost central contractions

Here is a finite-dimensional construction that explains the dimension
loss in a proposed norm-averaging argument. Let `U_1,...,U_r in U(d)`,
where `r>=1`, and fix a unit vector `xi`. Include inverse letters in word
length. For `j>=0`, let

```text
H_j = span{w(U)xi : |w|<=j},       P_j = projection onto H_j,
H_(-1) = {0},                     P_(-1) = 0.
```

For every generator or inverse generator `U_s`,

```text
H_(j-1) <= U_s H_j <= H_(j+1),
P_(j-1) <= U_s P_j U_s* <= P_(j+1).                    (9.1)
```

The left inclusion follows by applying `U_s^(-1)` to words of length at
most `j-1`; the right inclusion follows by applying `U_s` to words of
length at most `j`. For an integer `m>=1`, set

```text
A_m = (1/m) sum_(j=0)^(m-1) P_j.
```

Summing (9.1) and telescoping the two shifted sums gives

```text
-I/m <= U_s A_m U_s* - A_m <= I/m.
```

Thus `0<=A_m<=I` and

```text
max_s ||[U_s,A_m]|| <= 1/m.                            (9.2)
```

Also `A_m xi=xi`, while `A_m` vanishes on `H_(m-1)^perp`. The estimate

```text
dim(H_(m-1)) <= sum_(j=0)^(m-1) (2r)^j < (2r)^m
```

shows that, whenever `(2r)^m<d`, both `0` and `1` are eigenvalues of
`A_m`. In particular,

```text
dist(A_m,C I) = 1/2,       tr_d(A_m) <= (2r)^m/d.        (9.3)
```

For fixed `r` and `d_n->infinity`, choose
`m_n=floor((log_(2r) d_n)/2)` after discarding the finitely many terms
where it is zero. The resulting sequence defines a positive contraction
in the relative commutant of the generated norm-corona algebra. Its
distance from scalar coordinate sequences is exactly `1/2`, its norm is
one, and its normalized coordinate traces tend to zero. Its generator
commutators decay at rate `O(1/log d_n)`.

The construction requires no relator error at all. It also applies to
exact irreducible representations of one fixed Kazhdan group in growing
dimensions. Hence no dimension-independent bound of the form
`dist(A,C I)<=C max_s ||[U_s,A]||` follows merely from irreducibility and
a Hilbert--Schmidt adjoint spectral gap.

If the tuple is irreducible and `(2r)^m<d`, every inclusion
`H_j<H_(j+1)` for `0<=j<m` is strict. Otherwise one `H_j` would be
invariant under all generators and inverses, contradicting
irreducibility. The eigenvalues of `A_m` therefore include every point
of `{0,1/m,...,1}`. Consequently their norm-corona limit has spectrum
`[0,1]`. There is no fixed spectral gap across which its nontrivial
spectral projections could be recovered by continuous functional
calculus.

## 10. A uniform gap for projections survives the preceding contractions

The preceding continuous spectrum issue has a quantitative counterpart.
Suppose the lazy adjoint channel from Section 2 has scalar fixed space
and satisfies

```text
< (I-T)X,X >_2 >= gamma ||X||_2^2
       whenever tr_d(X)=0,                              (10.1)
```

where `gamma>0`. This is exactly the case when the spectral low cluster
has rank one and the complementary spectrum has the stated fixed gap.
Let `P` be any projection with `0<P<I`, set `t=tr_d(P)`, and put
`eta=max_(s in S) ||[U_s,P]||`. Then

```text
gamma t(1-t)
 <= <(I-T)P,P>_2
  = (1/(4|S|)) sum_(s in S) ||[U_s,P]||_2^2
 <= (1/2) min(t,1-t) eta^2.                             (10.2)
```

For the last inequality, the rank of `[U_s,P]` is at most
`2 min(rank(P),d-rank(P))`; this follows either by writing its two
off-diagonal blocks or by replacing `P` with `I-P`. Multiplying its
operator norm squared by that normalized rank bounds its squared
normalized Hilbert--Schmidt norm. Dividing (10.2) by the positive number
`min(t,1-t)` yields

```text
eta^2 >= 2 gamma max(t,1-t) >= gamma.                    (10.3)
```

So every nontrivial projection has some generator commutator of norm at
least `sqrt(gamma)`, even though the contractions in Section 9 almost
commute at logarithmic rate. Taking a spectral cutoff of those
contractions cannot produce a nontrivial projection whose operator-norm
commutators tend to zero in this case. This rules out that proposed
dimension reduction for the rank-one low-cluster branch; it does not
rule out MF models for the quotientless group.

## 11. Quantitative bootstrap from a fixed projective neighborhood

For a perfect finitely presented group `G=<x_1,...,x_r|R>`, choose fixed
commutator expressions

```text
x_i = product_k [a_(ik),b_(ik)] in G,
w_i = x_i^(-1) product_k [a_(ik),b_(ik)] in F_r.
```

Choose a finite van Kampen decomposition of each `w_i` into conjugates
of defining relators and their inverses. Let `A>=1` bound their numbers
of factors, and put

```text
B = max(1, 2 max_i sum_k |a_(ik)| |b_(ik)|),
D(U) = max_i ||U_i-I||,
E(U) = max_i dist(U_i,U(1)I),
delta(U) = max_(r in R) ||r(U)-I||.
```

Then every unitary tuple in every dimension satisfies

```text
D(U) <= A delta(U) + B E(U)^2.                         (11.1)
```

Indeed, choose scalar unitaries `z_i` attaining the finitely many
distances defining `E`. For every word `a`, telescoping gives
`||a(U)-a(z)I||<=|a|E(U)`. Subtract those scalar multiples in the identity
`[V,W]-I=(VW-WV)V^*W^*` to get

```text
||[a(U),b(U)]-I|| <= 2|a| |b| E(U)^2.
```

Telescoping along each product of commutators gives the quadratic term
in (11.1). Evaluating the chosen van Kampen decomposition gives
`||w_i(U)-I||<=A delta(U)` and proves the remaining term.

Since `E(U)<=D(U)`, if `E(U)<=1/(2B)`, (11.1) implies
`E(U)<=A delta(U)+E(U)/2`. Substitution back in (11.1) then gives

```text
E(U)<=2A delta(U),       D(U)<=2A delta(U).              (11.2)
```

This is a dimension-independent nonlinear repair theorem inside one
fixed projective neighborhood. Its identity-centered version already
appears in `full-mf-radical-forces-perfect-commutator-bound`; the
projective version removes the need to control the scalar phases first.
It uses only perfectness, not property (T).

For a separating norm-asymptotic representation of the quotientless
candidate, (11.2) shows that its generator tuple cannot eventually enter
this neighborhood. The remaining analytic target is thus global: force
arbitrary sufficiently accurate tuples into that neighborhood, or find
another contradiction for tuples staying outside it. Neither the
adjoint low cluster nor the almost central contractions constructed
above accomplishes that step.

## 12. The moving corner does recover some trace separation

The distinction between a norm-visible block and a trace-visible mark can
be made constructively. Let `G` be a nontrivial countable Kazhdan group
and let

```text
theta:G -> U(Q),       Q=product_n M_(d_n)/directSum_n M_(d_n)
```

be an injective norm-corona representation. Extend it to the full group
C*-algebra, let `p` be the Kazhdan projection there, and put
`q=1-theta(p)`. The extended C*-algebra homomorphism need not be
injective: no MF assumption on the full or reduced group C*-algebra is
being made. Since `u_g p=p`,

```text
theta(g)-1 = q(theta(g)-1)       for every g in G.       (12.1)
```

Thus `q!=0`, and compression to `qQq` preserves the norm separation of
every group element. Choose coordinate projection lifts `q_n`, retain
the nonzero corners, and let `U_n(g)` be unitary lifts of `theta(g)`.
Then `c_n(g)=||[q_n,U_n(g)]||->0`. On `ran(q_n)`, put
`A_n(g)=q_n U_n(g) q_n` and take its unitary polar part `V_n(g)`.
For all sufficiently large `n`,

```text
||A_n(g)* A_n(g)-q_n|| <= c_n(g)^2,
||V_n(g)-A_n(g)|| <= 1-sqrt(1-c_n(g)^2) <= c_n(g)^2.
```

The compressed multiplicative defect has the explicit bound

```text
||A_n(g)A_n(h)-A_n(gh)||
 <= ||U_n(g)U_n(h)-U_n(gh)|| + c_n(g)c_n(h).             (12.2)
```

Adding the three polar correction errors in (12.2) proves that `V_n`
is again a norm-asymptotic representation. All these estimates are
independent of both original and corner dimensions. Inverse pairs can
be chosen compatibly with polar decomposition.

For a finite symmetric generating set `S`, choose `lambda>0` such that
the full-group Laplacian

```text
Delta=1-(1/|S|) sum_(s in S) u_s
```

satisfies `Delta>=lambda(1-p)`. Its image in `qQq` is therefore at least
`lambda q`. Positivity in the norm corona and the preceding polar
estimates imply that, for all sufficiently large retained coordinates,

```text
Delta_n=q_n-(1/|S|) sum_(s in S) V_n(s)
          >= (lambda/2) q_n.
```

Normalize traces by `rank(q_n)`, not by `d_n`. Taking these traces gives

```text
(1/|S|) sum_(s in S) ||V_n(s)-q_n||_(2,tr_qn)^2
       = 2 tr_qn(Delta_n) >= lambda.                    (12.3)
```

Consequently some generator remains separated in normalized
Hilbert--Schmidt norm along a subsequence. Taking a diagonal subsequence
of the normalized characters gives a nontrivial hyperlinear quotient
of `G`. This is the precise established result in
`kazhdan-mf-hyperlinear-fragment` and
`GroupApproximation/Sofic/KazhdanCorner.lean`. If `G` has no finite
quotients, this nontrivial quotient is infinite and again has no finite
quotients. This fact alone is not a contradiction.

There is an additional mark-specific conclusion. Suppose `g` normally
generates `G`. Choose expressions of every `s in S` as a product of at
most `L>=1` conjugates of `g` and `g^(-1)`. Norm-asymptotic
multiplicativity and unitary invariance of the normalized
Hilbert--Schmidt norm give, uniformly over the fixed finite set `S`,

```text
||V_n(s)-q_n||_2 <= L ||V_n(g)-q_n||_2 + o(1).
```

Combining this with (12.3) proves the explicit bound

```text
liminf_n ||V_n(g)-q_n||_2 >= sqrt(lambda)/L.             (12.4)
```

Thus a normal generator does survive in normalized trace in the moving
corner. For an arbitrary marked element, the same proof would require
control of its normal closure. Quotientlessness does not provide the
displayed normal-generation expressions, and property (T) of `G` does
not assert property (T) for all of its normal subgroups. A vector state
that detects a norm outlier need not be invariant under conjugation;
averaging it to obtain a trace can erase that outlier. Neither an
arbitrary minimal invariant matrix block nor a weighted vector state
has yet supplied the missing control for general marks.

For a two-generated nontrivial perfect group `G=<a,b>`, the mark can be
chosen explicitly as `g=[a,b]`: quotienting by its normal closure makes
the two generators commute, so this quotient is abelian and hence
trivial. The commutator is itself nontrivial, since otherwise `G` would
be abelian. Therefore (12.4) applies to this fixed commutator in any
two-generated quotientless Kazhdan candidate. No bound on its matrix
dimensions is needed. This removes trace invisibility for one canonical
mark; it does not forbid the resulting nontrivial hyperlinear quotient.

The constant `L` is obtainable from a finite two-generator perfect
presentation without searching its word problem. The exponent-sum
vectors of the relators span `Z^2`. Choose integer combinations producing
`(1,0)` and `(0,1)`, and form corresponding products `u_a,u_b` of relator
powers with those exponent sums. The free words `a u_a^(-1)` and
`b u_b^(-1)` have exponent sums zero. Sorting their letters into the
abelian order by adjacent interchanges expresses each as a product of
conjugates of `[a,b]` and its inverse; at most the square of its length
interchanges suffice. Since `u_a=u_b=1` in the presented group, these
give the required normal-generation expressions for `a,b`, and inverse
expressions for `a^(-1),b^(-1)`. Their factor counts give an explicit
admissible `L` in (12.4).
