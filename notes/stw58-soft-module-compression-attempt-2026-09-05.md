# STW LVIII: a noncentral soft-module compression attempt

Date: 2026-09-05. Independent of the LXXVI mixed-Cu gluing lane.
The module realization below is verified; the required homotopy
compression estimate is not proved.

## The actual module sandwich supplied by purity

Let `B` be unital separable simple stably finite and pure, and fix
`n>=2`. Almost divisibility gives a nonzero class `x in Cu(B)` with

`n x <= [1_B] <= (n+1)x`.                              (1)

Lin gives stable rank one for `B`. Choose a countably generated
Hilbert B-module `X` representing `x`. The stable-rank-one Hilbert
module interpretation of Cu order realizes (1) as isometric module
embeddings

`X^n -> B -> X^(n+1)`.                                (2)

Here an isometric Hilbert-module embedding is not automatically
adjointable. The second embedding **is** adjointable, because its
domain is the free rank-one B-module: it is `b -> xi b` for a vector
`xi in X^(n+1)` with `<xi,xi>=1_B`, and its adjoint is
`eta -> <xi,eta>`. Its range projection is the compact operator
`P=theta_(xi,xi)` on `X^(n+1)`.

Set `D=K_B(X)`. Since `B` is simple and `X` is nonzero, `X` is a full
`D`--`B` imprimitivity module. Thus `D` is simple and Morita equivalent
to `B`, and it has stable rank one. Moreover,

`P in M_(n+1)(D)`, and `B ~= P M_(n+1)(D) P`.           (3)

Under the induced Cu Morita isomorphism, the class of `X_B` becomes
the class of the standard `D_D` module, and the class of `B_B`
becomes `[P]`. Consequently (1) becomes

`n [D] <= [P] <= (n+1)[D]` in `Cu(D)`.                 (4)

The notation `[D]` means the Cu class of the standard Hilbert module
`D_D`, equivalently that of a strictly positive element of the
sigma-unital algebra `D`. It does not mean a projection or a unit.
In the noncompact case `D` need not be unital. The right inequality
in (4) is realized by the actual compact projection `P` in (3).

This is more information than merely having an unrelated
dimension-drop map. It rewrites every coefficient of a proposed
stable nullhomotopy in a single explicit corner of `M_(n+1)(D)`.
The part missing from an exact matrix decomposition is the first
embedding in (2), which need not have an adjoint or a complemented
range.

## Where the attempted contraction stops

Given a stably null `gamma:S^k -> U(B)`, (3) transports it and any
chosen stable nullhomotopy into matrices over the corner `P`.
The exact-divisibility proof would next replace `P` by `1_n` over a
unital stable-rank-one coefficient algebra and apply the connected
stable-rank matrix estimate. Equation (4) does not license this.

The natural proposed replacement is a relative stable-rank estimate:
one would want sufficiently many copies of the standard module
contained in `P D^(n+1)` to give connectivity of its last-column
spaces over a parameter sphere, with the estimate improving as
`n` increases. A proof must use the non-adjointable embedding in (2)
and maintain exact unitary boundary conditions. No such estimate
has been established here.

Two concrete operations attempted in this formulation fail:

1. **Projecting onto the embedded copies.** The image of `X^n` in
   `B` is only a Hilbert submodule. Its orthogonal projection exists
   in an appropriate bidual but need not belong to `B` or be an
   adjointable operator on the module. Compressing the coefficient
   family by that projection is therefore not an operation in the
   original algebra.
2. **Using positive cutoffs instead.** Compact positive contractions
   approximating the identity on `X` do lie in `D`. Their images
   yield legal completely positive compressions, but compression
   does not preserve multiplication or unitarity for a general
   coefficient family. Small quasitracial size of a discarded
   remainder supplies no norm-small defect. Thus polar correction
   cannot be invoked until a separate norm-invertibility estimate
   is supplied.

The first failure is absent when `x` is a projection class and
`n x=[1_B]`, exactly the prior-art case in the companion note. The
second failure is absent for a genuinely central construction, but
central dimension-drop maps are not among the available hypotheses.

This reduction has not produced a contraction even in degree two.
It does not establish a K-stability theorem or a counterexample.

## One precise missing lemma

The following statement would suffice to finish this route. It is
posed as a lemma to prove, **not** asserted as a theorem:

> For each finite-dimensional compact metrizable space `Y` there is
> an integer `N(Y)` such that, whenever `D` is sigma-unital of stable
> rank one and `P in M_(n+1)(D)` is a full projection satisfying
> `n[D] <= [P] <= (n+1)[D]`, with `n>=N(Y)`, one has
> `csr(C(Y, P M_(n+1)(D) P)) <= 2`.

Only the case where `D` is simple and pure is needed here. Under
that restriction, the sandwich above would apply separately for
each torus `Y=T^j`; Rieffel's Theorem 3.3 would then give all-degree
K-stability of `B`. This is a connected-stable-rank assertion about
the actual coefficient corner, not about a scalar dimension-drop
subalgebra. It supplies the exact boundary-controlled last-column
transitivity needed by the stabilization fibration.

## A uniform obstruction to projection and cutoff repairs

There is a definite obstruction to two proposed proofs of that
lemma, already for the Jiang--Su algebra `B=Z`. This algebra has
stable rank one and the required soft divisibility, but its only
projections are zero and one.

First, no embedding `X^n -> B` in (2), with `n>=2` and `X!=0`, can
be adjointable. If it were, its nonzero range projection in `B`
would equal one. Thus `B_B ~= X^n` and
`B ~= K_B(X^n)=M_n(K_B(X))` would be unital. A matrix algebra is
unital only when its coefficient algebra is unital; the resulting
matrix unit `e_11` would be a nontrivial projection in `B`, a
contradiction.

Let `q` be the open support projection in `B**` of the hereditary
algebra corresponding to that submodule. It is nonzero and proper:
if `q=1`, the corresponding closed right ideal is all of `B`, so
the embedding is onto and has the impossible adjoint just discussed.
Then one has the exact norm separation

`dist(q,B)=1/2`.                                      (5)

For the lower bound, suppose `||q-a||<delta<1/2` for `a in B`.
Replacing `a` by its self-adjoint part preserves this inequality.
Its spectrum lies in `[-delta,delta] union [1-delta,1+delta]`.
The spectral projection for the upper interval belongs to `B`
and must be either zero or one. In the first case `||a||<=delta`,
contradicting `||q-a||<delta`; in the second case
`a >= (1-delta)1`, and compression to `1-q` again contradicts
`||q-a||<delta`. The upper bound follows from `a=(1/2)1`.

There is also an exact obstruction to the positive-cutoff repair.
Every norm-one positive contraction `a` in the hereditary algebra
supported by `q` has zero in its spectrum, since `q<1`, and one in
its spectrum. A self-adjoint element of a unital projectionless
algebra has connected spectrum: a spectral gap would produce a
nontrivial projection by continuous functional calculus. Hence

`spec(a)=[0,1]`, and `||a-a^2||=1/4`.                 (6)

In particular, these norm-one cutoffs cannot become approximate
projections in norm, however large `n` becomes. Even for the scalar
unitary `u=-1`, the natural expression that compresses on `a` and
leaves the complementary part fixed,

`T_a(u) = a u a + (1-a^2)`,

is `1-2a^2`, which is noninvertible because its spectrum contains
zero. It therefore has no polar correction to a unitary. The
constant path to `-1` is itself harmless; this example refutes the
specified compression-and-polar-correction formula, not K-stability
of `Z` or the proposed connected-stable-rank lemma.

Thus replacing the non-adjointable embedding by a norm-close
projection, or making its positive cutoffs norm-idempotent before
applying a universal polar repair, fails with uniform constants
even in a known K-stable example. A successful soft-module proof
must use additional homotopy operations rather than either repair.

## A positive coefficient-dependent contraction on each matrix piece

There is nevertheless a usable local contraction statement. It does
not assume that the coefficients are scalar or commute with matrix
units.

**Lemma (stable-range consequence).** Let `B` be unital and let
`C subset B` be a full hereditary subalgebra with an isomorphism
`C ~= M_N(D)`, where `sr(D)=1`. Fix `k>=1` and `N>=k+2`.
Suppose `gamma:S^k -> U(B)` is based at one, is norm-continuous,
and satisfies `gamma(x)-1 in C` for every `x`. If its stable
K-theory class in `K_(k+1)(B)` vanishes, then it has a based
null-homotopy through unitaries of the form `1+c`, `c in C`.

**Proof.** First consider a nonunital `D`, with minimal unitization
`D~`. Stable rank one means `sr(D~)=1`. Embed `S^k` as a closed
subset of an open coordinate chart in `T^(k+1)`. The standard
crossed-product stable-rank estimate, applied successively to the
trivial actions of `Z`, and then the quotient estimate give

`sr(C(S^k,D~)) <= sr(C(T^(k+1),D~)) <= k+2`.

Rieffel's degree-zero stabilization theorem (Theorem 2.10 in the
1987 paper) therefore identifies the path components of
`U(M_N(C(S^k,D~)))` with its stable K1 group. The same holds for
the constant coefficient algebra `D~`. Evaluation at the sphere
basepoint splits the map space explicitly as the product of the
constant unitary group and the based map space, using
`f(x) = f(x_0) [f(x_0)^* f(x)]`. Consequently stabilization on
`pi_k U(M_N(D~))` is an isomorphism in this range.

The scalar quotient also splits: writing `q` for
`U(M_N(D~))->U(N)`, the homeomorphism

`g -> (g q(g)^*, q(g))`

identifies its total space with the product of its kernel and
`U(N)`. The scalar groups are in their usual stable range, since
`N>=k+2`. Passing to the two split homotopy groups proves that
the kernel `U_N(D)={1_N+a : a in M_N(D), 1_N+a unitary}` has
injective stabilization in degree `k` (indeed an isomorphism).
Full hereditary inclusion gives the usual Morita K-theory
isomorphism `K_*(C)->K_*(B)`. Thus the vanishing assumption on
`gamma` is vanishing in the stable K-theory of `M_N(D)`, and
injectivity gives the asserted contraction. For unital `D`, the
same proof uses `D` directly and omits the scalar quotient; if
`C` has a proper unit projection `p` in `B`, identify its unitary
`u` with `u+(1-p)` in `B`. QED.

Explicitly, there is no unresolved scalar-quotient lifting step in
this proof. Having obtained a based null-homotopy
`H:S^k x [0,1]->U(M_N(D~))` from `gamma` to one, let `j` denote
the scalar matrix inclusion and define

`H_0(x,t)=H(x,t) j(q(H(x,t)))^*`.

Then `q(H_0)=1_N` throughout. Both endpoints stay fixed, since
`q(gamma)=1_N`, and `H_0(x_0,t)=1_N` whenever the original
homotopy is based. Thus `H_0` is the required null-homotopy in
`1_N+M_N(D)`, not just one in the larger unitization matrix algebra.

Here is how the available soft divisibility supplies the matrix
pieces needed by this lemma. A unital map
`theta:Z_(N,N+1)->B` gives its two canonical commuting order-zero
maps `phi_0:M_N->B` and `phi_1:M_(N+1)->B`, with

`h_0=phi_0(1)`, `h_1=phi_1(1)`, `h_0+h_1=1`.

For each nonzero `h_i`, the supporting homomorphism for `phi_i`
is a unital matrix homomorphism into
`M(Her(h_i))`. To check the multiplier assertion directly,
`pi_i(e_ab) h_i^(1/2)` belongs to `B` by the order-zero functional
calculus, and multiplying elements of `h_i^(1/2) B h_i^(1/2)`
on either side preserves their hereditary closure. Hence

`Her(h_0) ~= M_N(D_0)`,
`Her(h_1) ~= M_(N+1)(D_1)`

for the corresponding matrix corners `D_i`, whenever the displayed
hereditary algebra is nonzero. Stable rank one passes from `B` to
these corners. Simplicity makes each nonzero piece full. It is
possible for an endpoint-factor map `theta` to make one piece zero;
the other remains a unital matrix piece, so no nonzero assumption
on both pieces is silently imposed.

Thus every stably null coefficient-dependent family already
supported in either nonzero piece contracts for `N>=k+2`. This
is stronger than the scalar dimension-drop calculation: the
coefficients within the hereditary piece are unrestricted.

What this argument does **not** provide is a homotopy moving a
general sphere family into one such piece, or a valid fragmentation
of that family into supported families with controlled K-classes.
The equality `h_0+h_1=1` is insufficient by itself: the `h_i`
commute with each other but need not commute with the coefficients.
The noninvertible cutoff formula above prevents simply inserting
them into a general unitary and applying polar decomposition.
The next needed construction is precisely this localization of
families, including their based boundary conditions.

## The overlap is another large matrix piece

For these particular commuting positive contractions, put
`C_i=Her(h_i)` and `C_01=Her(h_0 h_1)`. Then

`C_0 intersection C_1 = C_01`.

Indeed the support projections of `h_0` and `h_1` commute in `B**`,
their meet is the support of their product, and intersections of
hereditary subalgebras correspond to meets of their open supports.
Here the meet is open because it is the support of the actual
positive element `h_0 h_1`.

If `h_0 h_1!=0`, both supporting matrix homomorphisms restrict to
the multiplier algebra of `C_01`, where their ranges commute and
their units are the unit of that multiplier algebra. Their product
therefore supplies a unital copy of `M_N tensor M_(N+1)`, and

`C_01 ~= M_(N(N+1))(D_01)`.

The same multiplier check used for the two pieces applies to the
product, or follows directly from the interior matrix fiber of
the dimension-drop algebra. Again `sr(D_01)=1`, and simplicity
makes the nonzero overlap full. Consequently the local
coefficient-dependent stabilization lemma applies to both pieces
and their overlap in every fixed degree for large `N`.

The nonzero-overlap condition has not been deduced from an arbitrary
unital dimension-drop map: an endpoint-quotient map can give
`h_0 h_1=0`. The statement above is conditional on nonzero overlap.

An unrestricted homotopy-pushout assertion for hereditary covers
would be false. For example, in `B=M_3(C)` take

`h_0=diag(1,1/2,0)`, `h_1=diag(0,1/2,1)`.

Both hereditary pieces and the overlap are full, and `h_0+h_1=1`.
Their unitary groups embedded by adjoining the complementary
identity are respectively `U(2),U(2)` and `U(1)`. The homotopy
pushout of `U(2) <- U(1) -> U(2)` has third integral homology
`Z direct-sum Z`, by Mayer--Vietoris for the double mapping cylinder:
`H_3(U(1))=H_2(U(1))=0` and `H_3(U(2))=Z`. Its natural map
to `U(3)`, whose third homology is `Z`, cannot be a weak homotopy
equivalence. The two `U(2)` subgroups do generate `U(3)`; generation
therefore cannot supply the missing parameterized assertion.

This example does not refute a **stable-range** excision statement
for the large dimension-drop pieces above: its overlap has matrix
size one and is outside the degree-three range. It identifies an
essential hypothesis for the next attempted theorem. A successful
argument must explicitly use the increasing connectivity of the
large overlap, in addition to fullness and `h_0+h_1=1`.

## Inputs

- Lin, *Strict comparison and stable rank one*, Theorem 3.6:
  https://doi.org/10.1016/j.jfa.2025.111065 .
- Coward--Elliott--Ivanescu, *The Cuntz semigroup as an invariant
  for C*-algebras*, Theorem 3, stable-rank-one Hilbert-module classification
  and the realization of Cu order by module embedding:
  https://arxiv.org/abs/0705.0341 .
- Rieffel, *The homotopy groups of the unitary groups of
  non-commutative tori*, Theorems 3.3, 4.7, and 4.13:
  https://jot.theta.ro/jot/archive/1987-017-002/1987-017-002-005.pdf .

The exact-divisibility prior-art result is frozen separately in
`notes/stw58-coefficient-unitary-stabilization-2026-09-05.md`.
