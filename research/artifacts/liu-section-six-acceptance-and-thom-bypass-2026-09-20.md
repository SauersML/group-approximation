# Section 6 acceptance and the Thom bypass

Date: 2026-09-20. This extends the earlier targeted audit with complete
written proofs of two conditional Section 6 statements and an independent
check of the normalization/double implication in Thom's preprint. It is a
textual mathematical verification, not proof-assistant certification.

## Accepted implications and remaining boundary

The following implications have been checked and are supplied as proof
routes, rather than merely marked as having no error located:

1. A fixed-gap physical decomposition of an approximate Kazhdan model,
   with vanishing discarded trace and tuple error, gives full commutant
   internality. The proof includes unequal-rank bounded matching and the
   all-pairs uniformity step.
2. Internal corners tending to full trace, together with one coordinate
   expectation lift valid on every bounded sequence, give full
   internality. The proof explicitly diagonalizes uniform coordinate
   norms; it never diagonalizes an uncountable set of test elements.
3. Universal Kazhdan commutant internality implies all-trace normalization
   for the stated compression pairs, by Thom's conditional theorem.
4. Universal internality plus the established explicit Kun-Thom pair
   implies the existence of a nonhyperlinear group, using Thom's group
   double. This bypasses both Liu Section 7 and the lamp/wreath equivalence
   argument.

Items 1 and 2 are complete conditional theorems. Their routes with empty
`requires` prove the implications whose assumptions are already in the
target claim; they do not prove those assumptions for arbitrary models.
In particular neither route supplies the physical decomposition from
Liu Theorem 5.1. No conclusion here changes that analytic import's review
boundary. Item 2 does not need the general existence theorem for
expectation lifts because the lift is explicitly a hypothesis.

## Primary sources checked

- Jihao Liu, [*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf),
  September 20, 2026, Lemma 6.4, Propositions 6.5-6.6, Theorem 6.7;
  printed pp. 29-38. The same PDF as the previous audit, SHA-256
  `6da1adbd94c82914457f6435426824087dd865a6af3d61d2bcd87a8bec89e71e`.
- Andreas Thom, [*A conditional construction of a nonhyperlinear group and the centralizer problem*](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
  Theorems 1.2-1.3 and full Sections 2-5, printed pp. 2-13. Downloaded
  PDF SHA-256
  `0776bde0857be69c8768f5bf1a816db68a48a36fb5c30f1e48ac474773dd39aa`.
- Adrian Ioana, [*Almost commuting matrices and stability for product groups*](https://ems.press/content/serial-article-files/51186),
  JEMS 27 (2025), equation (2.1), printed p. 4036. Its positive-operator
  Powers-Stormer inequality was checked in the published primary text.
- Gabor Kun and Andreas Thom,
  [*Nonsofic wreath products of residually finite groups*](https://arxiv.org/abs/2608.06222),
  Theorems A and E, are the credited source of the explicit pair and lamp
  mechanism. The already established repository import is retained as
  an explicit prerequisite for the concrete group witness.

The analytic matching/exhaustion mechanisms are Liu's. The conditional
normalization and double construction are Thom's; this is not an
independent discovery claim for either. The previous audit records the
comparison with Liu Section 7 and its different minimal assumptions.

## Section 6: independent checks behind acceptance

The full proof is in
`scalar-expanding-kazhdan-blocks-internality-proof`. Its only external
analytic input beyond basic finite-dimensional linear algebra and finite
tracial algebra facts is Powers-Stormer. The quotient gap follows
directly from the Kazhdan displacement inequality, and does not require
the coordinate-expectation lift of Section 3.

The following points were reconstructed independently because they are
where a false block-matching argument could otherwise hide:

- A minimizing rectangular `Z` is not assumed operator-norm bounded.
  Normalizing `Tr(ZZ*)=r` gives variance control for its modulus; replacing
  its polar part by an isometry `J` produces the bounded sequence before
  taking the ultraproduct. The error has the fourth-root term
  `sqrt(2/c) lambda^(1/4)`.
- A nonzero bounded off-diagonal fixed vector is obtained by the quotient
  Kazhdan gap. Positive traces of both block corners make their scalar
  gaps pass to the quotient. Scalar diagonal corners force the initial
  and final support traces of that vector to agree, so unequal ranks
  become asymptotically equal.
- The final polar repair to a coordinate isometry uses the direction
  `r>=t`; it does not assert that a partial isometry can be completed
  between arbitrary unequal full supports.
- The relation-selection argument divides by physical block weights only
  through Markov's inequality. Uniform relator accuracy on all retained
  blocks is established before choosing worst pairs. The pair maximizers
  may depend on the coordinate and on the witness; the bounded matching
  lemma still applies.
- Stabilized orbit distance includes the identity coordinate. That
  supplies rank comparability and makes its weighted triangle inequality
  adequate for transitive clustering.
- Coherence is exact because each member is aligned with one chosen
  representative. Orthogonal member ranges make `W_i W_j*` matrix units.
  There is no unverified approximate cocycle-to-cocycle step.
- Sector gaps are for the final copied representative tuples. Distinct
  representatives were already separated by mixed energy, and copies of
  one representative have precisely scalar intertwiners. The error
  summation uses member rank, never number of blocks.
- The final conditional-expectation estimate is uniform on the operator
  unit ball and proves both inclusions of the entire commutant, not just
  a diagonal subalgebra.

The proof of `internal-corner-exhaustion-by-uniform-expectations` is
independent of block matching. Its all-bounded-sequence hypothesis is
essential: the maximizing contraction at coordinate `n` can depend on
the maps. Equality on chosen words would not control these maximizers.
Compression estimates include both off-diagonal sectors. The corner
projections need not be central or nested; only positive trace at each
retained label and convergence to full trace are used. Scalar algebras
on the discarded corners preserve unitality in the original dimensions.

Thus the two target claims' actual conditional assertions are proved.
The universal internality assembly still needs the separately reviewed
large-block construction and expectation-lift existence where they are
invoked. No genuine coordinate representations are inferred.

## Thom's exact quantifiers

The centralizer problem on Thom p. 2 quantifies over a homomorphism from
a Kazhdan group into a tracial matrix ultraproduct; it imposes neither a
canonical character nor injectivity. Theorem 1.2 retains that same
homomorphism quantifier and concludes normalization for every group
element of the ambient group. Theorem 1.3 derives nonhyperlinearity of
the double for an infranormal, nonnormal pair, and explicitly includes
all prime powers `q` and all `r,d>=3` in Theorem E's family.

For our target the two groups are finitely generated. Hence universal
internality as stated in `kazhdan-commutants-are-internal` supplies every
instance actually used in Thom's proof: the representations of the
subgroup and the ambient group. There is no need to resolve any possible
formulation for uncountable discrete Kazhdan groups. If subgroup and
ambient group coincide, normalization is immediate; otherwise Thom's
proper-inclusion notation applies.

The hypothesis that finitely many compressors together with the subgroup
generate the actor implies infranormality. The subgroup's own elements
are compressors, so the full compression semigroup generates the group.
Conversely finite generation of an infranormal actor selects finitely
many compressor letters from expressions for a finite generating set.
These observations check both interfaces without an additional group
theory conjecture.

## Thom's finite-dimensional deduction checked

### Near inclusions and relative correction

Thom Lemma 2.2 is the full-unit-ball witness argument: an internal
inclusion implies uniform coordinate one-sided 2-near inclusion. Stable
negligible changes of ambient dimension preserve the algebra under its
specified common corner identification; Lemma 2.3 proves this by cutting
whole summands and at most one partial matrix/multiplicity summand. The
overshoot in dimension is at most `sqrt(m)`, negligible when `m->infinity`;
bounded dimensions are eventually equal. This ensures that the output
has meaning in the original ambient ultraproduct.

In Proposition 3.1, suppose `B subset_(2,epsilon) A` in `M_d`.
The map on `B tensor A'` given by

```text
Phi(b tensor a)=E_A(b)a
```

is unital completely positive: first apply `E_A|B tensor id`, then the
multiplication star-homomorphism of the commuting finite-dimensional
algebras `A,A'`. Its Stinespring isometry `V` has commuting factor
representations, exactly intertwines `A'`, and exactly intertwines every
common subalgebra `D subset A intersect B`. Trace preservation and
orthogonality of `E_A` give

```text
||rho_B(b)V-Vb||_HS^2=2||b-E_A(b)||_HS^2.
```

Average `P=VV*` under `U(B)` to obtain `h`; it also commutes with the
represented `A'`. Haar averaging is an orthogonal projection, giving

```text
Tr(h-h^2)=||h-P||_HS^2<=epsilon^2 d.
```

Cut `Q=1_[1/2,1](h)`. Since `Tr(QP)=Tr(Qh)`, the exact calculation is

```text
||Q-P||_HS^2=Tr min(h,1-h)<=2epsilon^2 d,
|rank Q-d|<=||Q-P||_HS^2.
```

The polar part `W` of `QV` preserves the exact `A'` and common-`D`
intertwining. Both defects of its supports and its squared HS displacement
are `O(epsilon^2 d)`. Independently averaging `QV` over `U(B)` gives a
source intertwiner `T` of rank at least `d-8epsilon^2 d`. These two
intertwiners give the two weighted multiplicity bounds in equation (3.3).
They are not erroneously identified with one another.

The represented source and the commutant of the represented `A'` are
exactly included on `QK`. Under a common stable identification, both unit
balls are uniformly close to the original algebras. For the target
algebra, take commutants on the large supports of `W`; compression and
extension by zero control all contractions. For the source, its
representation is surjective on the unit ball and its intertwining error
is uniform. This checks the common algebra requirement in the correction.

### Reverse near inclusion from scale concentration

For an exact inclusion `B subset C`, write blocks as
`B=direct_sum_i (M_(p_i) tensor I_(q_i))` and
`C=direct_sum_j (M_(r_j) tensor I_(s_j))`, with integer inclusion
multiplicities `k_ji`. Then `r_j=sum_i k_ji p_i` and
`q_i=sum_j k_ji s_j`. On the nonzero intersection of the corresponding
central supports,

```text
R=(r_j/s_j)/(p_i/q_i)>=k_ji^2>=1.
```

An independent Haar calculation gives

```text
integral_(U(C)) ||E_B(u)||_2^2 du
  = (1/d) sum_(j,i) k_ji p_i^2 s_j^2/(q_i r_j)
  = tr(R^-1).
```

Fubini and averaging over `U(B')` turn this mean into the uniform bound

```text
sup_(a in C, ||a||<=1) ||a-E_B(a)||_2
  <=sqrt(2) tr(1-R^-1)^(1/2).
```

Indeed a fixed `u in U(C)` has squared error
`(1/2) integral_(U(B')) ||[u,w]||_2^2`; replace `w` by
`w-E_(C')(w)` and integrate. The mean of the resulting squared distances
is the previous Haar defect. Convex combinations of unitaries give all
contractions. This proves Thom Lemma 4.1 with its stated constant.

Theorem 4.2 starts with aligned internal `D_n subset A_n`, unitary lifts
`u_l,n in D_n'`, one-sided inclusions `u_l* A u_l subset A`, and
`D=A intersect intersection_l {u_l}'`. On each central block of `D_n`,
choose a positive scalar `m` so that the expectation of
`Delta_n/(Delta_n+m)` is `1/2`, where `Delta_n` is the matrix-size divided
by multiplicity operator for `A_n`. Existence follows from continuous
strict decrease from one to zero. This is an expectation-normalized
transform, not an assertion about an unbounded ultraproduct element.

Relative correction keeps the same common copy of `D_n`. The corrected
source scale is at most the corrected target scale. Weighted multiplicity
control and

```text
|a/(a+s)-b/(b+s)|^2<=|a/b-1|   (a,b,s>0)
```

show that their bounded transforms represent `u_l* x u_l` and `x` under
the common identification, even if the scales and `m` are unbounded.
Their order and equal traces imply equality in the finite tracial
ultraproduct. This holds for every compressor, so `x in D` and, by its
coordinate conditional expectation, `x=1/2`.

The corrected transforms therefore both concentrate at `1/2`. Their
ratio identity

```text
R^-1 = x^- (1-x^+) / (x^+ (1-x^-))
```

gives convergence to one in measure. Since `0<=R^-1<=1`, dominated
convergence and Lemma 4.1 give uniform reverse near inclusion. Transferring
it back proves `u_l* A u_l=A`. No scalar gap or bounded number of blocks
was assumed in this finite-dimensional no-drift part.

### Assembling the all-homomorphisms theorem

Given universal internality, apply it to `pi|Gamma` and `pi|G`. Their
commutants are internal and one contains the other. Lemma 2.2 and
relative correction align their coordinate algebras. Every compressor
commutes with the ambient commutant. Uniform unitary witnesses, Haar
averaging and polar completion give its lifts in that common coordinate
commutant. This is Thom Proposition 5.1.

The compressor group relations imply the one-sided inclusion on the
subgroup commutant, and the generation hypothesis identifies the common
fixed algebra with the ambient commutant. Thus all assumptions of
Theorem 4.2 hold and normalization follows. None of these steps uses
injectivity or a canonical group trace. This checks Theorem 1.2 in the
precise scope needed by the new bypass route.

## Short root route through the double

For an infranormal nonnormal pair choose a strict compressor `t` and
`h in Gamma \ t Gamma t^-1`. In `P=G *_Gamma G` denote the two copies of
`t` by `t_1,t_2`. The element `c=t_1^-1 t_2` centralizes the common
subgroup: conjugation by either `t_i` maps it into the same identified
copy of `Gamma`. For any homomorphism `pi:P->U(M)`, normalization on the
first vertex puts

```text
pi(t_1 c t_1^-1)=pi(t_2 t_1^-1)
```

in the `pi(Gamma)` commutant. Thus `[h,t_2 t_1^-1]` is killed.
It is nonidentity: after collecting same-vertex letters its form is

```text
(h t_2) (t_1^-1 h^-1 t_1) (t_2^-1),
```

an alternating reduced word. The middle letter lies outside `Gamma`
because of the choice of `h`; the other two do because a strict compressor
does not lie in `Gamma`. Bass-Serre normal form excludes the identity.
Hence no homomorphism to a tracial matrix ultraproduct is injective.

Kun-Thom Theorem E supplies such a countable finitely generated pair,
already at `q=2,r=d=3`. This proves the root conditionally on universal
internality with only the explicit pair import as an additional named
premise. It avoids the uncertain availability of any stronger Liu
Section 7 per-model statement, and avoids the equivalence between the
ordinary wreath and the double.

## Why Liu Section 7 is still a distinct review item

Thom's proof uses internality of both the subgroup and ambient
commutants. Liu Theorem 7.4 assumes only subgroup internality and constructs
the invariant center by the weighted partition lemma before doing a
different two-scale matching argument. The earlier audit inspected those
steps without finding a concrete error, but the Thom bypass does not
prove that stronger one-model hypothesis. No acceptance route for that
stronger claim is supplied here. It is unnecessary for the shortest
universal-internality-to-root chain.
