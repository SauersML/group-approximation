# Independent review of exact finite abelian component groups

Date: 5 September 2026. Reviewer: the Berend/LXXVI parallel lane.

I read the complete manuscript
`stw59-exact-finite-abelian-component-groups-2026-09-05.md`, the
gauge calculation in Sections 2--4 of the exact factorial proof,
and the exact arbitrary-cyclic proof used for each arm. I found no
mathematical gap or correction needed for the stated theorem.
This is internal mathematical review, not external peer review or
formal verification.

## Checks of the new joined-base argument

1. **The gauge sequence applies to the nonmanifold base.** For a
   rank-`r+1` complex bundle over a finite CW base of dimension
   `2r`, its sphere fiber is `S^(2r+1)`. Section homotopies have
   no obstruction, and based section loops have exactly the
   primary difference group `H^(2r)(X;Z)`. The complex structure
   makes the orientation coefficients trivial. The explicit
   close-section polar charts in the factorial proof give local
   principal-bundle charts; homotopic sections lie in the same
   gauge orbit, so the map is onto. No manifold assumption is
   used here.
2. **The stable gauge identifications occur at the stated rank.**
   After one further line addition the sphere fiber is
   `S^(2r+3)`, and its section space is 2-connected over this
   base. Thus both `pi_0` and `pi_1` remain unchanged by all
   further trivial-line additions. A complementary bundle exists
   over the finite CW base; the complement-and-rotation argument
   identifies the resulting stable groups with `K^1(X)` and
   `K^0(X)`. It also identifies every K0 class with an actual
   loop at rank `r+1`, including the attaining classes below.
3. **The quotient is a group quotient.** The principal-bundle
   boundary concatenates lifted loops by multiplying their
   endpoint components, with possibly the opposite convention.
   Its source is the abelian group `H^(2r)(X;Z)` and it is onto
   because the larger gauge group is connected. Therefore the
   quotient description computes the entire component group,
   rather than only a set of orbits or a cyclic subgroup.
4. **Vector bundle gluing is legitimate.** The arms have common
   rank `R` and finitely many chosen fiber identifications.
   Trivializations on neighborhoods of the arm basepoints glue
   to a trivialization on their wedge neighborhood. Identifying
   the first two trivial directions gives the stated global
   trivial rank-two subbundle. Unequal values of `d_alpha` create
   no rank mismatch, because `e_alpha=R-d_alpha`.
5. **Top cohomology really has independent arm coordinates.**
   Each arm has dimension `2R` and one integral top class. The
   finite wedge has their direct sum in degree `2R`. In degree
   `2R+2m` of its product with `Y`, only the two top degrees can
   contribute. The groups are torsion-free. Thus restriction
   identifies the global top cohomology with `Z^s`; the common
   intersection `{*} x Y` cannot supply an additional class in
   that degree.
6. **The Euler image is exact, not just armwise bounded.** The
   arm coefficient calculation gives divisibility by `d_alpha`
   for every restricted global K0 class. Conversely
   `beta_alpha=kappa_[S^2] L_0` has virtual rank zero. Pullback
   along the collapse onto its arm therefore restricts to zero
   on every other arm, even after the product with `Y`. On its
   own arm the top Chern number of the remaining tautological
   block is of absolute value one, giving exactly
   `+/- d_alpha`. Hence the image is the full direct sum
   `direct_sum_alpha d_alpha Z`, with no hidden cross-arm
   relation. The stable gauge identification realizes these
   classes by actual gauge loops, not only virtual classes.

## Generator transport and the limit

7. Adding a tautological block changes the section-loop relative
   Euler class by multiplication with its top Chern class. The
   written product-zero construction proves the normalization
   without introducing an extra factorial. Restriction to each
   arm commutes with this construction; since the top restriction
   map is an isomorphism, the global map is coordinatewise
   multiplication by signs, with no mixing. The same check
   applies to the initial rank-padding block of size `e_alpha`.
8. The characteristic sphere unitary pulled back by the degree-one
   collapse is the boundary of the top-cohomology generator, as
   verified in the cyclic proof. Its arm extension therefore
   represents the desired cyclic generator. The identity values
   at the wedge point make the armwise gauge transformations
   continuous; disjoint arms make them commute pointwise.
   The `U(d_alpha+1)` contraction is based throughout. Using a
   trivial line in the second copy of the globally glued bundle
   therefore gives the asserted first matrix stabilization and
   glues to the constant homotopy on every other arm.
9. The connecting maps are actual unital injective endomorphism-
   bundle homomorphisms with the indicated evaluation twist. For
   each fixed unitary, its evaluation matrix has a path to one;
   no continuous contraction of the entire matrix-unitary group
   is assumed. Thus the induced map is exactly the identity-
   extension component map already computed, an isomorphism on
   the entire finite group at every stage.
10. The dense-tail/fullness argument proves simplicity, including
    the positive cutdown that passes from a nonzero limit ideal
    to a nonzero stage element in it. Even cells and Morita
    equivalence give stage `K_1=0`; continuity gives limit zero.
    Trace compactness needs only the finite intersection property,
    not surjective restriction maps. Simplicity and faithful
    matrix amplifications establish stable finiteness. Polar
    approximation gives surjectivity of stage components onto
    limit components, and the finite partition/logarithm argument
    gives injectivity of their direct limit. Consequently the
    whole component group is `G`, with the commuting generators
    and their stabilized contractions retained.

The trivial-group UHF case is also valid. The manuscript does not
claim nonabelian realization, purity of the examples, or a second
named-problem resolution. The exact finite-abelian strengthening
passes this independent internal review.
