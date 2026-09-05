---
rg: 2
id: stw99-problem-lxxvi-pure-implies-cu-regular
kind: claim
title: Every pure C*-algebra is Cuntz semigroup regular (STW Problem LXXVI)
root: true
refuted_by:
  - stw99-lxxvi-compact-counterexample
artifacts:
  - research/artifacts/stw99-lxxvi-soft-comparison-audit-2026-08-30.md
  - research/artifacts/stw99-lxxvi-strong-pure-infiniteness-audit-2026-08-30.md
  - research/artifacts/stw99-lxxvi-finite-graph-compact-audit-2026-08-30.md
  - research/artifacts/stw99-lxxvi-finite-tree-noncompact-audit-2026-08-30.md
  - research/artifacts/stw99-lxxvi-finite-graph-projectionless-cycle-audit-2026-08-31.md
  - research/artifacts/stw99-lxxvi-unicyclic-enriched-cu-audit-2026-08-31.md
  - research/artifacts/stw99-lxxvi-cactus-enriched-cu-audit-2026-08-31.md
  - research/artifacts/stw99-lxxvi-finite-graph-compact-core-audit-2026-09-05.md
  - research/artifacts/stw99-lxxvi-one-dimensional-simple-fiber-audit-2026-09-05.md
  - research/artifacts/stw99-lxxvi-scalar-unstable-homotopy-audit-2026-09-05.md
  - research/artifacts/stw99-lxxvi-all-base-compact-k-stability-audit-2026-09-05.md
  - research/artifacts/stw99-lxxvi-soft-realification-surjectivity-audit-2026-09-05.md
  - research/artifacts/stw99-lxxvi-residually-stably-projectionless-audit-2026-09-05.md
  - research/artifacts/stw99-lxxvi-rr0-relative-projection-selection-audit-2026-09-05.md
  - research/artifacts/stw99-lxxvi-rr0-cutoff-relative-selection-audit-2026-09-05.md
  - research/artifacts/stw99-lxxvi-rr0-full-order-reflection-audit-2026-09-05.md
  - research/artifacts/stw99-lxxvi-rr0-finite-projection-patch-realization-2026-09-05.md
  - research/artifacts/stw99-lxxvi-rr0-two-patch-angle-realization-2026-09-05.md
  - research/artifacts/stw99-lxxvi-universal-small-angle-obstruction-2026-09-05.md
  - research/artifacts/stw99-lxxvi-rr0-compact-summand-cancellation-2026-09-05.md
  - research/artifacts/stw99-lxxvi-closed-compact-stratum-realization-2026-09-05.md
  - research/artifacts/stw99-lxxvi-compact-equality-strata-comparison-2026-09-05.md
  - research/artifacts/stw99-lxxvi-rr0-field-cu-regularity-2026-09-05.md
  - research/artifacts/stw99-lxxvi-hereditary-k-stability-and-cutoff-restriction-2026-09-05.md
---

**Problem LXXVI of Schafhauser--Tikuisis--White, _Nuclear C\*-algebras:
99 problems_, arXiv:2506.10902v2.**  If `A` is pure, must the first-factor map

```text
iota_A : A -> A tensor_min Z,       a |-> a tensor 1_Z
```

induce an isomorphism

```text
Cu(iota_A) : Cu(A) -> Cu(A tensor_min Z)?
```

The general problem remains open. The full real-rank-zero coefficient-field
case is internally proved in
`stw99-lxxvi-rr0-simple-pure-field-cu-regularity`: if D is separable,
simple, stably finite, pure, and real rank zero, then

```text
Cu(C_0(X,D)) -> Cu(C_0(X,D tensor Z))
```

is an isomorphism for every second-countable locally compact Hausdorff
X. There is no base-dimension or nuclearity restriction. The
[reviewed proof](artifacts/stw99-lxxvi-rr0-field-cu-regularity-2026-09-05.md)
realizes every target cutoff inside its parent target class while
retaining the compact bundle data at both ends, then takes increasing
suprema. It covers arbitrary accumulating compact fibers.

The abstract characterization of pureness by
`Cu(A) tensor_Cu Cu(Z)` does not itself answer the problem: the missing map is
the canonical external-product morphism from that abstract Cu tensor product
to the Cuntz semigroup of the minimal C\*-tensor product.  The exact reduction
is `stw99-lxxvi-external-cu-tensor-map-is-the-only-gap`.

Two boundaries are currently rigorous.  Cuntz semigroup regularity is closed
under inductive limits (`stw99-lxxvi-cu-regularity-passes-to-inductive-limits`),
so a counterexample cannot be assembled as an ordinary inductive limit of
regular building blocks.  Conversely,
`stw99-lxxvi-compact-cancellation-counterexample-criterion` isolates a
projection-level route to a counterexample: tensoring with `Z` must collapse
noncancellation already present in a pure algebra.

Cu-regularity also passes to ideals, quotients, and hereditary subalgebras by
`stw99-lxxvi-cu-regularity-passes-to-ideals-and-quotients`.  This does not give
extension permanence in the reverse direction: the 2025 theorem that purity
is equivalent to purity of an ideal and quotient leaves the gluing of their
concrete first-factor Cu maps as a genuine remaining hinge.

The traceless idempotent corridor is completely positive.
`stw99-lxxvi-strong-pure-infiniteness-implies-cu-regularity` proves that every
separable strongly purely infinite algebra is pure and Cu-regular, without
nuclearity, stable rank one, or a Z-absorption assumption.  Both its source
and its Z-tensor target are purely infinite, so their Cuntz semigroups are
their ideal lattices; naturality then turns the already-known slice-map ideal
isomorphism into the required first-factor Cu isomorphism.  More generally,
the same proof applies whenever both `A` and `A tensor Z` are purely infinite.

There is also a genuinely non-simple positive class.  A pure, separable,
locally subhomogeneous algebra of stable rank one and topological dimension
zero is Z-stable, hence Cu-regular, by
`stw99-lxxvi-locally-subhomogeneous-positive-class`.
Independently, every interval field over a simple separable stably finite pure
fiber is Cu-regular by
`stw99-lxxvi-interval-fields-over-simple-pure-fibers`; this second result uses
the explicit Cu formula for interval fields and does not assume the fiber is
Z-stable.
The same is now proved for circle fields in
`stw99-lxxvi-circle-fields-over-simple-pure-fibers`: stable rank one cancels
the compact clutching term, while the noncompact term is pointwise.  In
particular `C(T) tensor C*_r(F_2)` is Cu-regular but not Z-stable.


The compact wing is now completely controlled over every finite graph,
without a `K_1`-vanishing hypothesis.
`stw99-lxxvi-finite-graph-compact-clutching-rigidity` classifies projection
bundles by their fiber class and one `K_1`-clutching coordinate per cycle,
and proves that the actual first-factor map preserves all of them.  Thus for
a simple stably finite pure fiber `D`, every compact class of `C(X,D)`
survives tensoring with `Z` for every finite graph `X`. This compact result
alone does not give the full Cu isomorphism: Phillips's circle-with-a-tail
phenomenon requires supportwise clutching. The compact-core theorem below
now retains exactly that data and proves the full finite-graph result.

The full noncompact wing is now controlled over every finite tree, with no
`K_1`-vanishing assumption.
`stw99-lxxvi-finite-tree-formation-preserves-cu-regularity` proves the
natural pointwise formula
`Cu(C(T,D))~=Lsc(T,Cu(D))` for a simple separable stable-rank-one fiber.
The proof attaches leaf edges one at a time: a nonzero unitary mismatch may
flow toward the unprescribed endpoint or disappear where the comparison
vector vanishes, and no cycle forces it back to a prescribed value.  Thus a
simple stably finite pure fiber gives a pure Cu-regular field over every
finite tree, even when its `K_1` is nonzero.  Cyclic graphs remain outside
this theorem.


Cycles are also controlled when the fiber is stably projectionless.
`stw99-lxxvi-stably-projectionless-finite-graph-cu-regularity` proves the
natural pointwise formula `Cu(C(X,D))~=Lsc(X,Cu(D))` for every finite graph,
still with arbitrary `K_1(D)`. After cutting the chords, small spectral slices
at the finitely many paired endpoints erase all clutching mismatches at
arbitrarily small cost, and one simultaneous unitary lift closes every cut.
Thus a simple stably finite pure stably projectionless fiber gives a pure
Cu-regular field over every finite graph. This does not cover coefficients
with nonzero projections or infinite graphs.


The projectionful one-cycle corridor is now classified exactly.
`stw99-lxxvi-unicyclic-enriched-cu-classification` identifies the full Cu
semigroup of a connected unicyclic field with the fiber product of its actual
circle Cu semigroup and its global `Lsc` function over circle evaluation.
Point evaluation is surjective; its fiber is a singleton except when the
function restricts to a nonzero constant compact class on the unique cycle,
where the fiber is `K_1(D)`. This records Phillips's globally noncompact
circle-with-a-tail classes without overdecorating soft cyclic support. It also
proves that finite-pseudoforest formation preserves Cu-regularity for simple
stable-rank-one fibers, so every simple stably finite pure fiber gives a pure
Cu-regular field over every finite pseudoforest with arbitrary projections
and arbitrary `K_1`. That theorem is the one-cycle case of the cactus result below.


Articulation gluing now pushes the projectionful theorem past one cycle.
`stw99-lxxvi-cactus-enriched-cu-classification` proves a one-point wedge Cu
pullback theorem and therefore reduces every finite graph exactly to the
actual Cu semigroups of its 2-connected blocks. For a cactus those blocks are
only edges and circles, yielding a full enriched formula with one independent
`K_1(D)` label on each cyclic block where the pointwise function restricts to
a nonzero constant compact class. Thus finite-cactus formation preserves
Cu-regularity for simple stable-rank-one fibers, and simple stably finite pure
fibers give pure Cu-regular fields over cacti with arbitrarily many cycles,
arbitrary projections, and arbitrary `K_1`. The subsequent compact-core
theorem also handles 2-connected blocks of first Betti number at least two.


The full finite-graph corridor is now proved in
`stw99-lxxvi-finite-graph-compact-core-cu-regularity`, including theta graphs
and arbitrary multicycle blocks. For each pointwise Cu function, retain
the union of circles on which it is a nonzero constant compact value.
Brown--Ciuperca's spectral-gap theorem makes the restriction to every
connected component of this core an actual compact class. Outside that
core, finitely many small-spectrum cuts reduce comparison to a forest of
compact cores. The proof realizes the data using the published surjective
interval-pullback theorem, establishes set bijectivity first, and then uses
`(O5)` to recover compact-left order before reflecting arbitrary comparison.
It follows that any coefficient map between simple separable stably finite
stable-rank-one algebras which is an isomorphism on Cu and K1 induces a
Cu isomorphism over every finite graph. Compact restriction methods already
appear in Tikuisis's theorem for Z-stable ASH coefficients; this result
extends the coefficient scope and proves rigidity of the specified map.

There is now a broader one-dimensional-base theorem at the exact idealwise
`K_1`-free boundary.  For every second-countable locally compact Hausdorff
space `X` of dimension at most one,
`stw99-lxxvi-one-dimensional-formation-preserves-cu-regularity` proves that
`C_0(X,B)` is Cu-regular whenever both `B` and `B tensor Z` have stable rank
one and idealwise vanishing `K_1`, and the actual coefficient first-factor Cu
map is an isomorphism.  In particular, if `D` is simple, separable, stably
finite, pure, and `K_1(D)=0`, then `C_0(X,D)` is pure and Cu-regular.  This
permits noncompact bases, infinite branching, and infinitely many cycles.  The
proof uses the published pointwise Cu formula, not an unproved graph pullback
formula. For simple fibers the K1 restriction is now removed entirely by
`stw99-lxxvi-one-dimensional-simple-fiber-cu-regularity`: every simple
separable stably finite pure `D` gives a pure Cu-regular `C_0(X,D)` for
every second-countable locally compact Hausdorff `X` of dimension at most
one. Compact bases are inverse limits of finite graphs, and the actual
first-factor maps pass through the Cu inductive limit. Noncompact bases
follow from one-point compactification and ideal permanence. This proves
regularity, not an unrestricted pointwise `Lsc` formula.

Beyond dimension one,
`stw99-lxxvi-all-base-compact-rigidity-k-stability` identifies an exact
boundary: for a simple separable stably finite pure coefficient D,
first-factor V isomorphisms over all spheres are equivalent to those over
all compact metrizable bases, and to K-stability of every nonzero
projection corner of `D tensor K`. Zhang's theorem supplies this condition
when D has real rank zero, proving the whole compact wing in every base
dimension. A corner stabilization kernel or cokernel conversely supplies
a pure sphere-field counterexample to LXXVI. Consequently a positive
answer to LXXVI would imply the stronger K-stability part of STW LVIII
for unital separable simple pure algebras. The noncompact higher-dimensional
wing is not settled by this projection theorem.

For real-rank-zero simple stably finite pure fibers, the stronger theorem
`stw99-lxxvi-rr0-all-base-compact-left-reflection` now reflects every
compact-left comparison against an arbitrary positive target, again over
every compact metrizable base. Its finite-dimensional relative embedding
proof verifies all hypotheses of Michael's selection theorem using
uniform polar contractions; projection lifting and Cu continuity remove
the dimension bound from the compact-left conclusion. Full source
comparison and mixed target realization are supplied by the subsequent
theorems below.

The subsequent theorem `stw99-lxxvi-rr0-all-base-full-order-reflection`
settles the source-comparison part entirely: for these coefficients,
the actual first-factor Cu map is an order embedding over every
second-countable locally compact Hausdorff base, with no dimension
bound. Exact relative embeddings on the strict-comparison locus are
proved by compatible projection-frame towers and uniformly controlled
spectral tails. Closing the equality set of a source cutoff gives a
compact core on which the earlier projection theorem supplies boundary
data. The full realization theorem now supplies the complementary
surjectivity statement for this coefficient class.
The attached finite-patch reduction places every target cutoff below
a finite sum of localized target projections inside the same hereditary
algebra, and each individual localized projection has an exact source
lift. The full realization theorem now also lifts their overlapping
sum. The earlier two-patch audit
proves exact realization for nested supports when the orthogonal angle
remainder is soft or has a uniform angle spectral gap. A transverse
compression also handles certain nonnested supports with soft remainder.
These remain useful explicit special constructions; arbitrary mixed
angle remainders and general finite-patch classes are now covered by
full surjectivity. The small-angle audit identifies the earlier difficulty
sharply: every target positive in a constant source projection corner
is the angle remainder of two globally trivial projections, as close
in norm as desired. An explicit small unitary homotopy can erase its
entire Cu class. Increasing source-projection compressions exhaust
every target class, so arbitrary angle-remainder realization is
equivalent to full realization here. Projection-space homotopies
alone, or invertible angle padding, do not prove that realization;
the hereditary sandwich construction now supplies it.

The reviewed theorem `stw99-lxxvi-rr0-compact-summand-cancellation`
now proves `[p]+[a]<=[p]+[b]` implies `[a]<=[b]` for these
real-rank-zero coefficient fields over every second-countable locally
compact base. It applies to both source and target without assuming
stable rank one of the section algebra. Over compact metrizable bases,
the first-factor Cu image is also closed under removing compact
summands. Hence the universal Gram class `[G_t]=[P]+[a]` is in the
image exactly when `[a]` is. The
[cancellation proof](artifacts/stw99-lxxvi-rr0-compact-summand-cancellation-2026-09-05.md)
settles this algebraic step. The full theorem now realizes both the
arbitrary mixed Gram class and its angle remainder.

A mixed realization theorem is now proved in
`stw99-lxxvi-closed-compact-stratum-realization`. For a finite-dimensional
compact metric base, a target class lifts whenever its restriction to
a closed subset is compact and all fibers outside that subset are
soft or zero. The compact bundle need not extend over the whole base:
the [collar construction](artifacts/stw99-lxxvi-closed-compact-stratum-realization-2026-09-05.md)
attaches it to a source soft representative on shrinking neighborhoods,
proves the resulting source classes increase, and verifies that their
supremum maps to the target by relative cutoff comparison. Arbitrary
accumulating compact strata are handled by the stronger full realization
theorem stated above; the general STW LXXVI question remains open.

The intrinsic comparison theorem
`stw99-lxxvi-compact-equality-strata-determine-comparison` now identifies
the exact global order data for these real-rank-zero coefficient fields
over finite-dimensional second-countable locally compact bases. Fiberwise
comparison suffices precisely when the support bundles agree on every
compact subset of each equal nonzero compact-value stratum. Closing a
source cutoff's equality locus reduces the proof to finitely many
projection-bundle boundary frames and strict relative embedding elsewhere.
This is a comparison theorem for actual sections. The full realization
proof uses it twice to verify the two global inequalities of each
hereditary sandwich; neither inequality follows merely from fiber ranks.

Beyond real rank zero, the reviewed conditional theorem
`stw99-lxxvi-hereditary-k-stable-projection-extension` proves exact
strict relative projection-source embedding over finite-dimensional
compact bases when the simple finite stable-rank-one coefficient has
K-stable nonzero hereditary subalgebras throughout its stabilization.
Its proof uses the full hereditary complement as a unitary stabilizer
and does not need projection approximate units. The corresponding
positive-source extension, with parameterized control sufficient for
mixed target realization, remains unproved under this hypothesis.
The separate theorem
`stw99-lxxvi-exact-positive-cutoff-restriction-not-onto` identifies a
precise failed replacement for the projection tower: exact restriction
between arbitrary positive cutoff embedding spaces need not be onto,
even for CAR coefficients and strict comparison against a projection
target. The [shared reviewed proof](artifacts/stw99-lxxvi-hereditary-k-stability-and-cutoff-restriction-2026-09-05.md)
leaves approximate lifting open. Neither this obstruction nor the
conditional projection theorem changes the full RR0 result above or
settles general LXXVI.

## Literature boundary

There is now also a complete positive theorem with no base-dimension
restriction. `stw99-lxxvi-residually-stably-projectionless-cu-regularity`
proves that every separable pure algebra whose every quotient is stably
projectionless is Cu-regular. This includes `C0(X,D)` for every simple
separable stably projectionless pure D and every second-countable locally
compact Hausdorff X, including infinite-dimensional compact bases.
All classes on both sides are soft: quotient spectral gaps would produce
forbidden projections, and the simple-exact tensor-ideal theorem controls
every quotient after tensoring with Z. The actual soft isomorphism thus
covers the entire Cu semigroup. Projection-bearing quotients remain the
boundary of this argument.

The equivalence

```text
A pure  iff  Cu(A) ~= Cu(A) tensor_Cu Cu(Z)
```

is imported from Antoine--Perera--Robert--Thiel.  The nodes below do not
identify this abstract tensor product with `Cu(A tensor_min Z)`; treating that
identification as automatic would assume the problem.

## Attempts

The positive route is to prove that the external-product morphism `mu_A` in
`stw99-lxxvi-external-cu-tensor-map-is-the-only-gap` is invertible.  Abstract
`Cu(Z)`-absorption supplies invertibility of `eta_A`, not of `mu_A`; no step may
replace the latter by the former.  The route is stable under ordinary
inductive-limit assembly by
`stw99-lxxvi-cu-regularity-passes-to-inductive-limits`, so genuinely new work
is needed only for building blocks not already known to be Cu-regular.

The current counterexample route is compact cancellation.  Find a pure
non-simple algebra with two stably inequivalent projections of the same
`K_0` class, while projections cancel after tensoring with `Z`.
`stw99-lxxvi-compact-cancellation-counterexample-criterion` then proves that
`Cu(iota_A)` is not injective.  The cross-`K_1` mechanism that refutes the
stronger tensor assertion in Problem XCV does not directly apply here:
tensoring by `Z` does not provide a second nonzero `K_1` factor, so the
candidate obstruction must collapse existing Cu data rather than manufacture
the compact cross class used there.

The source and target of the first-factor map always have canonically
identical ideal lattices, K-theory, and quasitrace cones; see
`stw99-lxxvi-first-factor-map-has-identical-coarse-shadows`.  Hence neither a
coarse ideal/K-theoretic calculation nor equality of all ranks can by itself
prove Cu-regularity or exhibit a counterexample.

There is nevertheless an automatic comparison-theoretic density statement.
`stw99-lxxvi-first-factor-cu-image-is-order-cofinal` proves more generally
that every full star homomorphism has order-cofinal Cu image.  Hence each
way-below class in `Cu(A tensor_min B)` is dominated by a first-factor class
for every unital `B`, and every target class has one global first-factor
dominator.  For `B=Z`, that dominator can be chosen inside the target class's
ideal, and the global dominator generates exactly the same ideal.  This is
only cofinality from above: it does not put an image class inside a prescribed
target class or hereditary subalgebra.  Indeed, inner cofinality together
with order reflection would already force surjectivity.  Thus the remaining
LXXVI hinge is a hereditary sandwich/realization problem, not a lack of
sufficiently large or ideal-correct first-factor classes.

There is now a sharp exception to that warning on the soft part.
`stw99-lxxvi-first-factor-reflects-soft-comparisons` proves, for every
separable `A` with almost unperforated `Cu(A)`, that the first-factor map
reflects `x<=y` whenever the left-hand class `x` is functionally soft.  Thus
for pure `A` it order-embeds the soft subsemigroup. The stronger theorem
`stw99-lxxvi-first-factor-soft-cu-isomorphism` now also proves
surjectivity on the entire soft part for every separable pure A.
Antoine--Perera--Thiel canonically identify the soft part of a pure
Cu-semigroup with its realification, and Robert recovers realification
from the topological functional cone. The actual first-factor map
therefore becomes precomposition by a cone homeomorphism. Any remaining
defect involves nonsoft classes; globally noncompact classes can still
be nonsoft because they have compact images in proper quotients.

In the stably finite compact corridor, the `K_0` equality must hold in the
ideal generated by the two projections, not just in the ambient algebra.  The
ideal-local protection theorem `stw99-lxxvi-ideal-local-k0-protection` proves
that a nonzero local difference survives tensoring with Z when the stabilized
generated ideal is stably finite.  In particular, index-boundary
noncancellation from a Toeplitz-type compact ideal cannot work.  The pure
Z-stable algebra
`Toeplitz tensor Z` explicitly exhibits ambient `K_0` noncancellation of this
protected kind; see `stw99-lxxvi-toeplitz-z-pure-noncancellation`.
The remaining stably finite compact frontier is stated without hidden
cancellation assumptions in `stw99-lxxvi-ideal-local-collapse-witness`.
There is a separate possible infinite-projection corridor in
`stw99-lxxvi-infinite-projection-collapse-witness`.

The scalar `S^6` clutching route is now refuted, and the same obstruction
is excluded on spheres of every dimension. The theorem
`stw99-lxxvi-pure-coefficients-kill-scalar-unstable-homotopy` shows that
every stably trivial class from `pi_k(U(r))` dies after scalar extension to
a unital simple pure coefficient, before any Z tensoring. The missing
literature input was Rørdam--Winter's criterion: almost divisibility of
the compact unit and stable rank one give unital maps from every finite
prime dimension-drop block `Z_(n,n+1)`. Choosing `n` in the stable
unitary range makes endpoint evaluation injective on the relevant
homotopy group; the coprime endpoint multiplicities remove the intervening
obstruction. Injectivity or compatibility of the block maps is unnecessary.
Lin handles the finite simple branch, and K-stability handles the purely
infinite branch. A remaining higher-dimensional projection route must use
coefficient-dependent unstable classes in projection corners, not scalar
vector bundles. The
one-dimensional simple-fiber theorem now rules out every second-countable
locally compact base of dimension at most one, for arbitrary `K_1` and
arbitrary projections in a simple separable stably finite pure fiber.
The finite-graph compact-core classification records the supportwise
clutching missed by pointwise `Lsc` functions; graph approximation extends
the actual first-factor isomorphism to all the indicated bases. The
higher-dimensional non-RR0 coefficient corridor and general
nonsimple-coefficient problem remain open outside the classes proved above.
