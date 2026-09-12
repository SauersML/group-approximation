---
rg: 2
id: stw99-problem-xcv-pure-tensor-permanence
kind: claim
title: Minimal tensor products of pure C*-algebras are pure (STW Problem XCV, general part)
root: true
refuted_by:
  - pure-tensor-entangled-compact-counterexample
distinct_from:
  stw99-problem-xcv-cu-z-tensor: that prescribes the entire Cuntz semigroup of the tensor product and is refuted by a compact K-theory cross class; the counterexample tensor remains pure and therefore does not decide this weaker permanence question.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw95-pure-tensor-frontier-2026-08-30.md
  - research/artifacts/stw95-entangled-compact-corridor-audit-2026-08-30.md
  - research/artifacts/stw95-pure-tensor-permanence-wave-audit-2026-08-30.md
  - research/artifacts/stw95-order-reflecting-inner-cofinal-audit-2026-08-30.md
  - research/artifacts/stw95-nonunital-ash-unitization-audit-2026-08-30.md
  - research/artifacts/stw95-scattered-primitive-tensor-localization-audit-2026-08-30.md
  - research/artifacts/stw95-central-block-tensor-purity-audit-2026-08-30.md
  - research/artifacts/stw95-strongly-purely-infinite-cellular-tensor-audit-2026-08-30.md
---

**Problem XCV, general part, of Schafhauser--Tikuisis--White.**  Is the
minimal tensor product of pure C\*-algebras pure?

This remains open.  The counterexample to the first part does not refute it:
both the nuclear Z-stable tensor square and the concrete selfless free-group
tensor square used in `stw95-cu-z-tensor-counterexample` are pure.  Their
failure is finer—the tensor product has extra compact Cuntz classes—not a
failure of almost unperforation or almost divisibility.

## Attempts

The exact/selfless case is positive by tensor-product permanence of
selflessness.  The Z-stable case needs no nuclearity at all:
`stw95-one-zstable-factor-forces-pure-product` proves that if either factor
absorbs `Z`, then its tensor product with an arbitrary separable C*-algebra
again absorbs `Z` and is pure.  Thus both factors in a counterexample must be
non-Z-stable.  No construction is currently recorded that makes either
almost unperforation or almost divisibility fail after tensoring.

Central block assembly now gives a positive class even when both full
factors are nonexact and non-Z-stable.
`stw95-central-block-closure-of-tensor-pure-seeds` starts with one pure seed
`P` whose tensor square is pure, adjoins arbitrary Z-stable blocks, and takes
finite or countable `c_0`-sums.  Minimal tensor products distribute over the
central blocks, leaving only the seed square and products having a Z-stable
coordinate.  Taking `P=C*_r(F_2)` and adding a nonexact block `N tensor Z`
produces explicit nonsimple, nonexact, non-Z-stable pure factors with pure
tensor square.  The argument is entirely decomposable and does not address
indecomposable nonexact pairs.

The current positive and negative frontiers are now explicit.  A splitting
of the canonical abstract-to-concrete Cu tensor map suffices by
`split-cu-tensor-map-implies-pure-product`.  On the other hand, an entangled
compact-bearing irreducible representation would refute the claim through
`pure-tensor-entangled-compact-route`; spatial product representations are
ruled out, without irreducibility assumptions on the factor representations,
by `spatial-pure-factor-reps-have-no-joint-compacts`.  The compact corridor
is narrower still for simple factors:
`stw95-simple-pure-factors-exclude-compact-corridor` proves that at least
one factor would have to be nonsimple.  Moreover,
`separable-exact-nowhere-scattered-tensor-permanence` proves that a separable
compact-bearing witness would require both factors to be nonexact.  These are
fences around one counterexample mechanism, not a proof of tensor purity.

There are now two further positive reductions.  Tensoring a pure algebra with
an arbitrary AF algebra is pure, with no exactness assumption on the
other factor, because the
canonical abstract-to-concrete Cu tensor map is an isomorphism in this case.
For exact algebras with finite composition series, extension permanence
reduces the entire question to tensor products of the simple subquotients.

The finite-series restriction is now removed.
`stw95-purity-passes-to-sequential-inductive-limits` proves directly from
the Cu colimit axioms that purity survives arbitrary sequential inductive
limits.  Therefore
`stw95-transfinite-exact-filtration-reduction` extends
the reduction to continuous filtrations indexed by arbitrary ordinals for
separable filtered algebras: exactness handles successor extensions, Cu
continuity handles countable-cofinality limits, and separability forces the
filtration to stabilize at every uncountable-cofinality limit.  In particular,
for two separable exact algebras with arbitrary continuous composition
series, only the tensor products of their simple successor quotients remain
to be checked.

There is now a complementary filtration theorem that does not require the
other tensor factor to be exact.  By
`stw95-nuclear-successor-filtrations-need-no-exact-factor`, if the successor
quotients of a continuous filtration of separable `B` are nuclear and all
their tensor products with an arbitrary `A` are pure, then `A tensor_min B`
is pure.  Choi--Effros cpc splittings, rather than exactness of `A`, make the
tensor sequence exact at every successor stage.
In particular, a pure `A` tensored with any separable continuously
AF-layered `B` is pure: the AF-factor theorem verifies every local product.
This allows nonunital AF layers and makes no exactness, separability,
simplicity, or residual stable-finiteness assumption on `A`; the assembled
factor `B` need not itself be AF.

Seth--Vilalta's ASH tensor theorem discharges all of those local products in
a substantial nonsimple class.  The strengthened
`stw95-transfinite-ash-layered-factor-preserves-purity` says that if `A` is
pure and either is simple or has every quotient stably finite, then
`A tensor_min B` is pure whenever `B` is separable and has a continuous
arbitrary-ordinal filtration whose successor quotients are separable ASH
algebras, now without a unitality requirement.  The local step is
`stw95-nonunital-ash-factor-preserves-purity`: unitize an ASH factor, apply
Seth--Vilalta, and pass purity to the tensor ideal.  This uses no exactness of
`A`, because it needs only the ideal inclusion and not identification with a
tensor-quotient kernel.  No separability or exactness assumption remains on `A`.  In
particular this solves Problem XCV for such a pair when `B` is also pure,
without requiring `B` itself to be ASH or either factor to be Z-stable.

The filtration can now be recovered intrinsically from ideal topology.
`stw95-scattered-primitive-local-product-test` proves that if `B` is
separable with topologically scattered primitive spectrum, then
`A tensor_min B` is pure whenever this is true over every simple subquotient
of `B` and those subquotients are nuclear.  Successive isolated primitive
points produce the needed continuous ordinal filtration automatically.  In
particular, if `A` is pure and either simple or residually stably finite,
then it is enough that every simple subquotient of `B` be ASH.  When `B` is
also pure this is a positive Problem XCV class, even if the full extension
tower `B` is neither ASH nor known to be Z-stable.

There is also a purely infinite positive class, disjoint from the ASH
mechanism.  By
`stw95-strongly-purely-infinite-cellular-factor-preserves-purity`, let `A`
be separable, exact, and strongly purely infinite.  Then `A tensor_min B` is
strongly purely infinite, hence pure, for every separable `B`; exactness of
`B` is not required.  It is enough that `A` be exact and ordinarily purely
infinite with the ideal property, or with a compact-open basis in its
primitive spectrum.

The same theorem has a transfinite version: let `A` instead have a continuous
ordinal ideal filtration whose successor quotients are strongly purely
infinite, and now let `B` be separable and exact.
Kirchberg--Sierakowski make every cell product strongly purely infinite;
its Cu-semigroup is therefore an idempotent ideal lattice and hence pure.
The exact transfinite-filtration theorem then gives `A tensor_min B` pure.
Taking `B` to be the scalar algebra shows that the filtered algebra `A` was
already pure, so an exact pure `B` gives a genuine Problem XCV pair.  It is
enough for every cell to be ordinarily purely infinite with the ideal
property—or, equivalently in this separable purely infinite setting, to have
primitive spectrum with a basis of compact-open sets.  The cells need not be
simple, nuclear, Z-stable, ASH, or locally subhomogeneous, and the extensions
need not split.

The tensor-exactness asymmetry can also be reversed.  If every successor
cell is exact and strongly purely infinite and every successor quotient map
has a cpc section, then the other tensor factor may be arbitrary, including
nonexact.  Exact strong pure infiniteness makes every local product strongly
purely infinite, while
`stw95-semisplit-successor-filtration-reduction` shows directly that cpc
semisplitting is enough to preserve the successor kernels under arbitrary
minimal tensoring.  Thus a pure filtered factor of this kind tensors purely
with every separable pure algebra.

The two purity axioms require different Cu-map input.  Almost divisibility
already follows when the canonical Cu tensor image is internally cofinal for
way-below pairs; no splitting or order reflection is needed.  Almost
unperforation transfers along a much weaker ordered-monoid retraction, without
the continuity requirements of a Cu-morphism.  Their simultaneous
verification would strengthen the existing split-map route.

The apparent simultaneous local verification has a sharper—and limiting—
interpretation.  By
`stw95-order-embedded-inner-cofinal-cu-image-forces-pure-product`, if the
canonical external map is an order embedding and its image is inner cofinal
for way-below pairs, then a diagonal sequence of brackets lifts every
concrete class.  The map is therefore a Cu-isomorphism.  Thus inner
cofinality is genuinely weaker for transferring almost divisibility alone,
but once order reflection is added it does not bypass the external-map
isomorphism hinge.  Any nonsurjective route to simultaneous purity must use
a weaker local condition or transfer almost unperforation without order
reflection.

Finally, failure of tensor exactness gives a counterexample mechanism not
limited to compact-bearing representations.  For an ideal `I` in one pure
factor, a nonpure excess kernel

```text
ker(A tensor_min B -> (A/I) tensor_min B)/(I tensor_min B)
```

would be a nonpure ideal-subquotient of the tensor product and hence refute
permanence.  Such an excess vanishes when `B` is exact.  No pure pair with a
nonpure excess kernel is constructed here.
