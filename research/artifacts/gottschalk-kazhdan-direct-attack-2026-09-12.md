# Gottschalk on a simple Kazhdan host: reduction and a direct measure attack

Lane `gk-other-hosts` (merged from `gk-fixed-host`), 2026-09-12. Two things:
a reduction of Gottschalk's conjecture to finitely generated simple groups, and
a direct measure-theoretic attack on a simple Kazhdan host such as the binary
Leavitt unit group `U = L_{F_2}(1,2)^x`, with an exact account of what property
(T), spectral gap, strong ergodicity and the absence of finite quotients do and
do not give.

Supports `finitely-generated-simple-groups-are-surjunctive`,
`gottschalk-via-finitely-generated-simple-groups`,
`injective-measure-preserving-ca-is-surjective` and
`injective-cas-over-leavitt-units-preserve-uniform-bernoulli`.

Conventions: a cellular automaton over `G` with finite alphabet `A` has finite
memory `M` and rule `mu: A^M -> A`, `tau(x)(g) = mu((x(gm))_{m in M})`, and
commutes with the left shift. `mu_A` is the uniform Bernoulli measure on `A^G`
(product of the uniform measure on `A`); it has full support.

## 1. Reduction to finitely generated simple groups

**Localization.** Let `tau` be an injective cellular automaton over `G` with
memory `M`, and `H = <M>`. The restriction `tau_H` (same memory and rule) is an
automaton over `H`, and `tau = (tau_H)^G` is its coset-wise extension to `G`
(the rule reads only `M <= H`, so on each left coset `gH` it acts as a copy of
`tau_H` transported by `h -> gh`). Coset independence gives: `tau` is injective
iff `tau_H` is, and `tau` is surjective iff `tau_H` is. So a counterexample over
`G` restricts to a counterexample over the finitely generated `H`.

**Embedding.** Every countable group embeds in a two-generator simple group
(`countable-group-embeds-in-two-generator-simple-group`). Embed `H <= S` with
`S` finitely generated and simple. By `surjunctivity-passes-to-subgroups`
(overgroup form), if `H` is not surjunctive then `S` is not surjunctive.

**Conclusion.** If every finitely generated simple group is surjunctive, then
every group is surjunctive: given `tau` injective over `G`, localize to `H`,
embed `H <= S`; `S` surjunctive makes `tau_H` surjective, hence `tau`
surjective. The converse is trivial. So Gottschalk's conjecture holds for all
groups if and only if it holds for all finitely generated simple groups.

This is different from, and complementary to, the fixed two-generator tester
`gottschalk-surjunctivity-fixed-two-generator-tester`: that reduces to one
finitely presented host, which is not simple; this reduces to the class of
finitely generated simple groups. Simplicity is what the direct attacks below
use: a simple group has no proper normal subgroup and no proper finite-index
subgroup, so no quotient or finite-approximation structure to peel.

## 2. The measure-preservation endpoint

**Lemma (measure-preserving injective automata are surjective).** Let `G` be any
countable group, `A` a finite alphabet, `mu_A` the uniform Bernoulli measure. If
an injective cellular automaton `tau: A^G -> A^G` preserves `mu_A`
(`tau_* mu_A = mu_A`), then `tau` is surjective.

*Proof.* `A^G` is compact and `tau` continuous, so the image `Y = tau(A^G)` is
closed. `tau^{-1} Y = A^G`, so `mu_A(Y) = tau_* mu_A(Y) = mu_A(A^G) = 1`. The
complement `A^G \ Y` is open and `mu_A`-null; since `mu_A` has full support, a
nonempty open set has positive measure, so `A^G \ Y` is empty and `Y = A^G`. QED

**Consequence.** For any group, surjunctivity follows once every injective
cellular automaton preserves the uniform Bernoulli measure. Conversely a strict
(injective non-surjective) automaton has image a proper closed set, of measure
`< 1` by full support, so it does not preserve `mu_A`. Hence:

    G surjunctive   <==   every injective automaton over G preserves mu_A,

and a strict automaton is exactly a measure-distorting injective automaton. The
positive question over a fixed group is precisely whether injectivity forces
measure preservation.

This is the elementary, qualitative form of the Rokhlin-entropy route: the
Rokhlin lane measures the defect quantitatively
(`strict-automaton-lowers-bernoulli-rokhlin-entropy`,
`bernoulli-rokhlin-entropy-maximal-for-every-group`); the lemma above only needs
full support and a closed image, and isolates the single fact a positive proof
must supply -- measure preservation.

## 3. What the Kazhdan tools give, and do not give

Take `U = L_{F_2}(1,2)^x`: finitely presented, simple, property (T) (hence
property FA, `leavitt-unit-group-is-simple-fa-nonsofic`), and nonsofic. It is
the natural simple Kazhdan host.

- **Absence of finite quotients / residual finiteness.** `U` is infinite simple,
  so it has no proper finite quotient and is not residually finite. The route
  "residually finite implies sofic implies surjunctive" is empty here. Absence of
  finite quotients gives no surjunctivity directly: surjunctivity is not known to
  follow from any quotient property for simple groups, and permanence from sofic
  groups provably misses `U` (`leavitt-tower-outside-sofic-permanence-closure`).

- **Property (T) and spectral gap.** (T) makes the Bernoulli action
  `U ↷ (A^U, mu_A)` strongly ergodic (spectral gap in the Koopman
  representation). By Section 2 the positive question is whether an injective
  automaton preserves `mu_A`. Spectral gap is a property of the
  measure-preserving Bernoulli dynamics and of unitary representations; it is
  invariant under measure isomorphism. It therefore cannot, by itself, detect the
  topological non-surjectivity of a measure-distorting injective automaton: the
  automaton that would be a counterexample does not preserve `mu_A` and so is not
  a measure-preserving transformation to which spectral gap applies. Spectral gap
  is useful here only if it is used to prove that an injective automaton must
  preserve `mu_A` (equivalently, must have maximal Bernoulli Rokhlin entropy).
  That is exactly the open claim `injective-cas-over-leavitt-units-preserve-uniform-bernoulli`.

- **Strong ergodicity.** Same limitation, sharper. Strong ergodicity concerns
  asymptotically invariant sequences of measurable sets; it says nothing about the
  existence of a shift-equivariant continuous injection with proper closed image.
  A proper closed invariant subshift can have any measure in `[0,1)`; strong
  ergodicity does not exclude an equivariant injection onto one.

**Net.** For a simple Kazhdan host the three tools do not, on their own, prove
surjunctivity. They all funnel into one target: injectivity forces preservation
of the uniform Bernoulli measure. That target is what (T) or Rokhlin entropy
must be made to deliver, and it is open. Combined with the earlier no-go's --
counting is dead (full sofic radical,
`sofic-radical-localizes-garden-of-eden-windows`), Cantor-orbit encodings are
dead (`full-shift-maps-to-infinite-stabilizer-coset-shifts-are-constant`), and
coset peeling is circular (`thompson-v-coset-stabilizers-contain-copies-of-v`)
-- the surviving positive route over `U` is internal and measure-theoretic:
prove that an injective automaton over `U` preserves `mu_A`.
