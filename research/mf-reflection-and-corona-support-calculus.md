---
rg: 2
id: mf-reflection-and-corona-support-calculus
kind: claim
title: MF reflection and matrix-corona support form a complete algebraic calculus
root: true
artifacts:
  - research/mf-reflection-and-corona-support-calculus-proof.md
  - notes/MF_REFLECTION_AND_CORONA_SUPPORT_CALCULUS.md
---

The operator-MF radical has two complementary exact structures.

### Reflection structure

Countable MF groups form an epireflective subcategory of countable groups,
with reflector

```text
R_MF(G)=G/Rad_MF(G).
```

Limits which remain countable are created in groups; colimits are computed
in groups and then reflected.  The morphisms inverted by `R_MF` form a
two-out-of-three, retract-closed, countable-colimit-stable localization
class.  The radical topology has `Rad_MF(G)` as the closure of the identity,
and MF relation closure is the corresponding Hausdorffization after imposing
relations.

### Corona support structure

Stable projections in a norm matrix corona are classified by eventual rank
germs.  Eventual rank domination classifies projection-generated ideals and
full corners, while support subsets modulo finite error embed the Boolean
algebra `P(N)/Fin` into the ideal lattice.

Every corona representation `rho:G->U(Q_d)` therefore carries the
conjugacy-invariant ideal-valued support

```text
Supp_rho(g)=Ideal(rho(g)-1),
```

with subadditivity under products and a meet bound under commutators.  Corona
quotients turn this support filtration into exact group kernels.

Localized Pauli involutions make both inequalities sharp: multiplication
realizes union of coordinate supports and commutators realize intersection.

### Hilbert-hotel consequences

The explicit simple Hilbert-hotel group generates Boolean restricted-sum
towers whose normal subgroups and quotients are all MF-invisible.  The
finitely presented Hilbert-hotel group generates free-product towers which,
after taking a direct product with any finitely presented MF group `Q`, give
infinitely many pairwise nonisomorphic finitely presented groups with the
same complete MF reflection `Q`, the same MF-target representation functor,
and the same compact and all-fields finite-dimensional visible quotient.

One full-radical star kernel realizes every countable permutation action and
the full transformation monoid of a countable set.  Every noninjective factor
fold has kernel `F_infinity`, including a fold identifying just one pair.
For each generating set `X`, the single group `C_d(F_X)` compiles every
`X`-generated MF presentation: visible relators produce `C_d(Q)`, and one
fixed final relation produces `Q`.  Arbitrary amalgamated attachments of the
black-hole group compute semantic quotients by killing exactly the attached
subgroups.

The binary Leavitt unit group realizes the opposite phenomenon internally:
for every finite group `F`, one block-monomial subgroup `U wr F<=U` has MF
reflection exactly `F`, although the ambient simple group `U` has zero MF
reflection.  All these subgroups are finitely generated Kazhdan groups.  A
single ambient full-radical group therefore contains every finite MF
reflection, and the reflection functor loses maximal information under these
subgroup inclusions.

The same ambient group contains a finitely generated bilateral wreath
subgroup `U wr Z` whose MF reflection is infinite cyclic.  Its entire
semantic closure operator is principal at one base involution, so killing
one fixed word is equivalent to making any quotient MF.

Iterating that bilateral shift produces an internal tower whose MF
reflections are the iterated amenable wreath products
`F`, `F wr Z`, `(F wr Z) wr Z`, and so on.  The same ambient simple group
therefore contains one-word non-MF thickenings of visible groups with
unbounded derived length.

More generally, one wandering Leavitt corner compiles any countable actor
`Q<=U` into an internal group `U^(Q) semidirectProduct Q` whose MF reflection
and complete semantic-closure operator are exactly those of `Q`.  Finite
prefix ping-pong supplies every `F_r` as such an actor.  Hence the single
group `U` contains finitely generated non-MF subgroups with reflection `F_r`,
and their quotient lattices internalize the MF-closure problem for all
finite-generator presentations.
One group `U wr F_2` already contains all finite-rank free-reflection
subgroups and a strict descending chain of isomorphic copies induced by a
proper free self-embedding.
Finite-factor ping-pong further realizes every reflection
`F_r*G_1*...*G_k` with finite `G_i`, together with its complete lattice of
MF-closed normal subgroups.
The demonstrative-subgroup characterization upgrades this to every countable
virtually free `Q`, and proves that virtual freeness is exactly the
finitely-generated prefix-dynamical range of the wandering-corner compiler.
Equivalently, this range consists precisely of the groups with context-free
word problem.

These results turn MF invisibility into a functorial localization calculus
and matrix-corona visibility into an exact ideal-valued geometry.

The zero class of the reflector is closed under quotients, extensions, and
countable colimits.  Consequently these relation cells may be substituted
inside arbitrary countable presentation constructions without changing any
MF-visible consequence beyond the relations they are designed to impose.
