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
One fixed `2 x 2` matrix corona contains every countable graph as the exact
commutation graph of a family of nonidentity involutions.
Quotienting by selected pair-support ideals realizes every graph completion
of that graph while preserving all vertex involutions.

### Hilbert-hotel consequences

The explicit simple Hilbert-hotel group generates Boolean restricted-sum
towers whose normal subgroups and quotients are all MF-invisible.  The
finitely presented Hilbert-hotel group generates free-product towers which,
after taking a direct product with any finitely presented MF group `Q`, give
infinitely many pairwise nonisomorphic finitely presented groups with the
same complete MF reflection `Q`, the same MF-target representation functor,
and the same compact and all-fields finite-dimensional visible quotient.

These results turn MF invisibility into a functorial localization calculus
and matrix-corona visibility into an exact ideal-valued geometry.

The zero class of the reflector is closed under quotients, extensions, and
countable colimits.  For a connected graph of full-radical vertex groups,
the exact MF reflection of its Bass--Serre fundamental group is the free
fundamental group of the underlying graph: tree gluings remain completely
invisible, and each graph cycle contributes exactly one visible free
generator.
