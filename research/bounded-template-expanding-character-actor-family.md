---
rg: 2
id: bounded-template-expanding-character-actor-family
kind: claim
title: Compile an unbounded expanding character actor with bounded occurrence templates
distinct_from:
  sampled-weyl-defect-controls-common-pvm-dirichlet-energy: that tries to recover all translations from sparse mixed X/Z tests; this removes the mixed table and asks for direct actor covariance.
---

OPEN.  Construct, for unbounded `n`, a bounded-template perfect-completeness
occurrence system containing:

1. one additive X table for `V_n=F_2^n`;
2. a bounded symmetric actor set `g_(1,n),...,g_(D,n)` whose dual Schreier
   graph on `V_n^*\{0}` has a uniform spectral gap;
3. actor occurrence unitaries satisfying, with a dimension-independent
   squared-HS modulus,

   ```text
   C_s U(a) C_s^* ~= U(g_(s,n)a)                              (BCA1)
   ```

   in the averaged all-label sense used in `(OPS1)`; and
4. one involution `Z_n` and one nonzero seed `a_(0,n)` with

   ```text
   [U(a_(0,n)),Z_n]=J.                                        (BCA2)
   ```

All sizes `n` must be realized by one finite presentation and one common
central mark `J`, with every local occurrence/covariance test a conjugate of
finitely many prototypes.  The incidence may not use equality fibers that
create the known balanced two-pair contour.

Together with
`one-pauli-seed-character-expansion`, this
is a complete capacity backend.  Candidate actors include bounded expanding
generators of `SL_n(2)` or a fixed property-`(T)` linear group acting through
finite quotients, but the latter must prevent the seed from remaining in one
fixed small quotient orbit.

## Attempts

- **One fixed finite quotient actor.**  It gives only a fixed capacity and
  can be spectator-amplified.
- **A fixed linear group with all quotient modules.**  Small evaluation
  quotients may retain the seed on a bounded orbit; an unbounded family of
  seeded modules still has to be compiled.
- **Transport remote names by stabilizer words.**  This reintroduces
  path-length HS loss.  Covariance must be tested occurrence-by-occurrence.

## Infinite-orbit reformulation

The finite levels are not logically essential.  By
`infinite-character-actor-kills-fd-mark`, it is enough to construct one
finitely presented semidirect/module system with a fixed property-`(T)`
actor `A`, an elementary abelian occurrence module `M`, and a seed `m_0`
such that every character with `chi(m_0)=-1` has infinite `A`-orbit.  Exact
finite-dimensional representations then kill `J` because their joint
`M`-spectrum has finite support.  A dimension-independent same-basis
rounding theorem would upgrade this to the required normalized-HS collapse.

There is a canonical algebraic model.  For an infinite finitely generated
simple property-`(T)` group, the augmentation module

```text
I_A=ker(F_2[A]->F_2)
```

has no nonzero finite character orbit by
`simple-t-augmentation-module-is-aperiodic`.  It therefore removes the
all-`n`-after-`d` quantifier completely.

But the obvious group `I_A semidirect A` is not finitely presented:
`augmentation-actor-semidir-is-not-fp` identifies it as the index-two even
lamp subgroup of `C_2 wr A`.  This gives a new exact formulation of the
groupification gate.  One must compress the regular lamp commutators by an
oligomorphic/self-similar addresser while retaining the aperiodic
property-`(T)` action on the character spectrum.  After that algebraic step,
one still needs finite-stage same-basis rounding; a diffuse invariant
spectral measure in the exact infinite witness shows why an ultraproduct
argument alone cannot supply it.

There is now a concrete conditional way around the regular-wreath failure.
`sharp-two-t-actor-gives-fp-host` proves that a finitely presented simple
property-`(T)` sharply two-transitive actor with finitely generated point
stabilizer makes the augmentation lamp extension finitely presented: the
diagonal action has only two pair orbits, so the generalized wreath-product
criterion applies.  The seed `delta_x+delta_y` is cyclic, its visible
characters all have infinite uniformly expanding orbits, and one D8
amalgam keeps `J` nontrivial while every exact matrix representation kills
it.

André--Guirardel provide a two-generated simple property-`(T)` sharply
two-transitive actor.  `andre-guirardel-sharp-t-actor-audit` records the
precise near miss: their theorem does not give finite presentation or a
finitely generated point stabilizer.  Consequently the terminal gate has
split into two auditable statements:

1. obtain the finite-presentation hypotheses in this sharp-two actor class
   (or finitely present the augmentation extension by another mechanism);
2. prove global finite-stage same-basis rounding for its elementary abelian
   occurrence module.
