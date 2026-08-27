# The finite-building quotient does not remember the arithmetic labels

## Scope

Put

```text
G = SL_3(Q_2),   K = SL_3(Z_2),
A = SL_3(Z[1/2]),   C = SL_3(Z).
```

The type-zero vertex orbit of the affine Bruhat--Tits building is
`X=G/K`, and density plus `A intersect K=C` identifies the transitive
`A`-set `A/C` with `X`.  This note audits the tempting construction of
sofic models for this action from finite quotients of the building.

The conclusion is deliberately limited: ordinary finite building
quotients, including large-injectivity-radius or random-lift quotients, do
not by themselves carry the **labelled** `A`-action.  This neither proves
nor refutes soficity of `A action A/C`.

## Exact descent criterion

Let `Gamma<G` be a torsion-free uniform lattice, so it acts freely on the
building, and let

```text
q : X -> Y=Gamma\X
```

be the quotient covering.  For `a in G`, consider the building
automorphism `L_a:x |-> ax`.

**Lemma.**  `L_a` descends through `q` to an automorphism of `Y` if and
only if

```text
a Gamma a^(-1) = Gamma.                                  (BQ1)
```

Indeed, an automorphism of the simply connected cover descends precisely
when it conjugates the deck group to itself.  Directly, `(BQ1)` makes
`Gamma x |-> Gamma ax` well defined.  Conversely, if `L_a` descends, then
`L_a gamma L_a^(-1)` is a deck transformation for every `gamma in Gamma`,
giving one inclusion; applying the same argument to `a^(-1)` gives equality.

Thus a finite quotient of the *unlabelled* building supplies the finite
incidence geometry but not the permutations attached to the fixed
arithmetic generators.  The obstruction is not repaired by increasing
injectivity radius.

## Why a Hecke adjacency is not the missing generator

The `G`-invariant Hecke relation attached to `KaK` joins

```text
gK  to  gaK.
```

It records relative position in the building.  The arithmetic generator
`a`, however, acts by

```text
gK  |->  agK,
```

whose displacement in the frame based at `gK` is `g^(-1)ag`.  Hence one
fixed double coset `KaK` does not encode the left action of the fixed
element `a` away from the base vertex.  Passing to a finite quotient turns
relative positions into finite Hecke correspondences, but does not choose
globally framed generator labels.

This is the same distinction as that between Benjamini--Schramm convergence
of unlabelled complexes and local convergence of labelled Schreier graphs.
The latter is what a GKEP sofic-action model needs.

## The precise remaining construction

What would suffice is a sequence of finite building quotients (or random
lifts) equipped with **coherent deck-cocycle rounding**.  For every finite
word window `W subset A` and finite vertex window `E subset X`, one needs:

1. permutations `sigma_a` of the finite vertex set for `a in W`;
2. on a `1-o(1)` fraction of base vertices, injective framed copies of `E`;
3. covariance of those frames under `sigma_a` whenever `x,ax in E`;
4. `sigma_a sigma_b=sigma_(ab)` off an `o(1)` set for every tested product.

Conditions 2--4 are a simultaneous choice of gauges for the local lifts.
They immediately give the finite orbit charts in the definition of a
sofic action.  Large injectivity radius supplies only condition 2 after
forgetting labels.  Randomly or independently choosing representatives for
the individual Hecke correspondences supplies no reason for condition 4;
the defect is holonomy around word cycles.

The resulting terminal is therefore not another expansion or local-
geometry assertion.  It is a coherent simultaneous permutation-rounding
statement for the deck cocycles of the fixed dense arithmetic subgroup.

## Literature boundary

Bowen--Burton, *Locally compact sofic groups*, arXiv:2106.09118, proves
that an lcsc group admitting a sofic lattice is locally compact sofic.
Their approximating local `G`-spaces model the regular local geometry of
`G`; the theorem does not state that quotienting by a compact open subgroup
produces GKEP models for the action of a fixed dense subgroup on `G/K`.
The descent calculation above identifies the extra datum that such a
quotient argument would require.

Finite Ramanujan-complex and Cartwright--Steger constructions likewise
provide finite quotients of affine buildings and excellent local geometry.
Those results are not labelled-action theorems for this particular dense
subgroup.  In particular, the Lubotzky--Samuels--Vishne complexes of
arXiv:math/0406217 are constructed over positive-characteristic local
fields, so they cannot simply be cited as quotients of the `Q_2` building.

## Exact boundary

```text
finite quotient / random lift of the unlabelled building
    + coherent deck-cocycle rounding for the A-labels
        ==> soficity of A action A/C;

finite quotient / random lift alone
        =/=> any A-action model by the descent argument.
```

No sign of the action-soficity fork is claimed here.
