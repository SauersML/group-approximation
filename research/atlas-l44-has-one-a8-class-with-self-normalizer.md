---
rg: 2
id: atlas-l44-has-one-a8-class-with-self-normalizer
kind: claim
title: L4(4) has one A8 class, its normalizer is A8, and both marking parities are unabsorbed
artifacts:
  - experiments/atlas_l44_a8_classification.py
  - experiments/atlas-l44-a8-classification.json
  - research/artifacts/atlas-l44-a8-classification-2026-08-23.md
distinct_from:
  atlas-six-relator-l44-subfield-has-no-marked-pair: that screens the standard subfield chart in two parities; this proves every abstract A8 subgroup and marking in L4(4) is represented there.
  atlas-a8-index-44551-to-48960-reaches-l44: that exhibits one subfield A8 and classifies the ambient simple-order interval; this classifies all A8 embeddings inside the endpoint.
  atlas-l44-subfield-packet-collision-exclusion: that runs the stronger packet/collision screen on one displayed chart; this is the missing embedding and normalizer classification making that chart exhaustive.
---

**ESTABLISHED.**  Put

```text
G=L4(4)=SL4(4),       H=GL4(2)~=A8.                    (L44A8-1)
```

There is exactly one `G`-conjugacy class of subgroups isomorphic to `A8`.
For its standard representative,

```text
C_G(H)=1,             N_G(H)=H,                        (L44A8-2)
|H^G|=48960.                                             (L44A8-3)
```

Moreover `Aut(A8)/Inn(A8)=C2`, and the nontrivial marking is not induced by
the normalizer.  Hence ordered marked pairs have exactly the two relative
marking parities already called `inner` and `graph` in the existing screens.

The classification is representation-theoretic and finite.  Since
`gcd(4,4-1)=1`, `PSL4(4)=SL4(4)`, so any `A8<G` is a faithful four-dimensional
module over `F4`.  The exact GAP/CTblLib 2-Brauer degrees are

```text
1,4,4,6,14,20,20,64.                                  (L44A8-4)
```

If the module were reducible, its four-dimensional semisimplification would
either contain one of the degree-four simples or have only trivial factors.
The first case is already irreducible by dimension; in the second the image
preserves a full trivial filtration and is a 2-group, impossible for the
faithful image of simple `A8`.  Thus the module is absolutely irreducible and
has one of the two degree-four Brauer characters.  GAP verifies that those
characters are dual.  They are the scalar extensions of the natural
`GL4(2)` module and its contragredient.  Their subgroup images coincide,
because `g -> (g^-1)^T` permutes the set `GL4(2)`.  Brauer--Nesbitt and finite
field descent therefore conjugate every `A8` to `H` in `GL4(4)`, hence in
`PGL4(4)=PSL4(4)`.

Finally the exact 85-point GAP calculation gives `(L44A8-2)`.  It also
follows conceptually: `N_G(H)/H` embeds in `Out(A8)=C2`, while an element
inducing the outer automorphism would identify the natural module with its
nonisomorphic dual.  Thus no outer element normalizes `H`, leaving precisely
two unabsorbed relative markings.

