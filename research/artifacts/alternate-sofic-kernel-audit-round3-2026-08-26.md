# Alternate sofic Kazhdan-kernel audit, round three

Date: 2026-08-26

## Exact reduced input

Any witness to the torsion-free exact-radical-over-`Z` target supplies a
finitely generated subgroup `K` which is

```text
torsion-free, sofic, property (T), non-LEF,
and has no nontrivial finite quotient.                     (R3.1)
```

Finite presentation of the ambient mapping torus is equivalent to a finite
two-sided automorphic presentation of `K`.  Conversely, a `K` satisfying
`(R3.1)` and that presentation condition gives the target: Dadarlat--Ozawa--
Thom makes every homomorphism from `K` to an MF group trivial, so the mapping
torus has radical exactly `K` once its quotient is `Z`.

No currently published construction located in this audit supplies `(R3.1)`.
The point is not merely that the preferred finitely presented strengthening
is open.  Even the underlying sofic, non-LEF, no-finite-quotient Kazhdan seed
is absent from the available candidate families.

## Current primary-source check

### Alekseev--Thom, 2026

*Centralizers of sofic approximations of Kazhdan groups*,
arXiv:2608.05362, Theorem A, proves that a Kazhdan group with a sofic
embedding whose ultraproduct centralizer acts ergodically is LEF.  Therefore
every hypothetical sofic embedding of `(R3.1)` must have a nonergodic
centralizer.  In particular, a positive Titz--Witzel construction cannot be
an asymptotically homogeneous regular finite-quotient model.  This is a
necessary design constraint, not a construction.  The same paper's Open
Problem 6.1 still asks for a finitely presented sofic Kazhdan group which is
not residually finite and records no soficity theorem for the Titz--Witzel
lattices.

URL: https://arxiv.org/abs/2608.05362

### Alekseev--Thom, 2025

*Remarks on approximability and stability for groups*, arXiv:2512.15494,
was rechecked because it treats Kazhdan normal subgroups and Rips
constructions.  Its quotient-soficity result is conditional on soficity of a
specific induced Bernoulli action.  The Belegradek--Osin Rips application
constructs hyperbolic groups with Kazhdan kernels, but supplies no soficity of
the ambient group or kernel.  Wise's residually finite Rips construction does
supply soficity, but then every subgroup kernel is residually finite and
cannot satisfy `(R3.1)`.  Hence the two Rips variants do not combine into the
requested seed.

URL: https://arxiv.org/abs/2512.15494

### Titz Mite--Witzel

No newer primary source proves soficity of the five torsion-free simple
Kazhdan lattices of arXiv:2509.05054.  Their current role is unchanged: each
already supplies finite presentation, torsion-freeness, property `(T)`, no
finite quotients, full MF radical, and one-element normal generation.  The
two-generator finite-permutation gate in Cairn is still their only missing
clause.

URL: https://arxiv.org/abs/2509.05054

## Published sofic non-LEF families excluded

### Kar--Nikolov cyclic amalgams

Kar--Nikolov, arXiv:1405.1620, construct

```text
SL_n(Z[1/p]) *_Z SL_n(Z[1/p]),
```

which is finitely presented and sofic but non-LEA.  It does contain Kazhdan
vertex groups.  However, any normal Kazhdan subgroup fixes the Bass--Serre
tree by property `FA`; normality and minimality make it fix the whole tree,
so it lies in the cyclic edge group and is trivial.  The theorem is recorded
in `normal-kazhdan-kernel-cannot-live-in-amenable-edge-tree`.  It also kills
all torsion-free congruence-subgroup replacements and, more generally, every
nontrivial minimal amalgam/HNN construction over amenable edges.

URL: https://arxiv.org/abs/1405.1620

### Cornulier's locally-RF-by-abelian group

Cornulier, arXiv:0906.3374, constructs a finitely presented sofic non-LEA
group with a locally residually finite normal subgroup and abelian quotient.
Every Kazhdan subgroup of any locally-RF-by-amenable group is residually
finite: its amenable image is finite, so a finite-index subgroup lies in the
locally RF kernel.  This is incompatible with `(R3.1)`.  See
`locally-rf-by-amenable-cannot-supply-exact-kazhdan-kernel`.

URL: https://arxiv.org/abs/0906.3374

### Thom/de Cornulier Kazhdan groups

Thom's characteristic-`p` non-Hopfian Kazhdan group is LEF and has torsion.
Its characteristic-zero Kida--Thom analogue is torsion-free and LEF, but its
nontrivial residually finite quotient forces every mapping-torus MF radical
into the proper central tail, as already proved in Cairn.  De Cornulier's
finitely presented non-Hopfian Kazhdan groups and Thom's related quotient are
hyperlinear but not known sofic; their standard characteristic-`p` forms
also contain torsion.  No alternate automorphism fixes these finite-residual
obstructions.

URLs:

* https://arxiv.org/abs/0810.2180
* https://arxiv.org/abs/math/0502140

## Other envelope candidates

* The Elek--Szabo simple sofic envelope has no finite quotients, but the
  available witness contains an involution and the construction does not
  preserve property `(T)`, finite generation, or finite automorphic
  presentability.
* A co-amenable simple envelope does not solve this: co-amenability of a
  Kazhdan subgroup does not promote property `(T)` to the overgroup, as
  `H<=H x Z` already shows.
* The literal exact MF radical cannot hide the desired kernel.  Cairn now
  computes it inside a central amalgam of finite Clifford blocks; its
  Bass--Serre action forces every property-`(T)` subgroup to be finite, and a
  torsion-free one to be trivial.
* Rover--Nekrashevych and topological-full-group simple envelopes retain
  torsion and, in the audited cases, have independent fences against an
  infinite Kazhdan subgroup.
* The Fournier--Facio torsion-free finitely presented group is nonsofic, so
  neither it nor the routed nonsofic quotient can be an ambient witness.

## Surviving work

The alternate-kernel sweep leaves two honest interfaces:

1. construct a new torsion-free sofic non-LEF Kazhdan group with no finite
   quotients and a finite automorphic presentation; or
2. solve the explicit Titz--Witzel permutation gate already reduced in Cairn
   to one exact involution, one arbitrary permutation, four approximate
   relators, and the separated word `u^8`.

The first formulation is not presently easier than the second.  All standard
sofic permanence mechanisms checked here either make the Kazhdan subgroup
residually finite, destroy property `(T)` through a nontrivial tree action,
or introduce torsion.
