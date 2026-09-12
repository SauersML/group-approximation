---
rg: 2
id: dyadic-perturbation-group-is-sofic
kind: claim
title: The dyadic finite-perturbation group is sofic
distinct_from:
  sofic-set-action-finitary-extension-is-sofic: that derives soficity of a finitary-symmetric extension from soficity of the underlying set action, a hypothesis not verified for this action; this proves soficity of one explicit such extension from local residual finiteness and explicit cyclic-interval models.
  dyadic-finite-perturbation-group-elementary-structure: that is the group and its elementary properties; this is the approximation statement.
  affine-perfect-lamp-wreath-has-locally-finite-mf-radical: that gets soficity from a finite-index orbit structure inside an ordinary wreath product; this has no finite index and no lamp group, and uses finite orbits of the dyadic translation subgroups.
artifacts:
  - research/artifacts/dyadic-finite-perturbation-sofic-non-mf-2026-09-08.md
---

**ESTABLISHED.**  The group `G = Sym_fin(X) x| H` of
`dyadic-finite-perturbation-group-elementary-structure` is sofic, and
hence hyperlinear.

Write

```text
N = D^3 x| SL_3(Z),    N_j = 2^-j Z^3 x| SL_3(Z)  (j >= 0),
R = Sym_fin(X) x| N,   so   G = R x| <a>.                         (SF1)
```

The two steps are:

1. `R` is **locally residually finite** — every finitely generated
   subgroup is residually finite — because every `N_j`-orbit in `X` is
   finite;
2. `R x|_alpha Z` is sofic for any locally residually finite `R`, by
   explicit permutation models on `(Z/MZ) x Q`.

Step 1 is not residual finiteness of `Sym_fin(X) x| N_j`: finitary
permutations mix different `N_j`-orbits, so restriction to one orbit is
not a homomorphism on that group.  Step 2 is proved directly rather than
by quoting a general extension theorem.

DERIVATION
dyadic-perturbation-soficity-proof
