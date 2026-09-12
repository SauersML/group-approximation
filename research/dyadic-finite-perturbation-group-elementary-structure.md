---
rg: 2
id: dyadic-finite-perturbation-group-elementary-structure
kind: claim
title: Finite perturbations of the dyadic affine coset action form a finitely generated group with no finite normal subgroup
distinct_from:
  affine-perfect-lamp-wreath-has-locally-finite-mf-radical: that is an ordinary permutational wreath product with lamp group A_5 over the level-three affine congruence base; this group is defined with no lamp group at all, as the finite perturbations of one affine action, and its finitary kernel is the full finitary symmetric group.
  sofic-set-action-finitary-extension-is-sofic: that is a general permanence theorem about the finitary-symmetric extension of any sofic set action; this is the elementary structure of one explicit such extension, including finite generation and the absence of finite normal subgroups, which the general theorem does not address.
  affine-congruence-source-is-kazhdan: that is the arithmetic property-(T) source with a proper self-embedding; this is the ambient permutation group built over a larger dyadic affine action.
artifacts:
  - research/artifacts/dyadic-finite-perturbation-sofic-non-mf-2026-09-08.md
---

**ESTABLISHED.**  Let `D = Z[1/2]` and

```text
X = { v + 2^k Z^3 : v in D^3, k in Z },                           (DP1)
H = D^3 x| (SL_3(Z) x Z),
(b,A,m)(v + 2^k Z^3) = b + 2^m A v + 2^(k+m) Z^3.
```

Let `G` be the group of **all** permutations of `X` that agree, outside a
finite subset, with one of these affine maps.  Then:

1. the action of `H` on `X` is transitive and faithful modulo finitely
   supported permutations, so

```text
G = Sym_fin(X) x| H;                                              (DP2)
```
2. `G` is finitely generated;
3. `H` embeds in `GL_4(D)` and is residually finite;
4. conjugation preserves parity, so

```text
G / Alt_fin(X) = C_2 x H,                                         (DP3)
```
   a residually finite group;
5. `G` has **no** nontrivial finite normal subgroup.

The definition in the first sentence is intrinsic: no lamp group, no
wreath product and no central extension enters it, and `(DP2)` is a
consequence rather than the definition.

DERIVATION
dyadic-finite-perturbation-structure-proof
