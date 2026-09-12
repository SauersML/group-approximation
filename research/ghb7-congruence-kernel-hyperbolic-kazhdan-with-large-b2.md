---
rg: 2
id: ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2
kind: claim
title: The kernel of CCKW's SL_4(F_7) quotient of GHB_2(7) is a torsion-free hyperbolic Kazhdan group with b_2 at least 1380
distinct_from:
  density-random-group-hyperbolic-kazhdan-with-positive-b2: that gives hyperbolic Kazhdan groups with b_2 >= 1 with high probability in the density model, with no certified presentation; this names one explicit finitely presented member, the torsion-free kernel of an explicit finite quotient of GHB_2(7), with b_2 >= 1380
  kazhdan-hyperbolic-b2-group-flexibly-hs-stable: that is the open premise that some such group is flexibly HS stable; this only certifies an explicit group in the premise's class, with no stability content
  cckw-ghb2-kms-group-structure: that imports CCKW's structure theorems for GHB_2(7) itself, which has b_2 = 0; this passes to the vertex-injective kernel and computes its Euler characteristic and second Betti number
artifacts:
  - research/artifacts/ghb7-kernel-certified-candidate-2026-09-12.md
---

**ESTABLISHED.** Let `G = G_{HB_2}(7)` and let
`ψ : G → SL_4(F_7)` be `a ↦ I + E_03 + E_12`, `b ↦ I + E_10 − E_23`, `c ↦ I + E_31`.
Put `H = Ker(ψ)`. Then:

- `H` is a finite-index, torsion-free, word-hyperbolic subgroup of `G` with property (T);
- `H` acts freely and cocompactly on the CAT(−1) 2-complex `Y` of `G`, so `H\Y` is a
  finite aspherical 2-dimensional `K(H,1)`;
- `χ(H) = [G:H]·1381/2401`, with `2401 | [G:H]`;
- `b_1(H;Q) = 0` and `b_2(H;Q) = [G:H]·1381/2401 − 1 >= 1380`.

So `H` is an explicit group in the candidate class of
`kazhdan-hyperbolic-b2-group-flexibly-hs-stable`. Earlier, only density-model groups,
with no certified presentation, were known to be in that class.

`G` itself has `b_2(G;Q) = 0`: it acts properly on the contractible `Y`, with quotient
a single triangle.

The number `1381/2401` is the orbifold Euler characteristic
`1/343 + 1/2401 + 1/2401 − 3/7 + 1` of the triangle of groups.

DERIVATION
ghb7-congruence-kernel-b2-euler-count-proof
