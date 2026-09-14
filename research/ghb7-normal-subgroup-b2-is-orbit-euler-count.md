---
rg: 2
id: ghb7-normal-subgroup-b2-is-orbit-euler-count
kind: claim
title: Every finite-index normal subgroup of GHB_2(7) has b_2 equal to its orbit Euler count minus one, and the index-7 kernel already has b_2 = 6
distinct_from:
  ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2: that computes b_2 for the torsion-free vertex-injective kernel of the SL_4(F_7) quotient, of index at least 2401; this gives the count for every finite-index normal subgroup, with torsion allowed, and exhibits index-7, 49 and 343 subgroups with b_2 = 6, 30 and 216
---

**ESTABLISHED.** Let `G = G_{HB_2}(7)` with vertex groups `X_0 = <a,b>`, `X_1 = <c,b>`,
`X_2 = <c,a>` and edge groups `<a>, <b>, <c>` (`cckw-ghb2-kms-group-structure`). Let
`φ : G → Q` be a homomorphism onto a finite group and `N = Ker φ`. Then `b_1(N;Q) = 0` and

```text
b_2(N;Q) = |Q| · ( 1 − Σ_{x∈{a,b,c}} 1/|φ(<x>)| + Σ_{i=0,1,2} 1/|φ(X_i)| ) − 1.
```

**Instances.** `G^ab = (Z/7)^3` with `a, b, c` a basis (the colimit of the vertex abelianizations,
`ghb7-triangle-vertex-groups-split-abelianizations`).

| quotient `φ` | `[G:N]` | `b_2(N;Q)` |
|---|---|---|
| `Z/7`, `a, b, c ↦ 1` | 7 | 6 |
| `(Z/7)^2`, `a ↦ e_1`, `b ↦ e_2`, `c ↦ e_1+e_2` | 49 | 30 |
| `(Z/7)^3`, the abelianization | 343 | 216 |
| any vertex-injective `φ` | `\|Q\|` | `\|Q\|·1381/2401 − 1` |

The last row is `ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`.

**Consequence.** `K_7 = Ker(G → Z/7, a,b,c ↦ 1)` is a finite-index Kazhdan subgroup with
`b_2(K_7;Q) = 6`. By the universal-coefficient argument in the Attempts of
`ghb7-finite-index-z-extension-center-survives`, it carries central `Z`-extensions with finite
abelianization. So the refutation premise can be tested at index 7, not only at the congruence
kernel of index `|Sp_4(F_7)|`.

DERIVATION
ghb7-normal-subgroup-b2-orbit-euler-proof
