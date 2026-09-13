---
rg: 2
id: flexible-hs-stability-descends-to-retracts-finite-index
kind: claim
title: Flexible HS stability descends to retracts, and from a Kazhdan group to its finite-index subgroups
distinct_from:
  hs-stability-descends-to-retracts: that is the strict same-dimension statement for finitely presented retracts; this is the flexible statement, needing only finite generation, together with descent to finite-index subgroups of Kazhdan groups.
  flexible-hs-stability-passes-to-kazhdan-kernel-quotients: that passes flexible stability to quotients by Kazhdan normal subgroups; this passes it to retracts and to finite-index subgroups.
---

**ESTABLISHED (unreviewed).** Flexible HS-stability is Dogon's Definition 1.2 (normalized
Hilbert--Schmidt, `D_n >= d_n`, `D_n/d_n -> 1`).

1. **Retracts.** Let `H` and `L` be finitely generated, with homomorphisms `i : H -> L` and
   `r : L -> H` such that `r∘i = id_H`. If `L` is flexibly HS-stable, so is `H`.
2. **Finite index.** Let `Γ` be a Kazhdan group and `H <= Γ` a subgroup of finite index. If `Γ`
   is flexibly HS-stable, so is `H`.

**Contrapositives used in the graph.** A non-roundable asymptotic representation of a retract,
or of a finite-index subgroup of a Kazhdan group, yields one of the ambient group. For example,
instability of a congruence subgroup of `SL_3(F_q[t])` gives instability of `SL_3(F_q[t])`, and
through the retract `x_1 -> t`, `x_j -> 0` also of `EL_3(F_q[x_1..x_d])`.

Derivation: `flexible-hs-stability-descends-to-retracts-finite-index-proof`.
