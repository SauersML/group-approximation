---
rg: 2
id: thompson-products-have-vanishing-zg-cohomology-proof
kind: route
title: "Künneth for finite-type cochain complexes: H^*(F; ZF) = 0 forces H^*(F x H; Z[F x H]) = 0"
target: thompson-products-have-vanishing-zg-cohomology
requires:
  - thompson-f-has-vanishing-zg-cohomology
---

Write `G = F`. By `thompson-f-has-vanishing-zg-cohomology` there is a free
resolution `P -> Z` over `ZG` with `P_p ≅ (ZG)^{a_p}` finite, and
`H^*(Hom_G(P, ZG)) = 0`. Let `Q -> Z` be a free resolution over `ZH` with
`Q_q ≅ (ZH)^{b_q}` finite.

**The product resolution.** `P ⊗_Z Q` is a complex of free `Z[G × H]`-modules, with
`(P ⊗ Q)_n = ⊕_{p+q=n} P_p ⊗ Q_q ≅ Z[G × H]^{Σ a_p b_q}`, finite in each degree. Its
homology is `Z` in degree 0 and zero elsewhere: `P` and `Q` are complexes of free
abelian groups with homology `Z` concentrated in degree 0, and the Künneth formula
gives `H_*(P ⊗ Q) ≅ H_*(P) ⊗ H_*(Q) = Z` in degree 0, since the Tor terms vanish
(`Z` is free). So `P ⊗ Q -> Z` is a finite-type free resolution over `Z[G × H]`.

**The cochain complex splits.** For finitely generated free modules,

```text
Hom_{G×H}((ZG)^a ⊗ (ZH)^b, Z[G×H]) ≅ Z[G×H]^{ab} ≅ (ZG)^a ⊗_Z (ZH)^b
                                   ≅ Hom_G((ZG)^a, ZG) ⊗_Z Hom_H((ZH)^b, ZH),
```

naturally in maps between such modules, using `Z[G × H] ≅ ZG ⊗_Z ZH`. Hence, with
the usual signs,

```text
Hom_{G×H}(P ⊗ Q, Z[G×H]) ≅ Hom_G(P, ZG) ⊗_Z Hom_H(Q, ZH)
```

as cochain complexes. Both factors are complexes of free abelian groups.

**Künneth.** For a tensor product of cochain complexes of free abelian groups,

```text
H^n(C ⊗ D) ≅ ⊕_{p+q=n} H^p(C) ⊗ H^q(D)  ⊕  ⊕_{p+q=n+1} Tor(H^p(C), H^q(D)).
```

With `C = Hom_G(P, ZG)`, every `H^p(C)` is zero, so every term vanishes and
`H^n(G × H; Z[G × H]) = 0` for all `n`. Taking `H = Z` (resolution
`0 -> Z[Z] -> Z[Z] -> Z`) and `H = F` gives the two products. ∎
