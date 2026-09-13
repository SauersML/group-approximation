---
rg: 2
id: left-right-sofic-closed-under-co-amenable-overgroups-proof
kind: route
title: Restrict to the preimage of the co-amenable subgroup and treat each double coset by the Goursat reduction
target: left-right-sofic-closed-under-co-amenable-overgroups
requires:
  - product-free-set-actions-reduce-to-left-right-actions
  - sofic-actions-restrict-to-co-amenable-subgroups
  - gkp-sofic-action-toolkit
artifacts:
  - research/artifacts/pfg-positive-goursat-reduction-2026-09-13.md
---

Full proof: Section 3 of the artifact.

**Setup.** Let `q_1 : F ↠ H` and `q_2 : F' ↠ H`, and put `A_i = q_i^-1(P)`.
`F/A_1 ≅ H/P` as `F`-sets, so `A_1` is co-amenable in `F`, and likewise `A_2`.
Products of Følner sets are Følner, so `D = A_1 x A_2` is co-amenable in
`F x F'`. By (CA) it suffices that `LR(q_1,q_2)` restricted to `D` is sofic.

**Orbits.** The `D`-orbit of `h` is `PhP`, with stabilizer

```text
L_h = { (a,b) in A_1 x A_2 : q_1(a) = h q_2(b) h^-1 }.
```

`L_h` is a subgroup of a product of two countable free groups, and `q_1`
identifies its Goursat quotient with `P ∩ hPh^-1 <= P`. Its finitely generated
subgroups are left-right sofic by subgroup closure. The Goursat reduction makes
`A_1 x A_2 ↷ PhP` sofic, and GKP 2.16 makes the restriction sofic.

**Corollaries.**

- *Amenable extensions.* `R` normal with amenable quotient is co-amenable.
- *Ascending HNN.* The kernel of `H ↠ Z` is an increasing union of copies of
  `B`, so it is left-right sofic by locality and subgroup closure. Then apply
  the amenable-extension case.
- *Firewall.* For Kazhdan `H`, an invariant mean on `ell^infinity(H/P)` gives
  almost invariant vectors in `ell^2(H/P)`, hence an invariant one, so `H/P` is
  finite.
- *Soficity firewall.* (G) of the co-amenable restriction node, together with
  permanence of soficity under subgroups and limits. `∎`
