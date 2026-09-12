---
rg: 2
id: fpbs-residual-price-one-non-ah-class-nonuniqueness
kind: claim
title: Every Cayley graph of a fixed-price-one non-acylindrically-hyperbolic group without amenable wq-normal subgroups has strict thresholds
distinct_from:
  fpbs-no-amenable-wq-normal-class-nonuniqueness: that covers every nonamenable group with no infinite amenable wq-normal subgroup; this removes the groups not of fixed price one (Lyons) and the acylindrically hyperbolic groups (Choi--Seo), leaving the part that no cited theorem touches.
  fpbs-fixed-price-one-percolation-kernel: that covers all nonamenable fixed-price-one groups, including every group with an infinite amenable normal subgroup; this is the subclass that is also not acylindrically hyperbolic and has no infinite amenable wq-normal subgroup.
artifacts:
  - research/artifacts/fpbs/docs/benjamini-schramm-frontier-map.md
---

**OPEN.** Let `Gamma` be a nonamenable finitely generated group such that

1. `Gamma` has fixed price one;
2. `Gamma` is not acylindrically hyperbolic;
3. no infinite amenable subgroup of `Gamma` is wq-normal.

Then every Cayley graph of `Gamma` has `p_c < p_u`.

**Structure of the class.** Use the intermediate-subgroup definition of
wq-normality. Condition 3 then says that every infinite amenable subgroup `A`
lies in a proper subgroup `I` with `g I g^(-1) ∩ I` finite for every `g notin I`.
Such an `I` is the intermediate subgroup witnessing that `A` is not wq-normal.

The known candidates are monster-like:
- Tarski monsters, which have no infinite proper subgroups at all;
- torsion-free Tarski monsters, whose proper subgroups are cyclic and whose
  maximal cyclic subgroups are almost malnormal.

Neither kind is acylindrically hyperbolic, since non-elementary acylindrically
hyperbolic groups contain free subgroups. Whether they have fixed price one is
not recorded here.

## Attempts

* **Every cited class misses it by definition.**
  - Lyons requires a group not of fixed price one.
  - Choi--Seo requires acylindrical hyperbolicity.
  - The relative susceptibility equivalence
    `fpbs-bs-iff-finite-relative-susceptibility` requires an infinite amenable
    wq-normal subgroup.

  **Where it stops:** no argument in the region uses the almost malnormal
  subgroups that condition 3 supplies.
* **Separation along a non-wq-normal subgroup.**
  `fpbs-relative-gap-along-any-subgroup-separates` needs no wq-normality. So for
  a torsion-free member one may take `I` to be a maximal cyclic subgroup, and a
  gap `p_c(G) < p_c(I;G)` would suffice.

  **Where it stops:** for almost malnormal `I` there is no estimate on
  `chi^I_p` above `p_c(G)`. The identity `p_c(I;G) = p_u(G)` is also
  unavailable, so this gives a sufficient condition only, not an equivalence.
