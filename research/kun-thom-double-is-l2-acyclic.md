---
rg: 2
id: kun-thom-double-is-l2-acyclic
kind: claim
title: Every L²-Betti number of the Kun--Thom group double G *_Γ G vanishes
distinct_from:
  kun-thom-wreath-is-l2-acyclic: that is the wreath product, killed at once by its normal lamp group; the double has no infinite normal amenable subgroup and needs the geometry of the two elementary groups.
  kun-thom-wreath-and-double-have-fixed-price-one: that is the cost of the double; this is its L²-Betti numbers.
  kun-thom-double-has-vanishing-first-l2-betti-number: that is degree one, which is established; this is every degree.
---

**OPEN.** For the Theorem E pair `Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^±]) ⋊ SL_d(Z)`,
`r, d >= 3`, `β_n^(2)(G *_Γ G) = 0` for every `n >= 0`.

## Attempts

- **Degrees zero and one: done.** `β_0^(2) = 0` because the group is infinite.
  `β_1^(2) = 0` by fixed price one and Gaboriau's inequality
  (`kun-thom-double-has-vanishing-first-l2-betti-number`).
- **Low degrees through frame complexes (2026-09-12, ex-lueck-approximation).**
  - Put `A = F_q[x_1^±..x_d^±]` or `F_q[x_1..x_d]`, of Krull dimension `d`, so `sr(A) <= d+1`.
  - Van der Kallen's Theorem 2.6(i), as used in the proof of Lemma 5.10 of Randal-Williams--Wahl
    (arXiv:1409.3541), makes the complex of splittable injections `A^(p+1) -> A^r`
    `(r - sr(A) - 1)`-connected.
  - Stabilizers in `GL_r(A)` contain infinite normal abelian unipotent radicals. So
    `l2-betti-numbers-vanish-for-actions-with-l2-acyclic-stabilizers` gives
    `β_n^(2)(GL_r(A)) = 0` for `n <= r - d - 2`.
  - Passing to `EL_r(A)` needs the radicals inside `EL_r(A)`, that is, Suslin's normality
    theorem `E_r(A) ⊴ GL_r(A)` (`r >= 3`, `A` commutative). It is not imported here.
  - With it, Theorem 6.4(ii) (normal subgroup) and 6.4(iv) (amalgams) of Lück's survey
    arXiv:math/0310489 would give vanishing of `β_n^(2)(G *_Γ G)` for `n <= r - d - 2`.
  - Stops: one import missing, and the range is bounded by `r - d - 2`.
- **Above degree `r - d - 2`.** No complex with amenable-radical stabilizers and higher
  connectivity is known to me for these rings. The Leavitt trick of changing the rank is
  unavailable, since `M_r(A)` is not isomorphic to `A`.
