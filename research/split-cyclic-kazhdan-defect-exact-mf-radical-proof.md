---
rg: 2
id: split-cyclic-kazhdan-defect-exact-mf-radical-proof
kind: route
title: Kill the Kazhdan kernel, separate through Z, and use sofic-by-amenable permanence
target: split-cyclic-kazhdan-defect-exact-mf-radical
requires:
  - normal-kazhdan-defect-non-mf
  - mf-positive-controls
  - universal-mf-quotient
  - sofic-kernel-amenable-quotient-permanence
  - hnn-extension-finite-presentation-permanence
  - sofic-implies-hyperlinear
artifacts:
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Sofic/SoficByAmenablePermanence.lean
---

Write `Kbar=K x {0}`.  It is nontrivial, normal and Kazhdan, and `(SCZ1)`
places it inside the compression defect.  The uncontaminated theorem
`normal-kazhdan-defect-non-mf` therefore gives

```text
Kbar <= Rad_MF(G).                                     (SCZ3)
```

The exponent map `epsilon:G->Z` has kernel exactly `Kbar`.  Since `Z` is
residually finite and therefore MF, compose `epsilon` with a faithful corona
model of `Z`.  The resulting representation has kernel `Kbar`, so

```text
Rad_MF(G) <= Kbar.                                     (SCZ4)
```

Together `(SCZ3)` and `(SCZ4)` prove the exact radical and quotient in
`(SCZ2)`.  The universal property in `universal-mf-quotient` gives the stated
factorization of every MF-target homomorphism, with uniqueness because
`epsilon` is onto.

Finite presentation is now a direct hypothesis on `G`; this is weaker than
requiring `K` finitely presented.  In the useful special case where `K` is
finitely presented, the mapping-torus presentation adds one stable letter
and finitely many relations implementing `phi` on a finite generating set,
so `hnn-extension-finite-presentation-permanence` supplies that hypothesis.
If an element of `G` has finite order, its exponent in `Z` is zero and it
lies in torsion-free `Kbar`, proving torsion-freeness.  Soficity follows from
the sofic kernel `Kbar` and amenable quotient `Z`; hence `G` is hyperlinear.
Finally, normal generation of `K` by `k` already uses conjugators in the
subgroup `Kbar`, so `<<k>>^G=Kbar` as well.
