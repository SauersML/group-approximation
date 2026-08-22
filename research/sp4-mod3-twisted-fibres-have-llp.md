---
rg: 2
id: sp4-mod3-twisted-fibres-have-llp
kind: claim
title: The two nontrivial mod-three twisted group C*-algebras of the symplectic lattice have the local lifting property
distinct_from:
  sp2g-z-full-c-star-algebra-has-llp: that is the untwisted fibre (the full group C*-algebra of Sp_4(Z)); this concerns the alpha- and alpha^2-twisted fibres of the Deligne triple cover, which have no finite-dimensional representations at all, so the RFD and Ioana--Spaas--Wiersma tool kits have no purchase on them in either direction.
  sp4-metaplectic-class-pointwise-coboundary-limit: that settled a cocycle-rigidity question about the mod-two metaplectic class; this is a lifting question about the mod-three twisted algebras, with no cocycle approximation involved.
---

OPEN CLAIM.  Let `alpha` be the multiplier of a section of Deligne's
triple cover `1 -> Z/3 -> E_3 -> Sp_4(Z) -> 1`.  Then the twisted group
C*-algebras

```text
C^*(Sp_4(Z); alpha)   and   C^*(Sp_4(Z); alpha^2)                  (TF3)
```

have Kirchberg's local lifting property.

**Why it matters.**  `C^*(E_3)` decomposes as the finite direct sum of
its three central-character fibres `C^*(Sp_4(Z); alpha^j)`, `j = 0,1,2`
(central idempotents of the finite central `Z/3`), and LLP holds for a
finite direct sum iff it holds for every summand.  So this claim plus the
untwisted fibre `sp2g-z-full-c-star-algebra-has-llp` is exactly LLP of
`C^*(E_3)`, which by `llp-non-rf-kazhdan-group-is-non-hyperlinear` makes
the non-residually-finite Kazhdan group `E_3` non-hyperlinear — the
route `non-hyperlinear-from-e3-fibre-llp` — and by the equivalence
`deligne-sector-gap-is-exactly-nonhyperlinearity` simultaneously yields
the mod-three Maslov defect gap and the one-word central collapse of the
Deligne lane.  This is Fournier-Facio--Willett Question 1.12 (does the
LLP pass from a group to its twisted algebras?) at its sharpest live
instance: a positive answer to their question reduces this claim to the
untwisted fibre.

## Attempts

- **No tool reaches these algebras in either direction.**  The twisted
  fibres have NO nonzero finite-dimensional representations
  (`deligne-triple-cover-fd-central-invisibility`), so they are as far
  from RFD as possible, the Ioana--Spaas--Wiersma finite-dimensional
  realizability mechanism is vacuous, and the
  Fournier-Facio--Willett positive machinery (LLP + RFD, property FD)
  does not apply.  Nothing in the recorded literature computes any
  lifting property of a twisted algebra of a higher-rank lattice.
- **The Connes-embeddability of the fibres is also live.**  Thom's
  criterion (Lemma 3.4, `thom-central-corner-criterion`) makes
  hyperlinearity of `E_3` equivalent to Connes-embeddability of all
  three twisted von Neumann fibres; if the alpha-fibre were shown non-CE
  the goal would close by a different mouth (the trace route), so BOTH
  the C*-lifting and the von Neumann embedding questions for `(TF3)` are
  goal-relevant and unrecorded.
