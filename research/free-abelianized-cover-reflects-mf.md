---
rg: 2
id: free-abelianized-cover-reflects-mf
kind: claim
title: Does MF descend from the free abelianized cover to the group
distinct_from:
  mf-quotient-nonclosure: that exhibits one surjection with MF source and non-MF target, so no general descent holds; this asks whether descent holds along the single canonical surjection with free abelian kernel, which that counterexample does not touch.
  mf-extension-nonclosure: that exhibits MF kernel and MF quotient with non-MF total group, a statement about building up; this asks about reading a property downward along one specific surjection.
  free-abelianized-cover-is-torsion-free: that is the group theory of the cover, proved and unconditional; this is the analytic transfer statement, open, and the only missing input of the torsion-free route built on it.
artifacts:
  - research/artifacts/torsion-free-transfer-covers-and-obstructions-2026-09-08.md
---

**OPEN.**  For `F` free and `R` normal in `F`, is it true that

```text
F/[R,R] is MF   =>   F/R is MF ?                                        (D)
```

Equivalently, in radical form (`universal-mf-quotient`), does a nontrivial
mark lift:

```text
Rad_MF(F/R) != 1   =>   Rad_MF(F/[R,R]) != 1 ?                          (D')
```

The contrapositive of `(D)` is what a torsion-free transfer needs: by
`free-abelianized-cover-is-torsion-free` the cover is torsion-free, countable
and of the same rank, so `(D)` applied to any finitely presented non-MF group
would produce a torsion-free countable non-MF group with no new analytic
input.  That is `torsion-free-countable-non-mf-from-abelianized-cover`.

## Attempts

- **The recorded "covers do not work" verdict does not settle this.**
  `torsion-free-countable-non-mf` and `torsion-free-finitely-presented-non-mf`
  both record that non-MF does not pass down along surjections, because free
  groups are residually finite, hence MF, and surject onto everything.  That
  refutes a general cover principle and it is why `(D)` cannot be free.  It
  says nothing about one canonical cover, and `F/[R,R]` is closer to `F/R`
  than `F` is: its kernel `R/[R,R]` is abelian, whereas the kernel `R` of the
  free cover is free of infinite rank.  The known quotient-nonclosure witness
  `mf-quotient-nonclosure` is exactly the free cover `F_8 -> E`, whose kernel
  is non-amenable; no witness with abelian kernel is known here.
- **Radical functoriality gives the useless inclusion.**  For a surjection
  `q : E -> G`, `Rad_MF(E) <= q^(-1)(Rad_MF(G))`, which is vacuous when
  `Rad_MF(E) = 1`.  So `(D)` cannot come from the universal-quotient calculus
  alone; any proof must use the structure of `R/[R,R]`.
- **The amenable-kernel permanence theorems point the other way.**
  `amenable-quotient-preserves-metric-approximability` (Brude--Sasyk) has the
  amenable group as the QUOTIENT and concludes soficity, weak soficity,
  linear soficity or hyperlinearity for the extension; here the amenable group
  is the kernel, the direction needed is downward, and the property is MF.
  `mf-extension-nonclosure` shows MF is not closed under extensions at all,
  so no general two-out-of-three argument is available.
- **Magnus embedding handle.**  The classical Magnus embedding (Magnus--Karrass--Solitar,
  Combinatorial Group Theory, Corollary 4.10.1, already used in this archive's
  Fox--Magnus lane) embeds `F/[R,R]` into the restricted wreath product
  `Z^n wr G` with `n` the rank of `F`, by `f[R,R] -> (Fox derivatives of f, fbar)`.
  Since `G` sits in that wreath product as the top group, the ambient group is
  non-MF whenever `G` is; the missing step is to locate the lifted mark inside
  the embedded copy of the cover, which the ambient statement does not do.
  `mf-radical-product-and-restricted-sum-formulas` computes radicals of
  restricted sums but not of the semidirect twist, so it does not close this.
- **What descent would actually require.**  An injective corona homomorphism
  of `F/[R,R]` makes the images of elements of `R` commute; it does not make
  them trivial, which is what a homomorphism of `F/R` needs.  Every nontrivial
  element of `R/[R,R]` is separated by such a model.  The missing operation is
  one on the matrix models that kills that kernel while keeping separation
  downstairs.  Assuming instead that every homomorphism from `F/R` to an MF
  group is trivial does not supply it: that hypothesis constrains maps AFTER
  they factor through `F/R`, and does not make a map of the cover factor.
- **Deferred:** no attempt at a proof or a counterexample is made here.  A
  counterexample would be as informative as a proof: it would be the first
  quotient-nonclosure witness with abelian kernel.
