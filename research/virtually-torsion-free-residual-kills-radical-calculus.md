---
rg: 2
id: virtually-torsion-free-residual-kills-radical-calculus
kind: claim
title: The virtually-torsion-free residual cut down the MF radical satisfies the whole radical calculus, torsion conclusions and finite-index trace included, and vanishes on every virtually torsion-free group
distinct_from:
  torsion-free-seeds-need-kernel-descent-or-trace-corner: that builds two countermodels, each violating one rule, (C) or (I), and leaves the combined (C)+(I) gate open; this builds one countermodel satisfying all of (F), (S), (X), (D), (I), (C) and (A), so the gate is closed and the calculus alone never reaches a torsion-free non-MF group.
  full-mf-radical-seed-has-no-torsion-free-quotient: that kills homomorphic images of a torsion-generated full radical; this kills finite-index passage as well, by inducing to a wreath product.
  torsion-generated-mf-absorbers-die-in-torsion-free-targets: that is one forward-functoriality instance; this is an assignment closed under the full rule set.
  virtually-torsion-free-mf-radical-is-torsion-free: that is the single lemma behind rule (C) here; this turns it into a class obstruction for every derivation.
artifacts:
  - research/virtually-torsion-free-residual-kills-radical-calculus-proof.md
  - research/torsion-free-seeds-need-kernel-descent-or-trace-corner.md
  - research/virtually-torsion-free-mf-radical-is-torsion-free.md
---

**ESTABLISHED (class obstruction), NO PROPERTY `(T)`.**

**Setup.**  The radical calculus is as in
`torsion-free-seeds-need-kernel-descent-or-trace-corner`:

- (F) forward functoriality;
- (S) saturation;
- (X) closure of the full class under extensions, directed colimits, free
  products and amalgams;
- (D) radical-kernel descent;
- (I) finite-index trace;
- (C) torsion conclusions;
- input (A), `R(St_20(L)) = St_20(L)`.

For a group `H`, let

```text
VT(H) = intersection of ker(psi) over all homomorphisms psi : H -> V
        with V virtually torsion-free,
R(H)  = Rad_MF(H) intersect VT(H).
```

**Theorem.**

(a) `R` satisfies all of (F), (S), (X), (D), (I), (C) and (A), with (A)
holding exactly when it holds for `Rad_MF`.  The bare assignment `VT`
satisfies (F), (S), (X), (D) and (I), and satisfies (A) unconditionally.

(b) `R(V) = 1` for every virtually torsion-free `V`, in particular for every
torsion-free group.

(c) More precisely, every torsion-generated subgroup of `Rad_MF(H)` lies in
`R(H)`.  Every element of `Rad_MF(H)` that survives in some virtually
torsion-free image of `H` lies outside `R(H)`.

**Consequences.**

1. **Consequence 3 of the w12 obstruction is corrected.**  No derivation in
   the calculus, even one using both (C) and (I), proves `1 != x in Rad_MF(T)`
   for a torsion-free `T`.  It cannot even prove this for a virtually
   torsion-free `T`.  The gate "torsion conclusion, then finite-index trace"
   is realized by `virtually-torsion-free-infinite-mf-radical-gives-seed` only
   vacuously: its corner corollary has no instances
   (`virtually-torsion-free-mf-radical-is-torsion-free`).
2. **Where any route must leave the calculus.**  Any proof of
   `property-t-free-torsion-free-fp-non-mf-seed` from (A) must contain a step
   that `R` violates.  At that step, a group `H` receives a radical element
   `x` whose image under some `psi : H -> V`, with `V` virtually torsion-free,
   is nontrivial.  By (F) that image is a nontrivial element of `Rad_MF(V)`.
   So the step itself certifies that a virtually torsion-free group is not
   MF.  It is an independent non-MF theorem for a virtually torsion-free
   group, and no bookkeeping of torsion radicals provides it.
3. **The two surviving exits.**
   - The descent `full-mf-radical-abelianized-cover-is-not-mf`, which `R`
     violates because the cover is torsion-free
     (`free-abelianized-cover-is-torsion-free`).
   - An intrinsic analytic non-MF theorem for a torsion-free group without
     Property `(T)`.
   So the manuscript goal needs the Leavitt collapse *and* one of these two.
   The virtual-torsion corner route is not a third exit.

**Invariant and death step.**  The invariant is `VT`, the
virtually-torsion-free residual.  The step that dies is the passage from a
torsion conclusion to a virtually torsion-free host.  Torsion in any MF
radical dies in every virtually torsion-free image, because such images have
torsion-free MF radical.  So the torsion never reaches the finite-index
subgroup that the trace rule (I) would hand on.
