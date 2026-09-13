# Deciding LLP for `C^*(Sp_4(Z))`: calibration and obstruction audit (2026-09-13)

Target: `sp2g-z-full-c-star-algebra-has-llp` at `g = 2`.

Sources read locally from PDFs fetched on MSI this date (page numbers are
the printed page numbers, checked against the form-feed count):

- [ISW] A. Ioana, P. Spaas, M. Wiersma, *Cohomological obstructions to
  lifting properties for full C*-algebras of property (T) groups*,
  arXiv:2006.01874.
- [FFW] F. Fournier-Facio, R. Willett, arXiv:2603.18456v2.

## 0. Calibration: `F_2 x F_2 <= Sp_4(Z)`

**Embedding.**  Write `Z^4` with symplectic basis `e_1, f_1, e_2, f_2`.
The hyperbolic planes `<e_1,f_1>` and `<e_2,f_2>` are orthogonal for the
form, and on each plane `Sp_2(Z) = SL_2(Z)`.  Block-diagonal matrices give

```text
SL_2(Z) x SL_2(Z) <= Sp_4(Z).                               (CAL1)
```

The Sanov matrices `[[1,2],[0,1]]` and `[[1,0],[2,1]]` generate a free
subgroup of rank two (of finite index) in `SL_2(Z)`, so

```text
F_2 x F_2 <= Sp_4(Z).                                       (CAL2)
```

**Permanence.**  [ISW] Remark 1.2 (p. 4): for countable `Sigma < Gamma`,
"if `C*(Gamma)` has the LP (respectively, the LLP), then so does
`C*(Sigma)`".  The same statement is [FFW] Corollary 3.17 (p. 17): "The LP
and LLP both pass to subgroups."  Hence

```text
C*(Sp_4(Z)) has LLP  ==>  C*(F_2 x F_2) has LLP.            (CAL3)
```

**Status of `F_2 x F_2`.**  [FFW] p. 6: "In another direction, the
following seems to be a particularly challenging group for which the (L)LP
is open.  Question 1.6.  Does `F_2 x F_2` have the (L)LP?"  And p. 18: "It
seems to be open whether the (L)LP is preserved under direct products.  For
example, it is open whether `F_2 x F_2` has the (L)LP (Question 1.6); this
problem is generally considered difficult, see for example the discussion
at the end of [155, Section 3]."  (I did not read [155] itself.)

**A second open question sits on the same side.**  `Sp_4(Z)` has property
(T): it is a lattice in `Sp_4(R)`, which [ISW] Example 1.3(i) (p. 4) lists
among the simple Lie groups with property (T).  [FFW] p. 6: "Question 1.9.
Is there an example of an infinite property (T) group (or just a group with
property (T) relative to an infinite subgroup) with the (L)LP?"  [FFW]
Remark 3.8 (p. 15): "We do not know an example of a group with the LLP that
has property (T), or even property (T) with respect to an infinite subgroup
(Question 1.9)."

**CALIBRATION OUTCOME.**

1. `C*(F_2 x F_2)` is NOT known to fail LLP.  The calibration does not
   refute the target.
2. A positive answer for `Sp_4(Z)` would answer three questions at once:
   - the LLP half of [FFW] Question 1.6, positively, by (CAL3).  [FFW] call
     this "generally considered difficult".
   - the LLP half of [FFW] Question 1.9, positively.
   - and it would produce a finitely presented nonhyperlinear group, by the
     established dichotomy `sp4-llp-failure-or-maslov-nonhyperlinear-extension`.
   The target node already records a fourth consequence: LLP without LP.
3. So the positive side is at least as hard as an open problem that [FFW]
   single out as difficult.  This lane works on the refutation side
   (sections 1-2); section 4 only records what the positive side would
   need.

**Other subgroups with known LLP failure.**

- [ISW] Corollary B (p. 2): "Let `Gamma = Z^2 rtimes Sigma`, where
  `Sigma < SL_2(Z)` is a non-amenable subgroup.  Then `C*(Gamma)` does not
  have the LLP.  Thus, `C*(Z^2 rtimes SL_2(Z))` and `C*(SL_n(Z))` do not
  have the LLP, for any `n >= 3`."
  - Every non-amenable `Sigma < SL_2(Z)` contains a free group `F`.  The
    established `sp4-contains-no-isw-affine-subgroup` excludes
    `Z^2 rtimes F` from every subgroup of `Sp_4(Z)`, not only the
    parabolics.
  - The Corollary B family, in the form quoted above, is therefore absent.
    Its ring generalisation (same page, "More generally, if R is ...")
    contains `Z^2 rtimes SL_2(Z)` whenever the ring contains `Z`.  Positive
    characteristic rings give infinite torsion abelian subgroups, which
    `GL_4(Z)` cannot contain.
  - `SL_3(Z)` does not embed in `Sp_4(Z)` (the superrigidity bullet on the
    target node).
- [ISW] Theorem A (p. 2), scalar cocycles realized by finite-dimensional
  projective representations: no data on `Sp_4(Z)` or on any finite-index
  subgroup (`isw-theorem-a-has-no-data-on-sp4-finite-index-subgroups`).  On
  the maximal parabolics the scalar obstruction dies on the radicals
  (`isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals`).
- [ISW] Corollaries D and E (p. 4) and Theorem G (p. 5) conclude only
  "does not have the LP".
- [FFW] Remark 3.8 (p. 15) also cites the Buss--Echterhoff--Willett examples
  built from Osajda's groups whose Cayley graphs contain expanders.  For
  Osajda's non-exact a-T-menable groups, failure of the (L)LP is only
  "plausible", not known.
  - Groups containing expanders in this way are not exact.  Every subgroup
    of the linear group `Sp_4(Z)` is exact (Guentner--Higson--Weinberger;
    not source-read here, no locator claimed).  So neither family occurs.
  - [FFW] Remark 3.8 also cites Ozawa [156, Corollary 5] and Thom
    [183, p. 198].  I did not read those sources and record no subgroup
    check for them.

Conclusion of section 0: no subgroup of `Sp_4(Z)` is currently known to
fail LLP.  The refutation side needs a mechanism at `Sp_4(Z)` itself or at a
subgroup with no recorded fence.
