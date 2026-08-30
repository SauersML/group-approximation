# STW XXII: the dimension-two uniform Stiefel obstruction

## Result

Global metric-uniform `LC^1` of the weighted purification fibres is
equivalent to one fixed-support statement: uniform small-loop filling for the strong
Stiefel spaces

```text
V(p,e)={v:v^*v=p, vv^*<=e},       tau(p)<=s<tau(e).
```

The reverse implication uses a spectral cut.  The high spectral frame is
close in ordinary `2`-norm and is filled by the assumed Stiefel modulus.
The low spectral frame can move arbitrarily: its total weighted diameter
is at most twice the square root of its `L^1` mass.  Strict corner slack
allows the low frame to be completed relatively over the disk.

## What is and is not known

Every individual hyperfinite-factor Stiefel space is path connected and
simply connected: apply the homotopy exact sequence to its locally trivial
unitary-orbit bundle, whose total and stabilizer unitary groups are strongly
contractible.  This does not imply a local simple-connectivity modulus
uniform over the support trace.  The principal-logarithm path proves the
`LC^0` estimate but is pointwise in its unitary extension; logarithm branch
choices need not be continuous on a loop.

Farah--Vaccaro explicitly identify the analogous equi-`LC^n` issue as the
obstruction beyond one-dimensional bases.  Their result proves continuous
comparison over bases of dimension at most one for arbitrary `II_1`
factors and in all finite dimensions for factors carrying the stronger
Popa--Takesaki contracting semigroup.  It does not state `(USF_1)` for the
family above.  Jekel's unitary-group contractibility theorem likewise gives
only the pointwise connectivity needed through the orbit bundle, not the
uniform family estimate.

No unconditional dimension-two trace theorem is claimed here.

Michael's ambient-local equi-`LC^1` hypothesis is weaker than the global
metric-uniform condition audited here.  Thus `(USF_1)` is a sharp reversible
criterion for the global-uniform route and a sufficient condition for
dimension two, not a proved necessary condition for every possible
Michael-selection argument.

Primary sources:

- I. Farah and A. Vaccaro, *Continuous Selection of Unitaries in II_1
  Factors*, Proc. Amer. Math. Soc. 154 (2026), 1609--1622,
  https://arxiv.org/abs/2501.01272.
- D. Jekel, *The unitary group of a II_1 factor is SOT-contractible*,
  Math. Ann. 393 (2025), 3109--3117,
  https://arxiv.org/abs/2508.05834.
- E. Andruchow and A. Varela, *States with equivalent supports*, J.
  Operator Theory 53 (2005), 35--48,
  https://jot.theta.ro/jot/archive/2005-053-001/2005-053-001-002.pdf.
