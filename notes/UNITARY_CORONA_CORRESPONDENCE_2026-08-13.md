# Unitary-corona correspondence audit — 2026-08-13

The manuscript now uses the same primary MF object as
`GroupApproximation/Sofic/OperatorMF.lean`:

```text
Ucor((d_n)) = (product_n U(M_d_n(C))) /
              { (u_n) : ||u_n - 1|| -> 0 }.
```

The denominator is a normal subgroup because the operator norm is unitarily
invariant.  This is exactly the cofinite unitary-sequence quotient
`NormMatrixCoronaUnitary` used by `IsOperatorMF`, not an ultrafilter quotient.

For the analytic proof the manuscript also uses the C-star quotient

```text
Q((d_n)) = (product_n M_d_n(C)) / (direct-sum_n M_d_n(C)).
```

The coordinate quotient gives a canonical isomorphism
`kappa : Ucor((d_n)) -> U(Q((d_n)))`.  Its kernel is exactly the null
unitary sequences.  Surjectivity is the polar-correction lemma: an arbitrary
bounded lift of a unitary in `Q` is asymptotically unitary and can be changed
by a norm-null sequence to coordinatewise unitaries.  The manuscript proves
this as Lemma `unitarycorona` immediately after its lifting lemma.

Consequently the division of labor is now explicit:

- group MF, corona representations, the MF radical, and the statement of
  Theorem A use `Ucor`, matching Lean literally;
- the Kazhdan projection, corners, stable finiteness, and fixed-space argument
  are written in `U(Q)` after applying `kappa`;
- the full and reduced group-C-star conclusions remain unchanged: a C-star
  embedding into `Q` gives a group embedding into `U(Q)`, which is transported
  back through `kappa^{-1}` to an MF embedding in `Ucor`.

The distinction prevents a definitional-equality claim that the current
mathlib quotient API cannot express while preserving the standard
operator-algebraic formulation as a proved corollary.
