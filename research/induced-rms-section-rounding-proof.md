---
rg: 2
id: induced-rms-section-rounding-proof
kind: route
title: Average Schreier edge diagrams and round the induced range projection
target: induced-rounding-needs-rms-section-fillings
requires:
  - one-unipotent-quotients-are-bounded-congruence
  - regular-bs14-cores-admit-dyadic-one-power-shadows
  - regular-congruence-endpoint-orbit-has-uniform-selberg-retraction
  - repeated-squaring-and-tau-do-not-supply-the-moving-basin
---

Use the right-coset model of induction.  A vector is a tuple indexed by
`T_N`; the exact induced representation `rho_N` uses `(IRF2)` to transport
the fiber by `beta(b)`.  If `U(t)` denotes evaluation of the chosen section
word, define

```text
(V_U xi)(t)=|T_N|^(-1/2) U(t)^* xi.                  (ISR1)
```

Every `U(t)` is unitary, so `V_U^*V_U=1` exactly.  At coordinate `t`, the
difference `rho_N(a)V_U-V_UU(a)` is, up to multiplication by unitaries, the
evaluation defect of the section-word equality in `(IRF2)`.  A relative
diagram of area `A_N(t,a)` and ordinary telescoping give

```text
||edge_defect(t,a)||_2 <= A_N(t,a) delta.             (ISR2)
```

The coordinates in the induced direct sum are orthogonal.  Squaring
`(ISR2)`, averaging over `t`, and taking square roots proves `(IRF5)`.

Put `P=V_UV_U^*`.  The elementary isometry calculation gives, in Frobenius
norm normalized by `dim(H)`,

```text
||[rho_N(a),P]||_(2,H)
 <=2||rho_N(a)V_U-V_UU(a)||_(2,H).                   (ISR3)
```

Average conjugation by the exact finite-group representation `rho_N`.
The uniform congruence Cayley gap gives a Poincare estimate for this exact
left-right representation, so the conditional expectation `E_N(P)` onto
`rho_N(A_N)'` satisfies

```text
||P-E_N(P)||_(2,H) <= C/kappa M_N delta.              (ISR4)
```

Spectrally cut `E_N(P)` at `1/2`.  Functional calculus produces a projection
`Q in rho_N(A_N)'` with the same bound up to a universal constant.  For two
projections, squared unnormalized Frobenius distance dominates their rank
difference; hence `(ISR4)` gives `(IRF6)`.  A polar identification of the
ranges of `P` and `Q` then transports the exact compression of `rho_N` on
`Q` back to a generalized flexible representation near `U`, with cost
`O_kappa(M_N delta)`.

For the dyadic shadow, `delta=O(K^(-1/2))`.  Therefore the area-telescoping
implementation tends to zero exactly under `(IRF7)`.  A diameter bound gives
short section **words** but contains no bound on the areas of the edge loops.
The scalar squaring presentations in
`repeated-squaring-and-tau-do-not-supply-the-moving-basin` show abstractly
that even a maximally gapped endpoint and short rows do not supply such
two-dimensional conditioning.  Any improvement from `A delta` to
`sqrt(A)delta` would require a new orthogonality/square-function estimate for
the relator errors; it is not a consequence of the Cayley spectral gap used
in `(ISR4)`.

More directly, if `(IRF8)` holds, the left side is the square of the
intertwining error in `(ISR1)`, averaged over its orthogonal induced
coordinates.  Equations `(ISR3)--(ISR4)` then give

```text
||P-Q||_(2,H)^2 <= C_kappa E_R(U).                    (ISR5)
```

The projection rank inequality used above turns `(ISR5)` into

```text
|rank(Q)-dim(H)|/dim(H) <= C_kappa E_R(U),            (ISR6)
```

which is the desired energy-paid flexible padding ledger.  Thus no further
finite-group representation estimate is missing after `(IRF8)`; the whole
gap is the uniform relative 2-cochain estimate itself.
