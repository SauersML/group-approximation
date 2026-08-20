---
rg: 2
id: multiplicity-surplus-is-blind-to-the-non-ce-input-proof
kind: route
title: Substitute a classical unsatisfiability gap for the compactness constant
target: multiplicity-surplus-is-blind-to-the-non-ce-input
requires:
  - non-ce-bcs-has-finite-dimensional-forbidden-mass-gap
  - finite-graph-of-groups-representation-types-are-integer-flows
---

**`(BLD1)`.**  Inspect the statement of
`non-ce-bcs-has-finite-dimensional-forbidden-mass-gap`: its conclusion `(FMG)`
is the single inequality `sum_c sum_(a in F_c) tau_d(P_a^c) >= beta_B`.  The
hypothesis on `B` appears only in the proof, never in the conclusion, and the
downstream steps quantify over the conclusion.  So any argument taking `(FMG)`
as input is a function of `beta_B` alone.

**`(BLD2)`.**  Let `(Z_x)` be globally commuting self-adjoint involutions in
`M_d(C)`.  Simultaneous diagonalization gives an orthogonal decomposition of
`C^d` indexed by assignments `s in {0,1}^X`, and `tau_d` restricted to it is a
probability distribution `mu` on assignments.  For each context `c`,

```text
sum_(a in F_c) tau_d( prod_(x in U_c) (I + (-1)^(a_x) Z_x)/2 )
   = Pr_(s ~ mu)[ s|_(U_c) in F_c ],
```

so the left side of `(FMG)` is the expected number of contexts violated by a
random assignment drawn from `mu`.  If `B` is classically unsatisfiable, every
assignment violates at least one context, so that expectation is at least `1`.
(A sharper constant is the usual unsatisfiability gap, but `1` suffices.)

**`(BLD3)`.**  A finite graph of finite groups has virtually free fundamental
group; virtually free groups are residually finite, hence sofic, hence
hyperlinear.  `finite-graph-of-groups-representation-types-are-integer-flows`
records the representation-theoretic form of the same fact, namely that the
dimension vector gives a positive stationary solution of the edge restriction
equations, so no genuine multiplicity surplus can accumulate.  Therefore a chain
concluding non-hyperlinearity from `beta` alone would contradict hyperlinearity
of that group.

**`(BLD4)`.**  Combining `(BLD1)`, `(BLD2)` and `(BLD3)`: a correct derivation
cannot be a function of `beta` alone, so it must use a hypothesis on `B` beyond
the forbidden-mass bound, and the only such hypothesis available is
non-embeddability.

**The centrality remark.**  In `K(M)` the generators `z_l` are declared central.
If `G = A *_C B` with `z in C` central in `A` and central in `B`, then `z`
commutes with every generator of `A` and of `B`, which together generate `G`, so
`z` is central in `G`.  Hence amalgamating context packets over their shared
selectors makes every BCS variable globally commuting, which is the hypothesis
of `(BLD2)`.
