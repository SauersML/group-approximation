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

**`(BLD4)`.**  Combining `(BLD1)`, `(BLD2)` and `(BLD3)`: a uniform derivation
whose only BCS-dependent input is `beta` cannot distinguish the non-CE system
from the classical counterexample.  A correct derivation must use additional
contextual operator structure of `B`, not merely the scalar lower bound.

**Why centrality is not the obstruction.**  In one amalgam `A *_<z> B`, an
element `z` central in both vertex factors is central in that two-vertex
amalgam.  But a selector which does not belong to a later vertex group need
not commute with that group's generators.  Concretely,

```text
<x,y | x^2=y^2=[x,y]=1> *_(<y>)
<y,z | y^2=z^2=[y,z]=1>
```

has no relation `[x,z]=1` and is `C_2 x (C_2*C_2)`.  Hence a context graph
preserves the intended partial commutation.  Its failure as a return
transducer is the virtually-free/integer-flow argument in `(BLD3)`, not a
global-classicality collapse.
