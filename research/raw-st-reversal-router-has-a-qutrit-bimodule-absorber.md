---
rg: 2
id: raw-st-reversal-router-has-a-qutrit-bimodule-absorber
kind: claim
title: A router which swaps both raw orientations still has an exact qutrit bimodule absorber
distinct_from:
  raw-root-hecke-gap-is-blind-to-qutrit-one-over-eighteen-cokernel: that tensors the complete Hecke packet with one commutant head; this also adjoins an exact mixed router square identifying the S and T charts
  two-raw-roots-have-a-uniform-full-carrier-gap: that controls distance to one full-carrier intertwiner; this constructs two exact intertwiner charts and an involution exchanging them
  finite-normalizer-covariance-density-no-go: that treats an abstract finite automorphism action on an old carrier; this gives the literal Toeplitz reversal and simultaneously authenticates the qutrit left and right head positions
---

Let `S_N,T_N` be the truncated unilateral shifts on `F_2^N`, and
let `R_N` reverse the standard basis. Put

```text
r_N=I_28 tensor R_N in F_N=GL_(28N)(F_2),
theta_N=Ad(r_N).
```

Then `theta_N` fixes the constant core and exchanges the two raw roots:

```text
theta_N(I+E_ij tensor S_N)=I+E_ij tensor T_N.             (STR1)
```

Let `F_0` be the 288-element qutrit sign packet and
`q_b=Ee_b`, so `tau_(F_0)(q_b)=1/18`. For every unitary
representation `beta` of `F_N` there are two exact rectangular
charts `epsilon=0,1`, each with head density `1/18`, and an
involutive router `W` such that

```text
W Pi_0(g,u) W^*=Pi_1(theta_N(g),u),
W Q_0 W^*=Q_1,
W S_0=S_1 W_S.                                            (STR2)
```

Here chart zero uses the left qutrit regular action and the commuting
right head `Q_0=R(q_b)`; chart one uses the right qutrit regular action
and the commuting left head `Q_1=L(q_b)`. The source spaces are the
orthogonal complements of the heads, `S_epsilon` are their inclusions,
and `W_S` is the restriction of `W` to those complements.

Thus the square in `(STR2)` simultaneously

- exchanges the raw `S_N)- and `T_N)-root orientations;
- identifies the commutant head with the natural qutrit packet atom in
  the opposite chart; and
- identifies the complete rectangular occurrences, not only their ranks.

All constant-core and both raw-root covariance rows are exact in both
charts. After adjoining the two target/source gradings and block actors,
the entire two-chart image is finite, a quotient of

```text
((F_N times F_0)^2 times D_8^2) semidirect C_2.            (STR3)
```

Both target charts restrict to a regular `F_0)-module, so the canonical
qutrit trace is retained.

Consequently even a mixed equality router which explicitly swaps the two
raw orientations does not expose the multiplicity cokernel when it factors
through finite Toeplitz reversal. A successful mixed law must distinguish
the two endpoint defects

```text
I-S_NT_N                 and                 I-T_NS_N,
```

which reversal exchanges and which have equal rank one. In the one-sided
Jacobson limit only the first survives because `TS=1`. The next law must
therefore return that non-surjective boundary to the same authenticated
chart; finite `S/T` symmetry is another exact absorber.

DERIVATION
two-chart-reversal-and-inversion-bimodule-proof
