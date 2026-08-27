---
rg: 2
id: free-relative-placement-closes-one-balanced-chord
kind: claim
title: Free relative placement closes one balanced chord in a finite signed packet
distinct_from:
  commuting-separator-chord-is-capacitated-transport: that decides a chord for a fixed pair of commuting separator algebras and fixed joint-cell capacities; this chooses the relative placement and constructs the smallest capacities directly from the two conditional tables.
  tracial-bcs-has-rational-balanced-hyperoctahedral-atlas: that balances each shared binary marginal separately; this simultaneously places both endpoint separator algebras and the chord sign, with literal finite-group transports.
  coherent-balanced-context-permutations-would-give-a-ce-trace: that rules out one globally coherent placement for every edge of the no-CE BCS; this proves that any single balanced chord is locally coherent before the earlier tree placements are frozen.
---

For `i=0,1`, let `A_i` be a finite-dimensional abelian algebra on a
`D`-dimensional coordinate packet, with minimal atom projections
`e_(i,s)`, and let `X_i` be a diagonal self-adjoint involution commuting with
`A_i`.  Write

```text
r_(i,s)^epsilon=rank(e_(i,s)(1+epsilon X_i)/2).         (FRP1)
```

Assume only the balanced global sign ranks

```text
sum_s r_(0,s)^epsilon=sum_t r_(1,t)^epsilon
                                              (epsilon=+,-). (FRP2)
```

Then the two pairs `(A_i,X_i)` admit coordinate embeddings into one copy of
`M_D(C)` such that

```text
[A_0,A_1]=0,              X_0=X_1=:Z.                  (FRP3)
```

The construction is integral and uses no amplification.  For each sign
`epsilon`, choose a nonnegative integer transportation matrix
`n_(s,t)^epsilon` with row sums `r_(0,s)^epsilon` and column sums
`r_(1,t)^epsilon`.  The common coordinate packet is

```text
Omega={(s,t,epsilon,k):1<=k<=n_(s,t)^epsilon}.          (FRP4)
```

Let `A_0` read `s`, let `A_1` read `t`, and let `Z` read `epsilon`.  The
smallest common relative-commutant decomposition produced this way has joint
cell capacities

```text
n_(s,t)=n_(s,t)^+ + n_(s,t)^-.                         (FRP5)
```

All identifications are coordinate permutations.  Hence in the tautological
irreducible block of the finite hyperoctahedral group

```text
K_D=(C_2)^D semidirect S_D
```

the separator projections, `Z`, and the two endpoint transports are exact
finite-group-corner data; the transports are literal elements of `S_D`.

Thus neither rational conditional multiplicities nor one isolated chord is
the obstruction to the signed-Hecke compiler.  The first genuine cycle
equation appears only after the join-tree placements are frozen.  If the
transported endpoint separators already commute with fixed joint capacities
`c_(s,t)`, closure requires transportation matrices as above satisfying

```text
n_(s,t)^+ + n_(s,t)^- = c_(s,t)                         (FRP6)
```

(and the analogous Wedderburn integer equations in the noncommuting case).
Free placement chooses the left side to define the capacities; cycle
holonomy removes precisely that freedom.

