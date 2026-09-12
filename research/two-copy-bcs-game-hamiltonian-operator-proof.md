---
rg: 2
id: two-copy-bcs-game-hamiltonian-operator-proof
kind: route
title: Vector-state separation proves the two-copy Fanizza Hamiltonian inequality
target: two-copy-bcs-game-hamiltonian-dominates-fanizza-signal
requires:
  - fanizza-turing-bcs-signal-collapse
---

Fix `m` and abbreviate the two-copy group in `(TCH1)` by `Lambda`.
Let `pi:Lambda->U(H)` be any representation and let `xi` be any unit
vector.  The images of the two direct factors commute.  In a left context
`c`, its variable involutions commute, so their joint spectral projections
`P_(c,a)^L` form a PVM indexed by Boolean assignments `a`.  Use this PVM as
Alice's measurement and use the two spectral projections of `X_x^R` as
Bob's measurement on question `x`.  This is a commuting-operator strategy.

For fixed `(c,x)`, the forbidden projections `P_(c,a)^L`, and the projections

```text
P_(c,a)^L (1-a_x X_x^R)/2
```

over allowed `a`, are pairwise orthogonal.  Their sum is therefore the losing
projection `L_(c,x)` in `(TCH2)`.  It follows directly from the constraint--
variable game predicate that this strategy's losing probability is

```text
epsilon_xi = <xi,pi(H_m)xi>.
```

The associated Bob state evaluates the distinguished BCS projection as

```text
phi_xi(D) = <xi,pi((1-X_D^R)/2)xi>
          = <xi,pi(D_R)xi>.
```

For `m` outside the recursively enumerable language,
`fanizza-turing-bcs-signal-collapse` applies to this arbitrary commuting
strategy and gives

```text
<xi,pi(D_R)xi> <= C_m <xi,pi(H_m)xi>.
```

Because this holds for every unit vector `xi`, the quadratic-form criterion
for positivity gives the operator inequality

```text
pi(D_R) <= C_m pi(H_m).
```

The construction also proves the advertised HALT side.  Let `(M,tau)` be the
GNS finite von Neumann algebra of the perfect tracial BCS state supplied by
the completeness half of `fanizza-turing-bcs-signal-collapse`.  Represent
the left copy on `L^2(M,tau)` by left multiplication and the right copy by
right multiplication by the inverse.  These are commuting representations;
on the trace vector `1`, every losing projection vanishes, while

```text
<1,D_R 1> = tau(D) > 0.
```

Finally, each joint spectral projection is the explicit product
`prod_(x in c)(1+a_x X_x^L)/2`.  Hence `H_m,D_R` belong to the rational group
algebra, and a convex combination of the losing projections gives
`0<=H_m<=1`, completing all clauses of the target claim.
