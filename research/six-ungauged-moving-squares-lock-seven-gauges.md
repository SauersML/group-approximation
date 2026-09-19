---
rg: 2
id: six-ungauged-moving-squares-lock-seven-gauges
kind: claim
title: Six ungauged moving squares lock all seven order-seven stage gauges
artifacts:
  - research/six-moving-squares-gauge-lock-proof.md
distinct_from:
  moving-order-seven-stage-gauges-have-coboundary-drift: that gives arbitrary stage coboundaries when only separate charts are typed; this identifies the minimal cross-stage square which measures each coboundary difference.
  fano-moving-packet-retains-actor-holonomy: that reduces the Fano packet to one arbitrary actor holonomy; this assumes independently authenticated coefficient bridges whose reservoir action is the identity.
  growing-multicut-el20-order-seven-inheritance: that asks for the concrete EL20 moving compiler; this is the abstract quantitative endpoint once the six coefficient bridges have been found.
---

**ESTABLISHED SIX-SQUARE GAUGE LOCK.**  Work on seven equal finite
corners `E_k`, `k in Z/7`, with fixed label charts.  Suppose the moving
native transitions `C_k:E_kH->E_(k+1)H` satisfy

```text
||C_k-(M_k tensor D_k)||_2<=eta_k,                    (SGL1)
```

where the `M_k` are label unitaries and the `D_k` are reservoir unitaries.
For `0<=k<=6`, suppose there is a parallel, independently authenticated
coefficient bridge `R_k:E_kH->E_(k+1)H` with

```text
||R_k-(N_k tensor 1)||_2<=zeta_k,                     (SGL2)
```

and, for `0<=k<=5`, a mixed square

```text
||C_(k+1)R_k-R_(k+1)C_k||_2<=epsilon_k,              (SGL3)
```

where the label maps obey

```text
M_(k+1)N_k=N_(k+1)M_k.                               (SGL4)
```

Then, with all corner norms normalized in the same way,

```text
||D_(k+1)-D_k||_2
 <=epsilon_k+eta_(k+1)+eta_k+zeta_(k+1)+zeta_k.       (SGL5)
```

Consequently six such squares lock every `D_k` to `D_0`.  If the moving
seventh-power telescope also gives

```text
||D_6D_5...D_0-1||_2<=rho                              (SGL6)
```

and `D_0^2=1`, then

```text
||D_0-1||_2
 <=rho+sum_(k=1)^6 ||D_k-D_0||_2.                     (SGL7)
```

Thus a dimension-free sum of the six square defects and chart errors kills
the initial native/Hecke involution.  Six is graph-theoretically sharp for
independent local charts: omitting an edge from a spanning tree leaves at
least two components, and a nontrivial involution may be inserted on one
component without changing any remaining square.

The word “ungauged” in `(SGL2)` is load-bearing.  A bridge authenticated only
up to its own reservoir unitary replaces `(SGL5)` by a relation among three
gauges and recreates the coboundary-drift countermodel.

DERIVATION
six-moving-squares-gauge-lock-proof
