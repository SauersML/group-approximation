---
rg: 2
id: common-source-hnn-bridges-need-one-gram-saturation-identity
kind: claim
title: Four context HNN bridges share the leakage source exactly when one source-Gram saturation identity holds
distinct_from:
  capacity-gated-common-corner-bcs-two-cell: that proves full localized BCS quietness from context intertwiners already having one common source; this audits whether ordinary context HNN bridges can supply that common-source hypothesis.
  two-sided-pauli-gauge-bridge-preserves-spin-scale: that equalizes private gauge multiplicities conditional on one logical overlap; this shows that equal restriction multiplicities do not identify the selected source Gram projection across all contexts.
  finite-selector-gadget-induction-barrier: that says every selector character occurs in some representation of a finite overgroup; this identifies the precise unwanted summands left inside a central-sign source and the higher-dimensional Hecke identity needed to remove them.
---

Let the four native Fanizza contexts be indexed by `c`.  After fixed packet
exactification, let `p_c` be the selected **allowed** Hecke projection in the
target packet for context `c`, let `U_c` be the unitary implementing its HNN
bridge, and let

```text
Q=(1-C)E                                                  (CSG1)
```

be one analytic off-capacity leakage projection.  Put

```text
V_c=p_cU_cQ.                                             (CSG2)
```

Then `V_c^*V_c<=Q`, and the following identity is exact:

```text
tau(Q)-tau(V_c^*V_c)=||(1-p_c)U_cQ||_2^2.               (CSG3)
```

Consequently the four bridges have the same full source `Q`, up to polar
rounding on a vanishing subspace, if and only if they satisfy the one scalar
source-Gram saturation estimate

```text
sum_c||(1-p_c)U_cQ||_2^2
 =sum_c[tau(Q)-tau(Q U_c^*p_cU_c Q)]
 <=K E_rel+o(1).                                        (CSG4)
```

Once `(CSG4)` holds, let `Q_c` be the spectral projection of `V_c^*V_c` for
`[1/2,1]`.  Markov's inequality gives

```text
tau(Q-Q_c)<=2[tau(Q)-tau(V_c^*V_c)].                   (CSG4a)
```

The projection onto the intersection of the four ranges has codimension at
most the sum of their codimensions.  Hence

```text
Q'=meet_c Q_c<=Q,
tau(Q-Q')<=2 sum_c[tau(Q)-tau(V_c^*V_c)].              (CSG4b)
```

Polar-rounding each `V_cQ'` now gives partial isometries with the literal
common source `Q'`, losing at most a fixed multiple of the left side of
`(CSG4)`.  The context covariance relations then feed directly into
`capacity-gated-common-corner-bcs-two-cell`.  Thus `(CSG4)`, plus the already
named context covariance defects, is the exact algebraic source-Gram identity
needed for `(NCL13)`.

## Why four ordinary HNN edges do not force `(CSG4)`

An HNN edge identifies representations of its edge subgroup.  It does not
select one irreducible summand of the adjacent vertex group.  In finite-group
language, if `sigma_c` is the source edge type and `pi_c` is the desired
allowed target type, then

```text
Ind_(H_c)^(G_c)(sigma_c)
 =m_c pi_c + sum_(rho!=pi_c)m_(c,rho)rho.               (CSG5)
```

The stable letter transports the entire `sigma_c`-isotypic source.  The
compression by `p_c` keeps only the first term in `(CSG5)`.  Every other term
is an exact source-Gram deficit in `(CSG3)`.  A central sign or a finite
selector tag cannot remove those terms: by Frobenius reciprocity and the
finite-selector induction barrier, every compatible selector character
occurs in some induced target representation.

One can sometimes make `Ind(sigma_c)` irreducible by using a full point
stabilizer rather than the selector subgroup.  This explains why the
hyperoctahedral tautological predicate packet is useful locally.  It does not
solve the global problem.  Its stabilizer `H_c` and Hecke idempotent depend on
the context predicate, so the four source isotypic projections are

```text
Q_c=e_(sigma_c)(rho(H_c)),                              (CSG6)
```

not one common `Q`.  A graph of finite groups can rotate their multiplicity
spaces independently and has the positive regular stationary model already
recorded in `finite-packet-graph-atlases-have-a-regular-stationary-flow`.

There are only two apparent ways to identify the four projections in
`(CSG6)`:

1. **Use only one central sign/tag.**  Then all four edges have a common
   source, but `(CSG5)` contains the unwanted induced summands and
   `V_c^*V_c<Q` on the regular stationary model.
2. **Put every shared logical variable in one common finite edge group.**
   Then the common selected type would have to restrict to an allowed joint
   spectrum in every context.  Its finite-dimensional representation is
   already a perfect finite-dimensional representation of the non-CE BCS,
   which does not exist.  Assuming such a type simply inserts the desired
   matrix-only conclusion into the finite edge data.

Thus selector-edge twisting does not manufacture `(CSG4)`.  The missing
datum is a two-cell acting on the edge-intertwiner multiplicity spaces and
forcing their selected Hecke compressions to have one common source Gram
projection.

## Countable-amplification completeness audit

There is no corresponding obstruction on the exact witness side.  Let `pi`
be a perfect non-CE tracial representation of the BCS.  Gauge doubling and
finite orbit covariantization make every required private gauge character
available without changing the retained logical words.  After one common
countable amplification, every nonzero allowed context packet type has
infinite multiplicity.  For each context independently choose a unitary
`U_c` from the same source Hilbert space `QH` onto the selected allowed target
packet carrier.  Then

```text
p_cU_cQ=U_cQ,
V_c^*V_c=Q                                               (CSG7)
```

for all four contexts, and the shared logical covariance holds because all
source actions are restrictions of the same `pi(Z_x)`.  The `U_c` need not
agree with one another; only their initial projection agrees.

For the Fanizza HALT packet extension, every forbidden source and hence the
off-capacity `Q` may be zero, so `(CSG7)` is vacuous.  Properly infinite
multiplicity remains available for any auxiliary return cell.  Therefore
`(CSG4)` is compatible with exact HALT completeness and does not impose a
tracial extension of the groupifier.

The regular representation gives the opposite audit.  Its finite packet
restriction contains every summand in `(CSG5)` with positive Plancherel
weight, so the left side of `(CSG4)` can be positive at zero group-relator
defect.  Hence `(CSG4)` cannot be a universal cyclic-trace or finite-level
NPA consequence.  It must be a matrix-ultraproduct statement consuming the
shared non-CE tuple.  This is the permitted asymmetry, not a contradiction.

## Reduced construction target

The whole source-specific transport gate can now be stated with two finite
rows:

```text
source-Gram row:
  sum_c||(1-p_c)U_c(1-C)E||_2^2 <=K E_rel+o(1),

context-covariance row:
  sum_(c,x)||A_(c,x)p_cU_c(1-C)E
                 -p_cU_c(1-C)E Z_x||_2^2
  +sum_(c,R)||R(A_c)p_cU_c(1-C)E||_2^2
  <=K E_rel+o(1).                                      (CSG8)
```

The second row is fixed-word telescoping once the packet blocks are supplied.
The first row is load-bearing.  It says exactly that all four context packets
accept the same off-capacity multiplicity carrier.  No current finite
restriction graph, gauge bridge, or selector reset proves it.
