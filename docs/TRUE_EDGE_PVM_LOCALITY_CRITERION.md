# Edgewise map-outcome PVMs are enough

Date: 2026-08-13

## 1. Exact sufficient criterion

Let

```text
A0=A1=Map(V,V),   B0=B1=Map(W,W).
```

Suppose a finite tracial algebra contains four projection-valued measures

```text
P0 : A0 -> Proj(M),   P1 : A1 -> Proj(M),
Q0 : B0 -> Proj(M),   Q1 : B1 -> Proj(M),             (EPL1)
```

whose projections are pairwise orthogonal inside each family and sum to one.
Assume only the three edgewise commutation relations

```text
[P0(a),Q0(b)]=0,
[P0(a),Q1(b)]=0,
[P1(a),Q1(b)]=0.                                     (EPL2)
```

No commutation between `P0` and `P1`, between `Q0` and `Q1`, or on the
unused edge `(P1,Q0)` is required.

Define

```text
mu00(a,b)=tau(P0(a)Q0(b)),
mu01(a,b)=tau(P0(a)Q1(b)),
mu11(a,b)=tau(P1(a)Q1(b)).                            (EPL3)
```

Commutation makes the products in `(EPL3)` positive.  Each `muij` is a
probability law.  Moreover

```text
sum_b mu00(a,b)=tau(P0(a))=sum_b mu01(a,b),
sum_a mu01(a,b)=tau(Q1(b))=sum_a mu11(a,b).           (EPL4)
```

Thus the shared `R0` and `L1` marginals agree automatically.  The explicit
`FiniteTreeCoupling.glueTransportPath` construction produces one law on
`(R0,R1,L0,L1)` preserving all three edge laws; its three marginal identities
are now written separately in Lean.  If the trace expectations of the three
pairing-error functions are small, `robust_floor_of_common_latent_maps` gives
the fixed contradiction.

This criterion is exact and uses only the path-shaped commutation graph.

## 2. Why outcomes must be whole maps

A PVM indexed merely by one target label for each source setting gives a
Bell-type family of measurements.  Different source settings need not be
jointly measurable, so their edge correlations need not be mixtures of
deterministic response functions.  To index `(EPL1)` by `Map(V,V)`, all
source responses for one transport must already have been assembled into one
classical measurement.

Equivalently, if `E_v` and `F_x` are the source and target atomic label
projections and `U` is a transport unitary, one must recover a common atomic
algebra on which `Ad(U)` is approximately a classical channel that admits a
whole-map dilation.  A squared block-mass matrix

```text
tau(F_x U E_v U* F_x)                                 (EPL5)
```

provides only the one-setting marginals.  Birkhoff decomposition of `(EPL5)`
is an external distribution on maps, but unrelated decompositions on two
edges do not reproduce the observed two-transport correlations.

## 3. Quantitative version

For matrix coordinates it is enough to construct approximate versions of
`(EPL1)--(EPL2)` with total normalized-Hilbert--Schmidt error tending to zero:

```text
sum_a ||P_i(a)^2-P_i(a)||_2^2,
sum_(a!=a') ||P_i(a)P_i(a')||_2^2,
||sum_a P_i(a)-1||_2^2,
sum_(a,b) ||[P_i(a),Q_j(b)]||_2^2 -> 0.               (EPL6)
```

The sums, rather than pointwise maxima, are the correct scale when the label
spaces grow.  After discarding an `o(1)` trace part, a simultaneous PVM
rounding theorem would turn `(EPL6)` into the exact criterion above.  Such a
rounding theorem is standard for a fixed number of projections but is not
automatic when the number of map outcomes grows with the microstate.

## 4. Application to the atlas packet

The raw-compressor/adjacent-root relations already supply:

* finite Pauli label PVMs inside each chart;
* exact edgewise Steinberg commutator signs;
* positive-density coefficient cuts;
* a fixed robust error floor after classicalization.

They do **not** yet supply the whole-map PVMs `(EPL1)`.  The order-32 regular
Pauli model is the local counterexample: it realizes all commutator signs but
keeps the response data in a nonclassical symplectic factor rather than a
map-outcome algebra.

The narrow live theorem is therefore:

> Use the raw compressor and the two Kazhdan chart restrictions to recover
> edgewise commuting whole-map PVMs satisfying `(EPL6)` for the paired
> radical quotient.

This is weaker than simultaneous recovery of both full coefficient
commutants.  It asks only for three edge contexts and no unused-edge
commutation.  It is stronger than four bistochastic block-mass matrices, and
the distinction is forced by the exact Pauli countermodel.
