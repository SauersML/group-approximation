# The atlas H-alignment gate is Reynolds norm saturation

Date: 2026-08-13

## 1. Canonical formulation

Let `G=A8`, let `H=diag(GL_3(F_2),1)`, and let `rho` be a regular
multiple of `G` in a finite matrix algebra with normalized
Hilbert--Schmidt norm.  After absorbing the fixed classical alignment, write
the second chart as

```text
g |-> U rho(g) U*.                                    (RNG1)
```

The finite Reynolds operator

```text
E_H(T)=|H|^(-1) sum_(h in H) rho(h) T rho(h)^*         (RNG2)
```

is the Hilbert--Schmidt orthogonal projection onto `rho(H)'`.  Therefore

```text
||U-E_H(U)||_2^2 = 1-||E_H(U)||_2^2.                  (RNG3)
```

Equivalently, averaging the commutator energy gives

```text
|H|^(-1) sum_(h in H) ||U rho(h)-rho(h)U||_2^2
  = 2(1-||E_H(U)||_2^2).                              (RNG4)
```

Thus finite-coordinate `H`-alignment is exactly the assertion that the
contractive commutant coefficient `E_H(U)` asymptotically saturates its
Hilbert--Schmidt norm.  This formulation chooses no tensor decomposition or
regular basis.

The abstract Pythagorean identity behind `(RNG3)` is formalized in
`GroupApproximation/PropertyT/FiniteGroupAverage.lean` as
`norm_sub_orbitAverage_sq`.

## 2. Gauge invariance

The relative implementer is not unique.  If `C,D` commute with the regular
`G`-representation, then `U` and `DUC` determine the same two-chart data up
to the harmless simultaneous commutant gauges.  Since `C,D` also commute
with `rho(H)`, `(RNG2)` gives

```text
E_H(DUC)=D E_H(U) C.                                  (RNG5)
```

Consequently the singular values, Hilbert--Schmidt norm, kernel dimension,
and range dimension of `E_H(U)` are intrinsic finite-multiplicity data.
This is the smallest gauge-free coefficient of the relative chart
implementer.

## 3. What the Weyl bridge forces

Put

```text
Delta_H=max_(h in H)||U rho(h)-rho(h)U||_2.            (RNG6)
```

The explicit bridge/interior estimate gives

```text
sqrt(2) <= epsilon_int+16D(epsilon_br+9Delta_H),
D<=20159.                                              (RNG7)
```

Hence, whenever the numerator below is positive,

```text
Delta_H >=
  (sqrt(2)-epsilon_int-16D epsilon_br)/(144D).         (RNG8)
```

At least one of the `168` summands in `(RNG4)` is `Delta_H^2`, so

```text
1-||E_H(U)||_2^2 >= Delta_H^2/(2|H|)
                         = Delta_H^2/336.              (RNG9)
```

In particular, a hypothetical zero-defect hyperlinear atlas sequence must
keep the canonical coefficient `E_H(U)` a fixed distance below norm
saturation.  This is a positive, gauge-invariant reformulation of the
remaining obstruction: the microstate cannot approach the classical
commutant branch.

## 4. Why this is not yet the missing theorem

The expectation `(RNG2)` is not multiplicative.  For arbitrary `X,Y`, the
product `E_H(X)E_H(Y)` discards cross terms between nontrivial conjugation
types and need not equal `E_H(XY)`.  Thus applying `E_H` to the raw
compressor relations does not automatically produce the three coefficient
products

```text
T_0S_0=1,       T_1S_1=1,       T_0S_1=0.             (RNG10)
```

The exact finite Pauli model in
`ATLAS_RELATIVE_PERFECTNESS_AND_COEFFICIENT_ENDPOINT.md` realizes the
commutator table while retaining precisely these missing cross terms.  Any
proof of `(RNG10)` must therefore use an additional raw-compressor relation
which resolves the proper dual-extension fibers; Reynolds averaging alone
cannot do it.

The live endpoint now has two sufficient formulations:

1. prove that the full finite-coordinate atlas relations force
   `||E_H(U)||_2 -> 1`, contradicting `(RNG9)`; or
2. refine `E_H(U)` into invariant multiplicity arrows satisfying `(RNG10)`,
   then apply the already formalized `2-sqrt(3)` contraction gap.

Both formulations retain the finite multiplicity trace and therefore do not
apply inside the infinite-multiplicity regular representation of the exact
Leavitt group.
