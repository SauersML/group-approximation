# The minimal mixed selector transvection has a positive guarded Pauli model

## Candidate relation

The smallest non-split relation coupling a selector permutation to a guarded
machine multiplicity is the controlled sign transvection

```text
S^2=Z^2=K^2=1,
[S,K]=[Z,K]=1,
S Z S^(-1)=K Z.                                        (MST1)
```

Here `K=[R_F,R_G]` is the D8 holonomy sign,

```text
H=(1-K)/2,                                              (MST2)
```

`Z` is the selected guarded C18 machine involution, and `S` is the selector
flip acting on the same multiplicity coordinate.  Unlike covariance on the
logical fixed algebra, `(MST1)` is genuinely mixed and phase-sensitive.

## Exact finite countermodel

Fix `m>=1` and take

```text
V_- = C^2 tensor C^m,       dim(V_-)=2m,
V_+ = C^(14m),              V=V_- direct_sum V_+.
```

On `V_-` put

```text
K=-I,       Z=sigma_z tensor I_m,       S=sigma_x tensor I_m.
```

On `V_+` put

```text
K=I,        Z=I,                       S=I.
```

Then every relation in `(MST1)` holds exactly and

```text
tr_V(H)=dim(V_-)/dim(V)=1/8.                            (MST3)
```

Thus the desired canonical D8 holonomy density survives with zero relation
defect.

More generally, on the `K=-1` sector `(MST1)` is exactly

```text
S Z S^(-1)=-Z.                                         (MST4)
```

It forces the `Z=+1` and `Z=-1` multiplicities inside `H` to be equal, but
places no upper bound on their common size.  Every positive guarded
multiplicity is allowed after a two-dimensional Pauli amplification.

## Consequence for trace-cyclic return

A unitary conjugacy is rank-preserving.  Therefore the controlled selector
transvection can at most balance guarded fibers; it cannot provide the
unequal-rank source/target maps required by `(STR1)` or `(STR1')`.  In the
explicit model the relation energy is zero while `tr(H)=1/8`, so no estimate

```text
tr(H) <= C defect_(MST1)                                (MST5)
```

is possible.

Tensoring `(MST3)` with any independent finite packet or exact machine-word
model preserves the calculation.  Identifying `Z` with a particular native
C18 word requires its guarded spectrum to contain this balanced Pauli
sector; the theorem does not assert that every full native model has such a
sector.  It proves that the mixed relation itself cannot exclude it.

## Sharp remaining shape

Adding more conjugacy rows of the same controlled-Clifford type only builds
a finite Clifford module on `H`; spectator amplification again leaves
`tr(H)` arbitrary.  A successful mixed cell must be non-automorphic on the
guarded carrier: after packet compression it must compare unequal source
and target ranks, or implement a genuinely one-sided map whose finite
matrix cyclic trace exposes the deficit while infinite multiplicity absorbs
it.  In particular the missing cell cannot be only a selector-controlled
sign flip, transvection, or finite Clifford covariance table.

This is compatible with exact HALT completeness: it does not forbid a
one-sided Toeplitz/Hilbert-hotel relation.  It only eliminates the smallest
unitary mixed-relation ansatz.
