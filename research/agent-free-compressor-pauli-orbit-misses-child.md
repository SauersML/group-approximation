---
rg: 2
id: agent-free-compressor-pauli-orbit-misses-child
kind: claim
title: A full-support Pauli character orbit misses the child annihilator
distinct_from:
  predicate-rank-jump-forces-adjoint-reynolds-gap: That gives an aggregate commutant-rank gap in honest packet modules; this gives an exact Fourier-character orbit on the additive packet block which sees no child-annihilator label.
  steinberg-root-shear-plancherel-covariance: That obtains uniform Plancherel multiplicities when the canonical trace is known on an injected finite root group; this treats an arbitrary multiplicity measure seeded only by one nontrivial payload root.
  agent-free-compressor-named-row-retains-complement-gauge: That puts an independent group gauge on the complement of a coefficient idempotent; this is the dual additive-character form of the obstruction inside the selected simple block itself.
---

On a forbidden Schur--Clifford simple block write

```text
S=P k[B_f]=M_D(k) tensor M_2(k),
S_A=P k[A_f]=M_D(k) tensor k I_2,                       (PCO1)
```

where `k` is a finite splitting field of odd characteristic and the relative
Pauli factor is spanned by `I,X,Y,Z`.  Identify the additive dual of `S` by

```text
chi_M(s)=psi(Tr(Ms))                                   (PCO2)
```

for one nontrivial additive character `psi` of `k`.

There is a `B_f`-orbit `O` in this dual such that

```text
chi(P)!=1                    for chi in at least one point of O,
O intersection S_A^perp = empty.                       (PCO3)
```

Indeed take

```text
M=I_D tensor (I+X+Y+Z).                                (PCO4)
```

Under either left or right multiplication by the relative Pauli group, the
four nonzero Pauli coefficients of `M` are permuted up to signs.  Hence the
identity coefficient is nonzero at every point of the full `B_f` orbit, so
no orbit character vanishes on all of `S_A`.  Since `D` is a power of two and
the characteristic is odd, `Tr(MP)=2D` is nonzero; choose `psi` so that the
corresponding value is not `1`.

Putting equal multiplicity on `O` gives an exact `B_f`-invariant character
PVM for the complete additive root window `x_12(S)` with positive nontrivial
`x_12(P)` mass but zero mass in `S_A^perp`.  Therefore no constant `c>0` can
make

```text
mass(S_A^perp minus {0})
  >= c * mass(nontrivial x_12(P) characters)            (PCO5)
```

follow from `B_f`-invariance of character multiplicities.

For the conjugation action used by adjoint Reynolds averages there is an
even smaller stationary alias: `M=I` is fixed by both `A_f` and `B_f`, detects
`P`, and does not lie in `S_A^perp`.

Thus exactifying the finite additive root window and comparing only packet
character orbits cannot pay the BCL root.  The HNN letter would have to impose
additional coefficient-specific multiplication compatibility across root
windows; the packet Reynolds gap and `B_f`-invariance alone do not supply it.
