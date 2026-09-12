---
rg: 2
id: core-type-blocks-classify-relative-hole-majorants
kind: claim
title: Core-type blocks classify the relative hole majorants
distinct_from:
  arbitrary-core-near-top-coverage-controls-relative-corner: that gives the abstract module coverage SDP and filler estimate; this decomposes that SDP into core isotypic blocks and solves the irreducible and right-invariant cases.
  hecke-stabilizer-averaging-leaves-indefinite-sector: that identifies exact left-right symmetries and a formal bimodule firewall for the regular core; this identifies what the actual core-type multiplicities do to the positive hole dual.
  bs14-unitary-representations-are-periodic-cycle-packets: that classifies exact BS(1,4) representations by packets; this translates those packets into the blocks and trace weights of the relative selector.
---

Let `beta:B->U(H_beta)` be a finite-dimensional core representation.
Choose its isotypic decomposition

```text
H_beta=direct_sum_(alpha in I) H_alpha tensor C^(m_alpha),
beta=direct_sum_alpha pi_alpha tensor 1_(m_alpha),
d_alpha=dim H_alpha,       d=sum_alpha d_alpha m_alpha. (CTB1)
```

Then

```text
D_beta=beta(B)'
 =direct_sum_alpha 1_(d_alpha) tensor M_(m_alpha),

tr_d(Z)=d^(-1) sum_alpha d_alpha Tr(Z_alpha).           (CTB2)
```

Let `E_beta=Hom_B(H_beta,Ind_B^G beta)`, let
`L_epsilon=Q_epsilon E_beta` be the near-top module, and let
`c_(epsilon,beta)` be its optimal coverage.

## Irreducible core

If `beta` is irreducible, then `D_beta=C`. Consequently

```text
c_(epsilon,beta)=0       if L_epsilon={0},
c_(epsilon,beta)=1       if L_epsilon!={0}.             (CTB3)
```

Hence a single nonzero vector in the `[1-epsilon,1]` band gives

```text
Delta_(G,B,beta)(X)<=sqrt(2 epsilon).                   (CTB4)
```

Equivalently, if `Delta>=eta` and `epsilon<=eta^2/4`, then

```text
L_epsilon={0},       lambda_max(T_X)<1-epsilon.         (CTB5)
```

So an irreducible-core counterexample must have a genuine uniform top
spectral gap; a small-trace right-majorant cannot coexist with even one
near-top intertwiner.

## Multiplicity-free core

If every `m_alpha=1`, put

```text
w_alpha=d_alpha/d,
A_alpha=Q_epsilon R_(e_alpha) Q_epsilon on L_epsilon,  (CTB6)
```

where `e_alpha` is the central type projection. The `A_alpha` form a
positive operator-valued partition of unity. The hole dual becomes the
exact weighted covering problem

```text
c_(epsilon,beta)
 =min {sum_alpha w_alpha z_alpha:
       z_alpha>=0, sum_alpha z_alpha A_alpha>=1}.       (CTB7)
```

Thus multiplicity-free does not by itself force coverage: compression by
the sharp band can turn the orthogonal type projections into overlapping,
noncommuting effects. If the effects commute, (CTB7) is an ordinary finite
linear program after simultaneous diagonalization.

If `L_epsilon` is invariant under the full right action of `D_beta`, then
the effects in (CTB6) are orthogonal projections and

```text
c_(epsilon,beta)
 =sum_(alpha:L_epsilon e_alpha !=0) w_alpha.            (CTB8)
```

More generally, with arbitrary multiplicities and full right
`D_beta`-invariance, the same formula holds with block weights

```text
w_alpha=d_alpha m_alpha/d.                             (CTB9)
```

In that case coverage tends to one exactly when the active isotypic blocks
carry trace weight tending to one.

## The actual BS(1,4) cores

For the authenticated Dogon--Vigdorovich core, the irreducible types are
the fourth-power orbit packets

```text
alpha=(O,v),       d_alpha=|O|,                        (CTB10)
```

where `v` is the scalar return phase, and `m_(O,v)` counts repeated
identical packets. Therefore

```text
D_beta=direct_sum_(O,v) M_(m_(O,v)).                   (CTB11)
```

A single scalar packet is in the solved irreducible regime (CTB3)--(CTB5).
A packet sum with no repetitions is exactly the POVM regime (CTB7).
Noncommutative core blocks arise only from repeated copies of the same
`(O,v)` packet.

For the literal regular finite core `beta=lambda_(B_N)`,

```text
m_alpha=d_alpha,
w_alpha=d_alpha^2/|B_N|.                               (CTB12)
```

Thus the right-invariant specialization of the finite-corner gate is
Plancherel coverage: the active packet types must carry
`1-o(1)` of the Plancherel mass. A merely regular limiting character does
not force multiplicity-freeness or bound the matrix-block sizes, so the
full Dogon--Vigdorovich problem cannot be reduced to (CTB3). It must control
the packet-weighted effects (CTB7), or their matrix-block analogue, under
the actual two cubic residuals.

This locates the remaining arithmetic content without another ambient
operator-algebra hypothesis. The nonhyperlinear-group root remains open.

DERIVATION
core-type-block-hole-majorant-proof
