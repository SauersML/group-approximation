---
rg: 2
id: iwahori-fractional-transport-integralization
kind: claim
title: Low-gap Iwahori transport integralizes to orthogonal near-intertwiner blocks
distinct_from:
  mixed-intertwiner-energy-transport-localization: That theorem gives an exact fractional transportation plan and proves that almost all of its mass lies on low mixed-gap pairs; this claim asks for the genuinely noncommutative step from that fractional plan to orthogonal physical summands and near-unitary block intertwiners.
  iwahori-outlier-repair: That is the complete endpoint, including correction to the common modular extension locus; this claim stops before extension-locus transversality and asks only for physical integralization of the low-gap transport.
artifacts:
  - notes/TRUE_IWAHORI_CENTRAL_REGULAR_OUTLIER_LOCALIZATION.md
  - notes/TRUE_IWAHORI_INDEX_THREE_HAS_BOUNDED_BRANCHING.md
---

Work in a fixed matched central sector of the Dogon--Vigdorovich Iwahori
problem.  Let `rho_n,sigma_n` be the two exact edge representations on
`C^(d_n)` with edge defect tending to zero.  Write their `B`-isotypic
projections as `(P_(n,i))` and `(Q_(n,j))`, let `lambda_(n,i,j)` be the bottom
mixed-intertwiner energy on `P_(n,i) M_(d_n) Q_(n,j)`, and put

```text
m_(n,i,j)=||P_(n,i) Q_(n,j)||_2^2.
```

By `mixed-intertwiner-energy-transport-localization`, for some thresholds
`a_n->0` the plan `m_n` has only `o(1)` total mass on pairs with
`lambda_(n,i,j)>a_n`.

Ask for the following **integralization**, after deleting and/or adding
`o(d_n)` physical dimensions.  There should be orthogonal decompositions of
the retained source and target spaces into matched summands

```text
H_n^src = directSum_k V_(n,k),
H_n^tgt = directSum_k W_(n,k),
dim V_(n,k)=dim W_(n,k),
```

and unitaries `U_(n,k):V_(n,k)->W_(n,k)` such that:

- every pair `(V_(n,k),W_(n,k))` lies inside a block pair with
  `lambda_(n,i,j)<=a_n`;
- the direct sum `directSum_k U_(n,k)` differs from the original identity
  identification by `o(1)` in normalized Hilbert--Schmidt norm; and
- the aggregate normalized mixed-intertwining defect of these block
  unitaries tends to zero.

No assertion is made here that the matched edge blocks can be corrected to
an exact common restriction of the two modular vertices.  That is the
separate extension-locus transversality problem.

## Attempts

1. **Threshold the fractional plan and invoke Hall.**  This controls scalar
   dimension flow, but a positive number `||P_iQ_j||_2^2` need not contain a
   partial isometry of comparable rank.  Singular values, not just masses,
   have to be controlled.
2. **Take the polar part of every block `P_iQ_j`.**  The resulting initial
   and final projections for different edges need not be orthogonal, so the
   block polar parts do not assemble to one unitary without another rounding
   argument.
3. **Use index-three bounded branching.**  It limits restriction/induction
   degree to three and prevents multiplicity blowup inside one vertex
   irreducible, but the two vertex decompositions have independent relative
   position.  A cardinality-free operator-valued matching theorem is still
   needed.
