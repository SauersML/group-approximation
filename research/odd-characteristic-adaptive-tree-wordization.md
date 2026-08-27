---
rg: 2
id: odd-characteristic-adaptive-tree-wordization
kind: claim
title: The finite adaptive tree admits an odd-characteristic wordization with exact root order
distinct_from:
  finite-adaptive-selected-atom-ring-tree: That constructs the conditional arrow ring over a characteristic-zero splitting base; this must rebuild the finite presentation over odd characteristic and preserve both the finite two-packets and the perfect complex tracial group representation.
  bcs-atom-detects-its-e5-central-root: That is the normalized-HS payload-overlap estimate after an exact odd-order root exists; this is the algebraic base-change and exact-order prerequisite.
  e5-idempotent-root-has-two-pair-extraspecial-cell: That computes the Heisenberg packet over an already given characteristic-p ring; this must connect that packet to the adaptive BCS coefficient presentation.
---

**ESTABLISHED BASE-CHANGE INTERFACE.**  Fix a contradiction depth `N`.
All scalar coefficients occurring in the finite selected-atom tree lie in
`Z[1/D]` for one fixed integer `D` (for the Boolean tree itself one may take
`D=2`; adjoining a fixed finite role packet only enlarges `D` by finitely
many packet orders).  Choose an odd prime `p` not dividing `D`, and base
change the finite coefficient presentation to a finite extension `k/F_p`
splitting the fixed packet tables.  Then rank-five context absorption gives
a finite ordinary-group wordization in which:

1. the BCS context packets, central sign, and Pauli seed remain injected with
   their stated finite relations;
2. the conditional idempotents and Murray--von Neumann arrow equations of
   `finite-adaptive-selected-atom-ring-tree` are imposed over a coefficient
   ring of characteristic `p`;
3. every named source coefficient `a_(sigma,i)` which is used by the finite
   menu is nonzero in the corresponding universal coefficient ring, so

   ```text
   Z_(sigma,i)=x_13(a_(sigma,i))
   ```

   has exact order `p`; and
4. the original perfect tracial BCS representation extends to the ordinary
   group presentation with all forbidden source roots trivial and the marked
   central involution nontrivial.

The exact-order calculation in clause 3 is elementary once nonvanishing and
the characteristic are in place.  Additivity gives `x_13(a)^p=1`, while the
map to `E_5(R)` sends the word to `1+aE_13`, proving it is nonidentity.
Nonvanishing of any one fixed source has an algebraic infinite-module model:
choose scalar structural BCS signs matching its context assignment, retain
an infinite Pauli seed space, and realize the finitely many conditional
arrows by partial bijections between countably infinite coordinate pieces.
All four clauses hold.

The reason reduction does not collapse a named source is that the defining
relations and a witness can be chosen integrally.  For any fixed
`a_(sigma,i)`, take a countably generated `k`-space, represent the Pauli
seed by the usual `0,1,-1` two-by-two matrices, and choose scalar BCS signs
matching the assignment `i` in its context.  Partition the remaining countable
basis into the finitely many infinite coordinate pieces needed by the depth
`N` tree.  Every nonzero source and its prescribed orthogonal range are
countably infinite, so `s` and `sbar` are the `0,1` partial-bijection matrices
between them; zero sources and ranges use the zero matrix.  Recursing down
the finite tree realizes `(FAR1)--(FAR2)`, and the chosen source acts as a
nonzero coordinate projection.  This model is defined over every `k` of odd
characteristic and proves that the corresponding universal coefficient is
nonzero after reduction.

The finite context packets remain injective by taking the direct product of
this source witness with the finitely many analogous regular packet
witnesses.  Direct products preserve every polynomial relation and separate
all elements in the finite packet menu.  Context absorption and the spare
index proof are integral word identities, so the rank-five presentation is
still finite after base change.

Finally, the perfect marked model survives at the ordinary-group level.
Every forbidden source coefficient is zero there; send its arrow/range
roots to the identity, keep all child carriers equal to the seed as in
`finite-adaptive-selected-atom-ring-tree`, and use the original external
BCS/Pauli representation.  The remaining Steinberg root presentation has
the trivial unitary representation, so the characteristic of its
coefficient syntax creates no homomorphism from `k` into the complex tracial
algebra and requires none.  All mixed root relators become identities while
the external marked involution remains nontrivial.

This base-change statement is necessary because the existing adaptive-ring claim explicitly
chooses a characteristic-zero splitting ring.  In characteristic zero a
nonzero additive root is generally infinite order, so

```text
P_(Z,1)=p^(-1)sum_(k=0)^(p-1) Z^k
```

is not its `1`-eigenspace projection.  The order-`p` Fourier cut and the E5
extraspecial cell used by `bcs-atom-detects-its-e5-central-root` therefore
cannot be imported silently from the current statement.

This base change does not solve the metric decoder.  The
coprime canonical-trace theorem handles literal Reynolds/prefix sources, but
arbitrary adaptive physical carriers would still require payload-to-root
reflection.

DERIVATION
odd-characteristic-adaptive-tree-base-change-proof
