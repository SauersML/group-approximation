---
rg: 2
id: finite-normal-signed-bcs-quotient-collapses-to-twisted-factor
kind: claim
title: A unique-trace finite-normal signed BCS quotient has already produced a non-CE twisted group factor
distinct_from:
  character-rigid-signed-bcs-quotient: that asks to construct the signed quotient; this proves that, for the proposed invariant finite-normal type, completing it already solves the existing twisted-factor gate and so is not a weaker groupification step.
  twisted-factor-existence-is-equivalent-to-nonhyperlinearity: that gives the global equivalence; this identifies the exact twisted factor hidden in the proposed signed corner.
---

Suppose the finite-normal invariant-type corner

```text
A=z_rho C*(Gamma) z_rho
```

has unique trace and admits a unital surjection `Phi:A->B`, where `B` has a
non-Connes-embeddable trace `sigma`.  Put `Q=Gamma/K`.  Then, for the
finite-valued Clifford cocycle `omega` from
`finite-normal-type-corner-is-twisted-group-algebra`,

```text
pi_sigma(B)'' ~= M_(dim rho)(C) tensor L_omega(Q).        (FSQ1)
```

Indeed uniqueness gives `sigma Phi=tau_A`, and surjectivity identifies the
two GNS von Neumann algebras.  The Clifford corner decomposition computes
the latter as the right side of `(FSQ1)`.  Matrix amplification preserves
Connes embeddability, so `L_omega(Q)` is non-CE.  The finite central extension
defined by `omega` is therefore a nonhyperlinear group.

Thus the BCS quotient is not an independent compiler in this setting.  Its
successful construction certifies that the corner's already-present twisted
regular factor is non-CE.  This is exactly the existing twisted-factor root
gate in finite-normal-subgroup coordinates.
