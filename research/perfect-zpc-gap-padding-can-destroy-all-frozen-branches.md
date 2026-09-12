---
rg: 2
id: perfect-zpc-gap-padding-can-destroy-all-frozen-branches
kind: claim
title: Harmless finite ZPC padding can destroy every frozen readable branch of a perfect gap witness
distinct_from:
  perfect-zpc-irs-quantum-gap-game: that supplies an existential unpadded gap witness; this proves the gap property is preserved by a padding operation which destroys universal readable freezing.
  zpc-readable-control-freezing-to-lcs: that is now the joint-selection claim for a specially chosen witness; this rules out proving it from the two value inequalities and ZPC axioms alone.
---

**ESTABLISHED PADDING NO-GO.**  There exists a finite tailored game `G'`
such that

```text
omega_ZIRS(G')=1,             omega*(G')<1,              (ZPD1)
```

but every global readable assignment of `G'` has an operator-inconsistent
frozen linear system.

Start with a witness `G` from `perfect-zpc-irs-quantum-gap-game` and adjoin,
with any fixed positive rational sampling weight, the disjoint finite gadget
`H_ms` from `finite-magic-square-selector-has-no-frozen-branch`.  The product
of the perfect ZPC-IRS strategy for `G` and the finite signed Pauli strategy
for `H_ms` is perfect for the padded verifier.  Conversely, restricting any
finite-dimensional strategy to the positive-probability `G` checks gives

```text
omega*(G') <= (1-delta) omega*(G)+delta < 1.             (ZPD2)
```

For every global readable assignment of `G'`, its magic-square selector
coordinate is either zero or one.  The frozen system contains the full base
magic-square rows and the corresponding pin `x_22=1` or `x_22=J`.  By the
finite gadget claim, either choice forces `J=1`.  Therefore no frozen branch
has a negative-central commuting-operator solution, independently of all
coordinates inherited from `G`.

Thus perfect ZPC completeness plus a strict quantum gap does not imply
readable freezing for an arbitrary witness and is not invariant under benign
finite padding.
