---
rg: 2
id: regular-finite-controlled-phase-has-half-wrong-mass
kind: claim
title: Regular finite normalization gives a nonaffine controlled phase exactly one-half wrong mass
distinct_from:
  controlled-central-phase-finite-group-barrier: that uses irreducible induction to show a universally sound finite central phase must be affine; this computes the exact Plancherel mass of the wrong phase in the regular representation and does not require centrality in the whole group.
  finite-selector-gadget-induction-barrier: that guarantees occurrence of every compatible selector character somewhere; this rules out suppressing the bad characters by making their irreducibles small.
  leavitt-regular-atlas-hyperlinearity-criterion: that normalizes fixed finite atlas factors to regular type; this gives the selector-phase distribution forced by regular normalization in any finite packet overgroup.
---

Let `H` be finite.  Let `D=<z_1,...,z_k>` be a Boolean subgroup and let `c`
be an involution commuting with `D`, so `C=<D,c>` is abelian.  In the left
regular representation of `H`, restriction to `C` is `[H:C]` copies of the
left regular representation of `C`.  Consequently:

1. if `c in D`, its value is one affine character of the selector bits;
2. if `c notin D`, then for every selector character `x in D^`, the two joint
   characters extending `x` and sending `c` to `+1` and `-1` have equal
   Hilbert mass.

Thus for every Boolean predicate `f`, if `c notin D`, the regular
representation has

```text
Pr[c != (-1)^(f(x)) | selector character x] = 1/2              (RCP1)
```

for every `x`, and total wrong-phase mass exactly `1/2`.  If `c in D`, the
phase law is affine.  There is no intermediate regime in which a nonlinear
controlled phase is correct on most of a regular finite packet.

This blocks a possible repair of the Schur--Clifford groupification problem:
adjoining the controlled Fourier phase to a finite overgroup and hoping that
the spurious irreducibles have negligible Plancherel weight cannot work.
Hyperlinear regular-character normalization exposes those sectors with
one-half mass.  Any successful compiler must avoid a finite regular packet
law for the controlled phase and obtain its selection from an infinite or
state-dependent mechanism.

